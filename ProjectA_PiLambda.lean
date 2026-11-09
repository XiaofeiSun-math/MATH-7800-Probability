/-
  Math 7800 (Fall 2026) -- Take-home Lean midterm, Project A.
  Scaffold release: 2026-10-13. Due: Thursday, 2026-10-29, Gradescope.

  Read Midterm/README.md before starting.
  Replace ALL five `sorry` placeholders with proofs (four lemmas and
  the main theorem). None may remain in a final submission.
  Keep the definitions, namespace, and five statements unchanged.
  Add helper lemmas as needed. General Mathlib set algebra is allowed.
  Do not use MeasurableSpace.DynkinSystem.*, any constant beginning
  MeasurableSpace.generateFrom, or MeasurableSpace.induction_on_inter,
  including through a helper lemma. See README.md for the proof map.
  Check the two projects separately: they share the frozen definitions.
-/
import Mathlib

open Set Function

namespace Math7800.Midterm

variable {Ω : Type*}

-- BEGIN FROZEN DEFINITIONS
/-- π-system: closed under finite intersection. (∅ allowed, as in Mathlib.) -/
def IsPiSys (P : Set (Set Ω)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, A ∩ B ∈ P

/-- λ-system (Billingsley): contains Ω, closed under complements and
countable disjoint unions. -/
structure IsLambdaSys (L : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ L
  compl_mem : ∀ A ∈ L, Aᶜ ∈ L
  iUnion_mem : ∀ f : ℕ → Set Ω, Pairwise (Disjoint on f) → (∀ n, f n ∈ L) →
    (⋃ n, f n) ∈ L

structure IsSigmaField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  iUnion_mem : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ F) → (⋃ n, f n) ∈ F

/-- Field (algebra) of sets. -/
structure IsField (F : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

/-- Monotone class: closed under increasing unions and decreasing
intersections of sequences. -/
structure IsMonotoneClass (M : Set (Set Ω)) : Prop where
  iUnion_mem : ∀ f : ℕ → Set Ω, Monotone f → (∀ n, f n ∈ M) → (⋃ n, f n) ∈ M
  iInter_mem : ∀ f : ℕ → Set Ω, Antitone f → (∀ n, f n ∈ M) → (⋂ n, f n) ∈ M

def sigmaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {F | IsSigmaField F ∧ A ⊆ F}
def lambdaGen (A : Set (Set Ω)) : Set (Set Ω) := ⋂₀ {L | IsLambdaSys L ∧ A ⊆ L}
def monoGen (A : Set (Set Ω)) : Set (Set Ω) :=
  ⋂₀ {M | IsMonotoneClass M ∧ A ⊆ M}
-- END FROZEN DEFINITIONS

/-!Th 3.2（Dynkin π-λ 定理）：P 是 π-系统，L 是 λ-系统，P ⊆ L ⇒ σ(P) ⊆ L。
令 L₀ = λ(P)。

* A1 `lambdaGen_isLambdaSys`：λ(A) 是 λ-系统。
* A2 `subset_lambdaGen`：A ⊆ λ(A)。
* A3 `lambdaGen_inter`：Th 3.2 证明 ②。
  It remains to show L₀ 是 π-系统。L_A = {B | A ∩ B ∈ L₀}，路线 P × P → P × L₀ → L₀ × L₀。
  辅助：
  - 最小性 `lambdaGen_subset`；
  - Remark：λ₁ + λ₂ + λ₃ ⇔ λ₁ + λ₂′ + λ₃（λ₂′：A ⊆ B ⇒ B \ A ∈ L）；
  - Claim `isLambdaSys_good`：L_A 是 λ-系统。
* A4 `isSigmaField_of_lambda_pi`：Lemma 6：λ-系统 + π-系统 ⇒ σ-域。
  用 Mathlib 的 `disjointed`（Bₙ = Aₙ \ (A₀ ∪ ⋯ ∪ Aₙ₋₁)）不交化。
* A5 `pi_lambda`：主定理（Th 3.2 证明 ①）。
  L₀ 是 π-系统已由 A3 证明，所以由 Lemma 6（A4），L₀ 是 σ-域，于是 P ⊆ σ(P) ⊆ L₀ ⊆ L。

（笔记里先写证明 ①（假设 L₀ 是 π-系统），再写证明 ②。现在代码按题目顺序，
A3（证明 ②）在 A5 之前，所以 A5 可以直接使用 A3，不再需要「假设」。）
-/

/-! ## A1：λ(A) 是 λ-系统 -/

/-- L₀ = λ(P) 是 λ-系统：它是所有包含 P 的 λ-系统的交，三条性质在每一个里都成立。
--λ(A) 的定义是 ⋂₀ {L | L 是 λ-系统 且 A ⊆ L}
`mem_sInter : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t`；`hL.1`：L 是 λ-系统；`hL.2`：A ⊆ L。 -/
lemma lambdaGen_isLambdaSys (A : Set (Set Ω)) : IsLambdaSys (lambdaGen A) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (λ₁)
    exact mem_sInter.2 fun L hL => hL.1.univ_mem  --只需证对每个 L，Ω ∈ L
  · -- (λ₂)
    intro B hB
    exact mem_sInter.2 fun L hL => hL.1.compl_mem B ((mem_sInter.1 hB) L hL)
  · -- (λ₃)
    intro f hd hf
    exact mem_sInter.2 fun L hL =>
      hL.1.iUnion_mem f hd (fun n => mem_sInter.1 (hf n) L hL)

/-! ## A2：A ⊆ λ(A) -/

/-- P ⊆ L₀：P 包含在每个包含 P 的 λ-系统里。 -/
lemma subset_lambdaGen (A : Set (Set Ω)) : A ⊆ lambdaGen A := by
  intro B hB
  exact mem_sInter.2 fun L hL => hL.2 hB 

/-! ## A3：λ(P) 对交封闭（Th 3.2 证明 ②） -/

/-! ### A3 的辅助 1：最小性 -/

/-- 【辅助】最小性（"smallest λ-system"）：L 是 λ-系统且 A ⊆ L ⇒ λ(A) ⊆ L。（任何包含A的λ-system） -/
lemma lambdaGen_subset {A L : Set (Set Ω)} (hL : IsLambdaSys L) (hA : A ⊆ L) :
    lambdaGen A ⊆ L :=
  sInter_subset_of_mem ⟨hL, hA⟩

-- sInter_subset_of_mem ：如果 t 是集族 𝒮 中的一员，那么 ⋂₀ 𝒮 ⊆ t 
-- 这里 𝒮 = {L | L 是 λ-系统 且 A ⊆ L}，⋂₀ 𝒮 = λ(A)，t = L。 

/-! ### A3 的辅助 2：Remark：λ₁ + λ₂ + λ₃ ⇔ λ₁ + λ₂′ + λ₃ -/


/-- 【辅助】∅ ∈ L：∅ = Ωᶜ，用 λ₁、λ₂。 -/
lemma IsLambdaSys.empty_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) :
    (∅ : Set Ω) ∈ L := by
  simpa using hL.compl_mem univ hL.univ_mem

/-- 【辅助】两个不交集合的并（证明 ① 里「Bᶜ ∪ A ∈ L by λ₃」这一步）。
λ₃ 只讲可数并，所以把序列补成 A, B, ∅, ∅, …。 -/
lemma IsLambdaSys.union_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) {A B : Set Ω}
    (hA : A ∈ L) (hB : B ∈ L) (hAB : Disjoint A B) : A ∪ B ∈ L := by
  let f : ℕ → Set Ω := fun n => if n = 0 then A else if n = 1 then B else ∅
  have hU : (⋃ n, f n) = A ∪ B := by
    ext x --把证明两个集合相等变成证明他们的元素相等，相等也就是iff所以下面分成两个方向来解释
    simp only [mem_iUnion, mem_union, f] --改写之后 hn 即 x ∈ f(n)
    constructor --把↔拆成两个方向
    · rintro ⟨n, hn⟩ -- ⇒ 方向，把已知拿进来拆开 尖括号 ⟨ , ⟩：用逗号隔开，拆出的东西同时成立。一种情况，多样东西。
      split_ifs at hn --按if条件分情况 因为x在union n fn中那么也就意味着存在某个n使得x在其中一个集合中，所以分情况罗列
      · exact Or.inl hn          -- n = 0 （Or.inl 证明或） 此时意味着 x在A ∪ B中左边的那个集合exact后面是证据
      · exact Or.inr hn          -- n = 1 （Or.inr 证明或） 此时意味着 x在A ∪ B中右边的那个集合
      · simp at hn               -- n ≥ 2：x ∈ ∅，矛盾 （化简hn，hn变成false，因为x不可能属于空集）
    · rintro (hxA | hxB) -- ⇐ 方向 有两种情况 A？B？ 圆括号 ( | )：用竖线隔开，拆出的是不同的可能。多种情况，每种一样东西。
      · exact ⟨0, by simpa using hxA⟩ --x ∈ A
      · exact ⟨1, by simpa using hxB⟩ --x ∈ B
  rw [← hU] --rw [← hU]：从右往左用，把 A ∪ B 换成 ⋃ f(n)
  refine hL.iUnion_mem f ?_ ?_ --两个条件f两两不交，f每一项都在L里面
  · -- 两两不交：i、j 各取 0 / 1 / 其他，共 9 种情况
    intro i j hij
    show Disjoint (f i) (f j) --即要证明 fi fj不交
    simp only [f]
    split_ifs
    · omega                         -- (0,0)：与 i ≠ j 矛盾  omega 专门处理自然数（和整数）之间的等式、不等式
    · exact hAB                     -- (0,1)
    · exact disjoint_bot_right      -- (0,≥2) disjoint_bot_right是引理，任何集合都和空集不交
    · exact hAB.symm                -- (1,0) 把AB位置对调
    · omega                         -- (1,1)：矛盾
    · exact disjoint_bot_right      -- (1,≥2)
    · exact disjoint_bot_left       -- (≥2,0)
    · exact disjoint_bot_left       -- (≥2,1)
    · exact disjoint_bot_left       -- (≥2,≥2)
  · intro n --下面说明每一项都在L里面
    simp only [f]
    split_ifs
    · exact hA  --前面假设hA
    · exact hB
    · exact hL.empty_mem

/-- 证明 ①（λ₁+λ₂+λ₃ ⇒ λ₂′）：A, B ∈ L，A ⊆ B ⇒ B \ A ∈ L。
B \ A = B ∩ Aᶜ = (Bᶜ ∪ A)ᶜ（De Morgan）。
Bᶜ ∈ L（λ₂），Bᶜ 与 A 不交（因为 A ⊆ B），所以 Bᶜ ∪ A ∈ L（λ₃），再取补（λ₂）。 -/

  --任何λ-system都满足λ₂′
lemma IsLambdaSys.diff_mem {L : Set (Set Ω)} (hL : IsLambdaSys L) {A B : Set Ω}
    (hA : A ∈ L) (hB : B ∈ L) (hAB : A ⊆ B) : B \ A ∈ L := by
  have h : B \ A = (Bᶜ ∪ A)ᶜ := by
    ext x
    simp --把这个B \ A = (Bᶜ ∪ A)ᶜ化简成这个x ∈ B \ A ↔ x ∈ (Bᶜ ∪ A)ᶜ
  rw [h]
  -- `disjoint_compl_left : Disjoint Bᶜ B`；A ⊆ B 缩小右边得 Disjoint Bᶜ A

  have h1 : Bᶜ ∈ L := hL.compl_mem B hB
  have h2 : Disjoint Bᶜ A := disjoint_compl_left.mono_right hAB
  have h3 : Bᶜ ∪ A ∈ L := hL.union_mem h1 hA h2
  exact hL.compl_mem _ h3  --后面跟对象 然后跟对象属于L
  --B ∈ L ⇒ Bᶜ ∈ L（λ₂），A ∈ L，所以 Bᶜ ∪ A ∈ L（λ₃，不交），所以 (Bᶜ ∪ A)ᶜ ∈ L（λ₂）

/-- 证明 ②（λ₁+λ₂′+λ₃ ⇒ λ₁+λ₂+λ₃）：取 B = Ω，Ω \ A = Aᶜ ∈ L。 即说明complement还在L就可以了-/
lemma isLambdaSys_of_diff {L : Set (Set Ω)} (h1 : univ ∈ L)
    (h2' : ∀ A ∈ L, ∀ B ∈ L, A ⊆ B → B \ A ∈ L)
    (h3 : ∀ f : ℕ → Set Ω, Pairwise (Disjoint on f) → (∀ n, f n ∈ L) →
      (⋃ n, f n) ∈ L) : IsLambdaSys L := by
  refine ⟨h1, ?_, h3⟩
  intro A hA
  have h : Aᶜ = univ \ A := by
    ext x
    simp
  rw [h]
  exact h2' A hA univ h1 (subset_univ A) --一一对应h2‘的条件

/-! ### A3 的辅助 3：Claim：L_A 是 λ-系统 -/


/-- Claim：L 是 λ-系统且 A ∈ L 时，L_A = {B | A ∩ B ∈ L} 是 λ-系统。
验证 λ₁、λ₂′、λ₃，再用 Remark 的证明 ②：
* (λ₁) A ∩ Ω = A ∈ L；
* (λ₂′) B₁ ⊆ B₂：A ∩ (B₂ \ B₁) = (A ∩ B₂) \ (A ∩ B₁)，A ∩ B₁ ⊆ A ∩ B₂，用 L 的 λ₂′；
* (λ₃) A ∩ (⋃ Bₙ) = ⋃ (A ∩ Bₙ)，A ∩ Bₙ 仍两两不交，用 L 的 λ₃。 -/
lemma isLambdaSys_good {L : Set (Set Ω)} (hL : IsLambdaSys L) {A : Set Ω}
    (hA : A ∈ L) : IsLambdaSys {B | A ∩ B ∈ L} := by
  apply isLambdaSys_of_diff
  · -- (λ₁)
    show A ∩ univ ∈ L
    simpa using hA
  · -- (λ₂′)
    intro B₁ hB₁ B₂ hB₂ h12
    show A ∩ (B₂ \ B₁) ∈ L
    have h : A ∩ (B₂ \ B₁) = (A ∩ B₂) \ (A ∩ B₁) := by
      ext x
      constructor
      · rintro ⟨hxA, hx2, hx1⟩
        exact ⟨⟨hxA, hx2⟩, fun h => hx1 h.2⟩
      · rintro ⟨⟨hxA, hx2⟩, hx⟩
        exact ⟨hxA, hx2, fun h1 => hx ⟨hxA, h1⟩⟩
    rw [h]
    exact hL.diff_mem hB₁ hB₂ (inter_subset_inter_right A h12)
  · -- (λ₃)
    intro f hf hfL
    show A ∩ ⋃ n, f n ∈ L
    rw [inter_iUnion]                 -- A ∩ (⋃ Bₙ) = ⋃ (A ∩ Bₙ)
    refine hL.iUnion_mem _ ?_ hfL
    intro i j hij
    show Disjoint (A ∩ f i) (A ∩ f j)
    exact Disjoint.mono inter_subset_right inter_subset_right (hf hij)

/-! ### A3 本身 -/


/-- L₀ 对交封闭。路线 P × P → P × L₀ → L₀ × L₀：
* 第一轮：A ∈ P 固定。B ∈ P ⇒ A ∩ B ∈ P ⊆ L₀，即 P ⊆ L_A；
  L_A 是 λ-系统（Claim），最小性 ⇒ L₀ ⊆ L_A。
* 第二轮：B ∈ L₀ 固定。对 A ∈ P，由第一轮 A ∩ B ∈ L₀，所以 P ⊆ L_B；
  最小性 ⇒ L₀ ⊆ L_B，即 B, C ∈ L₀ ⇒ B ∩ C ∈ L₀。 -/
lemma lambdaGen_inter (P : Set (Set Ω)) (hP : IsPiSys P) :
    ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P := by
  have hL₀ := lambdaGen_isLambdaSys P
  -- 第一轮：P × P → P × L₀
  have round1 : ∀ A ∈ P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P := by
    intro A hA
    exact lambdaGen_subset (isLambdaSys_good hL₀ (subset_lambdaGen P hA))
      fun B hB => subset_lambdaGen P (hP A hA B hB)
  -- 第二轮：P × L₀ → L₀ × L₀（固定 B ∈ L₀，考虑 L_B）
  intro B hB C hC
  have hPB : P ⊆ {D | B ∩ D ∈ lambdaGen P} := by
    intro A hA
    show B ∩ A ∈ lambdaGen P
    rw [inter_comm]                   -- B ∩ A = A ∩ B
    exact round1 A hA B hB
  exact lambdaGen_subset (isLambdaSys_good hL₀ hB) hPB hC

/-! ## A4：λ-系统 + 对交封闭 ⇒ σ-域（Lemma 6） -/
--大纲1.σ-域的前两条直接用 λ₁、λ₂，只剩可数并。
--2.任取 A₀, A₁, … ∈ F，令 Bₙ = disjointed f n = Aₙ \ (A₀ ∪ ⋯ ∪ Aₙ₋₁)。
--3.⋃ Bₙ = ⋃ Aₙ。（iUnion_disjointed）
--4.Bₙ 两两不交。（disjoint_disjointed）
--5.每个 Bₙ ∈ F：从 Aₙ 出发一次减去一项，t \ Aᵢ = t ∩ Aᵢᶜ，用补集（λ₂）和交（π）。（disjointedRec）
--6.由 λ₃，⋃ Bₙ ∈ F，所以 ⋃ Aₙ ∈ F。


/-- Lemma 6：既是 π-system 又是 λ-system 的类是 σ-field。
用 Mathlib 的 `disjointed`：disjointed f n = Aₙ \ (A₀ ∪ ⋯ ∪ Aₙ₋₁)，
也就是笔记里的 Bₙ = Aₙ ∩ Aₙ₋₁ᶜ ∩ ⋯ ∩ A₀ᶜ。
* Bₙ 两两不交：`disjoint_disjointed`；
* ⋃ Bₙ = ⋃ Aₙ：`iUnion_disjointed`；
* Bₙ ∈ L：`disjointedRec`，每一步只是「减去一项」，t \ Aᵢ = t ∩ Aᵢᶜ（λ₂ + π）。 -/
lemma isSigmaField_of_lambda_pi (L : Set (Set Ω)) (hL : IsLambdaSys L)
    (hπ : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) : IsSigmaField L := by
  -- σ-域的前两条直接来自 λ₁、λ₂，只剩可数并
  refine ⟨hL.univ_mem, hL.compl_mem, fun f hf => ?_⟩
  -- ⋃ Aₙ 换成 ⋃ Bₙ（Bₙ = disjointed f n）
  rw [← iUnion_disjointed]
  -- Bₙ 两两不交，用 λ₃；剩下要证每个 Bₙ ∈ L
  refine hL.iUnion_mem _ (disjoint_disjointed f) fun n => ?_
  -- Bₙ 是从 Aₙ 出发，一次减去一项得到的；每次减去一项都留在 L 里
  refine disjointedRec (p := fun t => t ∈ L) (fun t i ht => ?_) (hf n)
  -- t \ Aᵢ = t ∩ Aᵢᶜ：Aᵢᶜ ∈ L（λ₂），交集 ∈ L（π）
  have h : t \ f i = t ∩ (f i)ᶜ := by
    ext x
    simp
  rw [h]
  exact hπ _ ht _ (hL.compl_mem _ (hf i))

/-! ## A5：主定理（Th 3.2） -/

/-- Th 3.2（Dynkin π-λ 定理）：P 是 π-系统，L 是 λ-系统，P ⊆ L ⇒ σ(P) ⊆ L。
L₀ = λ(P) 是 π-系统已经在 A3 证明了，这里直接使用：
* 由 A1，L₀ 是 λ-系统；由 A3，L₀ 对交封闭；由 Lemma 6（A4），L₀ 是 σ-域；
* σ(P) 是包含 P 的最小 σ-域，而 L₀ 是包含 P 的 σ-域（A2），所以 σ(P) ⊆ L₀；
* L₀ 是包含 P 的最小 λ-系统，L 是包含 P 的 λ-系统，所以 L₀ ⊆ L。
即 P ⊆ σ(P) ⊆ L₀ ⊆ L。 -/
theorem pi_lambda (P L : Set (Set Ω)) (hP : IsPiSys P) (hL : IsLambdaSys L)
    (hPL : P ⊆ L) : sigmaGen P ⊆ L := by
  -- L₀ 对交封闭（A3，Th 3.2 证明 ②）
  have hπ₀ : ∀ A ∈ lambdaGen P, ∀ B ∈ lambdaGen P, A ∩ B ∈ lambdaGen P :=
    lambdaGen_inter P hP
  -- L₀ 是 σ-域（A1 + A3 + A4）
  have hσ : IsSigmaField (lambdaGen P) :=
    isSigmaField_of_lambda_pi _ (lambdaGen_isLambdaSys P) hπ₀
  -- σ(P) ⊆ L₀：sigmaGen 也是 ⋂₀，L₀ 是其中一员
  have h1 : sigmaGen P ⊆ lambdaGen P :=
    sInter_subset_of_mem ⟨hσ, subset_lambdaGen P⟩
  -- L₀ ⊆ L：最小性
  exact h1.trans (lambdaGen_subset hL hPL)

end Math7800.Midterm

#print axioms Math7800.Midterm.lambdaGen_isLambdaSys
#print axioms Math7800.Midterm.subset_lambdaGen
#print axioms Math7800.Midterm.lambdaGen_inter
#print axioms Math7800.Midterm.isSigmaField_of_lambda_pi
#print axioms Math7800.Midterm.pi_lambda
