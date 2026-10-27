module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.TCX.E CFSG.RankThree.E6
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

@[expose] def e6ExtVec : Option (Fin 6) → Fin Tag.E6.rank → ℤ
  | none => -![1, 2, 2, 3, 2, 1]
  | some j => Pi.single j 1

@[expose] def e6EdgeWord : Option (Fin 6) → Option (Fin 6) → List (Fin Tag.E6.rank)
  | some 1, some 3 => [4, 3, 2, 1, 3, 4, 0, 2, 3]
  | some 1, none => [3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]
  | some 2, some 0 => [3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 2, some 3 => [0, 2, 3]
  | some 3, some 1 => [2, 3, 0, 2, 1, 3]
  | some 3, some 2 => [4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 3, some 4 => [2, 3, 4, 0, 2, 3]
  | some 4, some 3 => [1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 4, some 5 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 5, some 4 => [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | none, some 1 => [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]
  | _, _ => []

@[expose] def e6Anc : ℕ → List ℕ
  | 0 => [0, 2, 4]
  | 1 => [1, 3, 4]
  | 2 => [2, 4]
  | 3 => [3, 4]
  | 4 => [4]
  | 5 => [5, 4]
  | 6 => [6, 5, 4]
  | _ => []

@[expose] def e6EdgeIdx : List (ℕ × ℕ) :=
    [(0, 2), (1, 3), (2, 0), (2, 4), (3, 1), (3, 4), (4, 2), (4, 3), (4, 5), (5, 4), (5, 6), (6, 5)]

@[expose] def e6Conn : List (List ℕ) :=
    [[0], [1], [2], [3], [4], [5], [6], [0, 2], [1, 3], [2, 4], [3, 4], [4, 5], [5, 6], [0, 2, 4],
     [1, 3, 4], [2, 3, 4], [2, 4, 5], [3, 4, 5], [4, 5, 6], [0, 2, 3, 4], [0, 2, 4, 5],
     [1, 2, 3, 4], [1, 3, 4, 5], [2, 3, 4, 5], [2, 4, 5, 6], [3, 4, 5, 6], [0, 1, 2, 3, 4],
     [0, 2, 3, 4, 5], [0, 2, 4, 5, 6], [1, 2, 3, 4, 5], [1, 3, 4, 5, 6], [2, 3, 4, 5, 6],
     [0, 1, 2, 3, 4, 5], [0, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6]]

@[expose] def e6APathsRaw : List (List (Option (Fin 6))) :=
    [[none, some 1], [some 0, some 2], [some 1, some 3], [some 2, some 3], [some 3, some 4],
     [some 4, some 5], [none, some 1, some 3], [some 0, some 2, some 3], [some 1, some 3, some 2],
     [some 1, some 3, some 4], [some 2, some 3, some 4], [some 3, some 4, some 5],
     [none, some 1, some 3, some 2], [none, some 1, some 3, some 4],
     [some 0, some 2, some 3, some 1], [some 0, some 2, some 3, some 4],
     [some 1, some 3, some 4, some 5], [some 2, some 3, some 4, some 5],
     [none, some 1, some 3, some 2, some 0], [none, some 1, some 3, some 4, some 5],
     [some 0, some 2, some 3, some 4, some 5]]

@[expose] def e6APaths : List (List (Option (Fin Tag.E6.rank))) := e6APathsRaw

theorem kacE6_extRoot : kacE6.extRoot = e6ExtVec := by
  funext x
  cases x <;> rfl

set_option maxRecDepth 100000

theorem e6_tree : IsTreePaths (Tag.E6.rank + 1) e6EdgeIdx (treePath e6Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem e6_adj_raw : ∀ x y : Option (Fin 6),
    (x ≠ y ∧ iform (e6ExtVec x) (e6ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx := by
  decide +kernel

theorem e6_adj :
    ∀ x y : Option (Fin Tag.E6.rank), kacE6.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx := by
  intro x y
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj
  rw [kacE6_extRoot]
  exact e6_adj_raw x y

theorem e6_check : ((List.range (Tag.E6.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => e6Conn.any (sameSet (compIdx (Tag.E6.rank + 1) (treePath e6Anc) zl x))) =
        true := by
  decide +kernel

theorem e6_lt : ∀ c ∈ e6Conn, ∀ w ∈ c, w < Tag.E6.rank + 1 := by
  decide +kernel

theorem e6_card : ∀ c ∈ e6Conn, (c.map (idxNode (r := Tag.E6.rank))).toFinset.card = c.length := by
  decide +kernel

theorem e6_count_raw : ∀ c ∈ e6Conn, 2 ≤ c.length →
    kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e6APaths, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e6_count : ∀ c ∈ e6Conn, 2 ≤ c.length →
    kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e6APaths, sameSet c (P.map nodeIdx) = true :=
  e6_count_raw

theorem e6_paths_raw : ∀ P ∈ e6APathsRaw, P.Nodup ∧ 2 ≤ P.length ∧
    (∀ c d : Fin P.length, iform (e6ExtVec (P.get c)) (e6ExtVec (P.get d)) = chainGram c d) ∧
    ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
      (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e6EdgeIdx := by
  decide +kernel

theorem e6_paths :
    ∀ P ∈ e6APaths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length,
        iform (kacE6.extRoot (P.get c)) (kacE6.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e6EdgeIdx := by
  rw [kacE6_extRoot]
  exact e6_paths_raw

theorem e6_words : ∀ x y : Option (Fin 6), (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx →
    wordMat Tag.E6 (e6EdgeWord x y) *ᵥ (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = e6ExtVec x ∧
    wordMat Tag.E6 (e6EdgeWord x y) *ᵥ (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = e6ExtVec y := by
  decide +kernel

section Frames

theorem e6_chain13_add : ∀ i j k : Fin 3,
    CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j +
      CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 j k =
        CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i k := by
  decide +kernel

theorem e6_base_frame {L : Type} [Field L] :
    CFSG.RankThree.PartOne.KF4.IsA2Frame (a2Std₁.ρ L)
      (fun i j => CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 i j) :=
  { injective := a2Std₁.inj L
    isRoot := fun i j hij => ((a2Std₁.roots _).2 ⟨i, j, hij, rfl⟩).1
    neg := fun i j => CFSG.RankThree.E6.chainRoot_swap _ i j
    add := e6_chain13_add
    transv := a2Std₁.gen L
    range := by
      rw [a2Std₁.range L, subsystemGroup_eq_rootSpan]
      congr 1
      ext α
      exact a2Std₁.roots α
    diag := a2Std₁.diag L }

theorem e6_base_01 : CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 0 1 =
    (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem e6_base_12 : CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain13 1 2 =
    (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

theorem e6_frames {L : Type} [Field L] : ∀ x y : Option (Fin Tag.E6.rank),
    (nodeIdx x, nodeIdx y) ∈ e6EdgeIdx →
      ∃ (ρ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = kacE6.extRoot x ∧
          σ 1 2 = kacE6.extRoot y := by
  intro x y h
  rw [kacE6_extRoot]
  obtain ⟨h1, h2⟩ := e6_words x y h
  refine exists_a2Frame_of_word (e6_base_frame (L := L)) (e6EdgeWord x y) ?_ ?_
  · rw [e6_base_01]
    exact h1
  · rw [e6_base_12]
    exact h2

theorem exists_frame_of_typeA_E6_T_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTp : rootDiagUnit Tag.E6 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.E6 L) (σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ :=
  exists_frame_of_typeA_T_of_prime (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
    e6_lt e6_card e6_count e6_paths e6_frames S hp hpL hTp i h2 hn

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar

