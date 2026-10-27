module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

@[expose] def e7ExtVec : Option (Fin 7) → Fin Tag.E7.rank → ℤ
  | none => -![2, 2, 3, 4, 3, 2, 1]
  | some j => Pi.single j 1

@[expose] def e7EdgeWord : Option (Fin 7) → Option (Fin 7) → List (Fin Tag.E7.rank)
  | some 0, none => [2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 0, 2]
  | some 1, some 3 => [4, 3, 2, 1, 3, 4, 0, 2, 3]
  | some 2, some 0 => [3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 2, some 3 => [0, 2, 3]
  | some 3, some 1 => [2, 3, 0, 2, 1, 3]
  | some 3, some 2 => [4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 3, some 4 => [2, 3, 4, 0, 2, 3]
  | some 4, some 3 => [1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 4, some 5 => [3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 5, some 4 => [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | some 5, some 6 => [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]
  | some 6, some 5 => [4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]
  | none, some 0 => [2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0]
  | _, _ => []

@[expose] def e7Anc : ℕ → List ℕ
  | 0 => [0, 1, 3]
  | 1 => [1, 3]
  | 2 => [2, 4, 3]
  | 3 => [3]
  | 4 => [4, 3]
  | 5 => [5, 4, 3]
  | 6 => [6, 5, 4, 3]
  | 7 => [7, 6, 5, 4, 3]
  | _ => []

@[expose] def e7EdgeIdx : List (ℕ × ℕ) :=
    [(0, 1), (1, 0), (1, 3), (2, 4), (3, 1), (3, 4), (4, 2), (4, 3), (4, 5), (5, 4), (5, 6), (6, 5),
     (6, 7), (7, 6)]

@[expose] def e7Conn : List (List ℕ) :=
    [[0], [1], [2], [3], [4], [5], [6], [7], [0, 1], [1, 3], [2, 4], [3, 4], [4, 5], [5, 6], [6, 7],
     [0, 1, 3], [1, 3, 4], [2, 3, 4], [2, 4, 5], [3, 4, 5], [4, 5, 6], [5, 6, 7], [0, 1, 3, 4],
     [1, 2, 3, 4], [1, 3, 4, 5], [2, 3, 4, 5], [2, 4, 5, 6], [3, 4, 5, 6], [4, 5, 6, 7],
     [0, 1, 2, 3, 4], [0, 1, 3, 4, 5], [1, 2, 3, 4, 5], [1, 3, 4, 5, 6], [2, 3, 4, 5, 6],
     [2, 4, 5, 6, 7], [3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5], [0, 1, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6],
     [1, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6], [0, 1, 3, 4, 5, 6, 7],
     [1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7]]

@[expose] def e7APathsRaw : List (List (Option (Fin 7))) :=
    [[none, some 0], [some 0, some 2], [some 1, some 3], [some 2, some 3], [some 3, some 4],
     [some 4, some 5], [some 5, some 6], [none, some 0, some 2], [some 0, some 2, some 3],
     [some 1, some 3, some 2], [some 1, some 3, some 4], [some 2, some 3, some 4],
     [some 3, some 4, some 5], [some 4, some 5, some 6], [none, some 0, some 2, some 3],
     [some 0, some 2, some 3, some 1], [some 0, some 2, some 3, some 4],
     [some 1, some 3, some 4, some 5], [some 2, some 3, some 4, some 5],
     [some 3, some 4, some 5, some 6], [none, some 0, some 2, some 3, some 1],
     [none, some 0, some 2, some 3, some 4], [some 0, some 2, some 3, some 4, some 5],
     [some 1, some 3, some 4, some 5, some 6], [some 2, some 3, some 4, some 5, some 6],
     [none, some 0, some 2, some 3, some 4, some 5],
     [some 0, some 2, some 3, some 4, some 5, some 6],
     [none, some 0, some 2, some 3, some 4, some 5, some 6]]

@[expose] def e7APaths : List (List (Option (Fin Tag.E7.rank))) := e7APathsRaw

theorem kacE7_extRoot : kacE7.extRoot = e7ExtVec := by
  funext x
  cases x <;> rfl

set_option maxRecDepth 100000

theorem e7_tree : IsTreePaths (Tag.E7.rank + 1) e7EdgeIdx (treePath e7Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem e7_adj_raw : ∀ x y : Option (Fin 7),
    (x ≠ y ∧ iform (e7ExtVec x) (e7ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ e7EdgeIdx := by
  decide +kernel

theorem e7_adj :
    ∀ x y : Option (Fin Tag.E7.rank), kacE7.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ e7EdgeIdx := by
  intro x y
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj
  rw [kacE7_extRoot]
  exact e7_adj_raw x y

theorem e7_check : ((List.range (Tag.E7.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => e7Conn.any (sameSet (compIdx (Tag.E7.rank + 1) (treePath e7Anc) zl x))) =
        true := by
  decide +kernel

theorem e7_lt : ∀ c ∈ e7Conn, ∀ w ∈ c, w < Tag.E7.rank + 1 := by
  decide +kernel

theorem e7_card : ∀ c ∈ e7Conn, (c.map (idxNode (r := Tag.E7.rank))).toFinset.card = c.length := by
  decide +kernel

theorem e7_count_raw : ∀ c ∈ e7Conn, 2 ≤ c.length →
    kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e7APaths, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e7_count : ∀ c ∈ e7Conn, 2 ≤ c.length →
    kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e7APaths, sameSet c (P.map nodeIdx) = true :=
  e7_count_raw

theorem e7_paths_raw : ∀ P ∈ e7APathsRaw, P.Nodup ∧ 2 ≤ P.length ∧
    (∀ c d : Fin P.length, iform (e7ExtVec (P.get c)) (e7ExtVec (P.get d)) = chainGram c d) ∧
    ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
      (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e7EdgeIdx := by
  decide +kernel

theorem e7_paths :
    ∀ P ∈ e7APaths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length,
        iform (kacE7.extRoot (P.get c)) (kacE7.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e7EdgeIdx := by
  rw [kacE7_extRoot]
  exact e7_paths_raw

theorem e7_words : ∀ x y : Option (Fin 7), (nodeIdx x, nodeIdx y) ∈ e7EdgeIdx →
    wordMat Tag.E7 (e7EdgeWord x y) *ᵥ (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) = e7ExtVec x ∧
    wordMat Tag.E7 (e7EdgeWord x y) *ᵥ (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) = e7ExtVec y := by
  decide +kernel

section Frames

theorem e7_base_frame {L : Type} [Field L] :
    CFSG.RankThree.PartOne.KF4.IsA2Frame (rhoSigma L 1) (sigmaRoot 1) where
  injective := rhoSigma_injective 1
  isRoot _ _ hij := isRoot_sigmaRoot 1 hij
  neg i j := (sigmaRoot_neg 1 i j).symm
  add := sigmaRoot_add 1
  transv := rhoSigma_transvection 1
  range := by rw [rhoSigma_range, sigmaSet_eq]
  diag := rhoSigma_diagonal 1

theorem e7_base_01 : sigmaRoot 1 0 1 = (Pi.single 0 1 : Fin Tag.E7.rank → ℤ) := by
  rw [sigmaRoot_eq_smul, one_smul, chainRoot13_values.1]
  rfl

theorem e7_base_12 : sigmaRoot 1 1 2 = (Pi.single 2 1 : Fin Tag.E7.rank → ℤ) := by
  rw [sigmaRoot_eq_smul, one_smul, chainRoot13_values.2.1]
  rfl

theorem e7_frames {L : Type} [Field L] : ∀ x y : Option (Fin Tag.E7.rank),
    (nodeIdx x, nodeIdx y) ∈ e7EdgeIdx →
      ∃ (ρ : SL(3, L) →* ModGL Tag.E7 L) (σ : Fin 3 → Fin 3 → Fin Tag.E7.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = kacE7.extRoot x ∧
          σ 1 2 = kacE7.extRoot y := by
  intro x y h
  rw [kacE7_extRoot]
  obtain ⟨h1, h2⟩ := e7_words x y h
  refine exists_a2Frame_of_word (e7_base_frame (L := L)) (e7EdgeWord x y) ?_ ?_
  · rw [e7_base_01]
    exact h1
  · rw [e7_base_12]
    exact h2

theorem exists_frame_of_typeA_E7_T_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTp : rootDiagUnit Tag.E7 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.E7 L) (σ : Fin ν → Fin ν → Fin Tag.E7.rank → ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ :=
  exists_frame_of_typeA_T_of_prime (Or.inr (Or.inr (Or.inl rfl)))
    kacE7 facts_E7 e7_tree e7_adj e7_check
    e7_lt e7_card e7_count e7_paths e7_frames S hp hpL hTp i h2 hn

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar

