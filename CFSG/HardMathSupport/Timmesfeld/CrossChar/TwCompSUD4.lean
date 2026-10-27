module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.RankThree.PartOne.KGD.D4A2Frame

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice
open CFSG.RankThree.PartOne.KGD
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

@[expose] def d4ExtVec : Option (Fin 4) → Fin Tag.D4.rank → ℤ
  | none => -![1, 1, 2, 1]
  | some j => Pi.single j 1

@[expose] def d4EdgeWord : Option (Fin 4) → Option (Fin 4) → List (Fin Tag.D4.rank)
  | some 1, some 2 => [3, 2, 1, 0, 2, 3]
  | some 2, some 0 => [3, 2, 1, 0, 2, 3, 0, 2, 1]
  | some 2, some 1 => [0, 2, 1]
  | some 2, some 3 => [0, 2, 3]
  | some 2, none => [1, 2, 3, 2, 1, 0, 2]
  | some 3, some 2 => [1, 2, 3, 0, 2, 1]
  | none, some 2 => [0, 2, 3, 1, 2, 0]
  | _, _ => []

@[expose] def d4Anc : ℕ → List ℕ
  | 0 => [0, 3]
  | 1 => [1, 3]
  | 2 => [2, 3]
  | 3 => [3]
  | 4 => [4, 3]
  | _ => []

@[expose] def d4EdgeIdx : List (ℕ × ℕ) :=
    [(0, 3), (1, 3), (2, 3), (3, 0), (3, 1), (3, 2), (3, 4), (4, 3)]

@[expose] def d4Conn : List (List ℕ) :=
    [[0], [1], [2], [3], [4], [0, 3], [1, 3], [2, 3], [3, 4], [0, 1, 3], [0, 2, 3], [0, 3, 4],
     [1, 2, 3], [1, 3, 4], [2, 3, 4], [0, 1, 2, 3], [0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4],
     [0, 1, 2, 3, 4]]

@[expose] def d4APathsRaw : List (List (Option (Fin 4))) :=
    [[none, some 2], [some 0, some 2], [some 1, some 2], [some 2, some 3], [none, some 2, some 0],
     [none, some 2, some 1], [none, some 2, some 3], [some 0, some 2, some 1],
     [some 0, some 2, some 3], [some 1, some 2, some 3]]

@[expose] def d4APaths : List (List (Option (Fin Tag.D4.rank))) := d4APathsRaw

theorem kacD4_extRoot : kacD4.extRoot = d4ExtVec := by
  funext x
  cases x <;> rfl

set_option maxRecDepth 100000

theorem d4_tree : IsTreePaths (Tag.D4.rank + 1) d4EdgeIdx (treePath d4Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem d4_adj_raw : ∀ x y : Option (Fin 4),
    (x ≠ y ∧ iform (d4ExtVec x) (d4ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ d4EdgeIdx := by
  decide +kernel

theorem d4_adj :
    ∀ x y : Option (Fin Tag.D4.rank), kacD4.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ d4EdgeIdx := by
  intro x y
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.Adj
  rw [kacD4_extRoot]
  exact d4_adj_raw x y

theorem d4_check : ((List.range (Tag.D4.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => d4Conn.any (sameSet (compIdx (Tag.D4.rank + 1) (treePath d4Anc) zl x))) =
        true := by
  decide +kernel

theorem d4_lt : ∀ c ∈ d4Conn, ∀ w ∈ c, w < Tag.D4.rank + 1 := by
  decide +kernel

theorem d4_card : ∀ c ∈ d4Conn, (c.map (idxNode (r := Tag.D4.rank))).toFinset.card = c.length := by
  decide +kernel

theorem d4_count_raw : ∀ c ∈ d4Conn, 2 ≤ c.length →
    kacCount Tag.D4 ![1, 1, 2, 1] (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ d4APaths, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem d4_count : ∀ c ∈ d4Conn, 2 ≤ c.length →
    kacCount Tag.D4 kacD4.θ (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ d4APaths, sameSet c (P.map nodeIdx) = true :=
  d4_count_raw

theorem d4_paths_raw : ∀ P ∈ d4APathsRaw, P.Nodup ∧ 2 ≤ P.length ∧
    (∀ c d : Fin P.length, iform (d4ExtVec (P.get c)) (d4ExtVec (P.get d)) = chainGram c d) ∧
    ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
      (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ d4EdgeIdx := by
  decide +kernel

theorem d4_paths :
    ∀ P ∈ d4APaths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length,
        iform (kacD4.extRoot (P.get c)) (kacD4.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ d4EdgeIdx := by
  rw [kacD4_extRoot]
  exact d4_paths_raw

theorem d4_words : ∀ x y : Option (Fin 4), (nodeIdx x, nodeIdx y) ∈ d4EdgeIdx →
    wordMat Tag.D4 (d4EdgeWord x y) *ᵥ (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = d4ExtVec x ∧
    wordMat Tag.D4 (d4EdgeWord x y) *ᵥ (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = d4ExtVec y := by
  decide +kernel

section Frames

theorem d4_base_01 :
    CFSG.RankThree.E6.chainRoot CFSG.RankThree.Chevalley.d4ChainA2 0 1 =
      (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

theorem d4_base_12 :
    CFSG.RankThree.E6.chainRoot CFSG.RankThree.Chevalley.d4ChainA2 1 2 =
      (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) := by
  decide +kernel

theorem d4_frames {L : Type} [Field L] : ∀ x y : Option (Fin Tag.D4.rank),
    (nodeIdx x, nodeIdx y) ∈ d4EdgeIdx →
      ∃ (ρ : SL(3, L) →* ModGL Tag.D4 L) (σ : Fin 3 → Fin 3 → Fin Tag.D4.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = kacD4.extRoot x ∧
          σ 1 2 = kacD4.extRoot y := by
  intro x y h
  rw [kacD4_extRoot]
  obtain ⟨h1, h2⟩ := d4_words x y h
  refine exists_a2Frame_of_word (d4Std_frame (L := L)) (d4EdgeWord x y) ?_ ?_
  · rw [d4_base_01]
    exact h1
  · rw [d4_base_12]
    exact h2

theorem exists_frame_of_typeA_D4_T_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.D4.rank → Lˣ} (hTp : rootDiagUnit Tag.D4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.D4 L) (σ : Fin ν → Fin ν → Fin Tag.D4.rank → ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ :=
  exists_frame_of_typeA_T_of_prime (Or.inl rfl) kacD4 facts_D4 d4_tree d4_adj d4_check
    d4_lt d4_card d4_count d4_paths d4_frames S hp hpL hTp i h2 hn

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar

