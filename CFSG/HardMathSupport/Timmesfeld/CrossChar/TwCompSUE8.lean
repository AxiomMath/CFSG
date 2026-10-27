module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompE8

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

@[expose] def e8Anc : ℕ → List ℕ
  | 0 => [0, 8, 7, 6, 5, 4]
  | 1 => [1, 3, 4]
  | 2 => [2, 4]
  | 3 => [3, 4]
  | 4 => [4]
  | 5 => [5, 4]
  | 6 => [6, 5, 4]
  | 7 => [7, 6, 5, 4]
  | 8 => [8, 7, 6, 5, 4]
  | _ => []

@[expose] def e8EdgeIdx : List (ℕ × ℕ) :=
  [(0, 8), (1, 3), (2, 4), (3, 1), (3, 4), (4, 2), (4, 3), (4, 5), (5, 4), (5, 6), (6, 5), (6, 7),
    (7, 6), (7, 8), (8, 0), (8, 7)]

@[expose] def e8Conn : List (List ℕ) :=
  [[0], [1], [2], [3], [4], [5], [6], [7], [8], [0, 8], [1, 3], [2, 4], [3, 4], [4, 5], [5, 6],
   [6, 7], [7, 8], [0, 7, 8], [1, 3, 4], [2, 3, 4], [2, 4, 5], [3, 4, 5], [4, 5, 6], [5, 6, 7],
   [6, 7, 8], [0, 6, 7, 8], [1, 2, 3, 4], [1, 3, 4, 5], [2, 3, 4, 5], [2, 4, 5, 6], [3, 4, 5, 6],
   [4, 5, 6, 7], [5, 6, 7, 8], [0, 5, 6, 7, 8], [1, 2, 3, 4, 5], [1, 3, 4, 5, 6], [2, 3, 4, 5, 6],
   [2, 4, 5, 6, 7], [3, 4, 5, 6, 7], [4, 5, 6, 7, 8], [0, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6],
   [1, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 7], [2, 4, 5, 6, 7, 8], [3, 4, 5, 6, 7, 8],
   [0, 2, 4, 5, 6, 7, 8], [0, 3, 4, 5, 6, 7, 8], [1, 2, 3, 4, 5, 6, 7], [1, 3, 4, 5, 6, 7, 8],
   [2, 3, 4, 5, 6, 7, 8], [0, 1, 3, 4, 5, 6, 7, 8], [0, 2, 3, 4, 5, 6, 7, 8],
   [1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8]]

@[expose] def e8APathsRaw : List (List (Option (Fin 8))) :=
  [[none, some 7], [some 0, some 2], [some 1, some 3], [some 2, some 3], [some 3, some 4],
   [some 4, some 5], [some 5, some 6], [some 6, some 7], [none, some 7, some 6],
   [some 0, some 2, some 3], [some 1, some 3, some 2], [some 1, some 3, some 4],
   [some 2, some 3, some 4], [some 3, some 4, some 5], [some 4, some 5, some 6],
   [some 5, some 6, some 7], [none, some 7, some 6, some 5], [some 0, some 2, some 3, some 1],
   [some 0, some 2, some 3, some 4], [some 1, some 3, some 4, some 5],
   [some 2, some 3, some 4, some 5], [some 3, some 4, some 5, some 6],
   [some 4, some 5, some 6, some 7], [none, some 7, some 6, some 5, some 4],
   [some 0, some 2, some 3, some 4, some 5], [some 1, some 3, some 4, some 5, some 6],
   [some 2, some 3, some 4, some 5, some 6], [some 3, some 4, some 5, some 6, some 7],
   [none, some 7, some 6, some 5, some 4, some 3],
   [some 0, some 2, some 3, some 4, some 5, some 6],
   [some 1, some 3, some 4, some 5, some 6, some 7],
   [some 2, some 3, some 4, some 5, some 6, some 7],
   [none, some 7, some 6, some 5, some 4, some 3, some 1],
   [none, some 7, some 6, some 5, some 4, some 3, some 2],
   [some 0, some 2, some 3, some 4, some 5, some 6, some 7],
   [none, some 7, some 6, some 5, some 4, some 3, some 2, some 0]]

@[expose] def e8APaths : List (List (Option (Fin Tag.E8.rank))) := e8APathsRaw

set_option maxRecDepth 100000

theorem e8_tree : IsTreePaths (Tag.E8.rank + 1) e8EdgeIdx (treePath e8Anc) where
  self := by decide +kernel
  lt := by decide +kernel
  head := by decide +kernel
  last := by decide +kernel
  chain := by decide +kernel
  step := by decide +kernel

theorem e8_adj_raw : ∀ x y : Option (Fin 8),
    (x ≠ y ∧ iform (e8ExtVec x) (e8ExtVec y) ≠ 0) ↔ (nodeIdx x, nodeIdx y) ∈ e8EdgeIdx := by
  decide +kernel

theorem e8_adj :
    ∀ x y : Option (Fin Tag.E8.rank),
      kacE8.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ e8EdgeIdx := by
  intro x y
  unfold KacData.Adj
  rw [kacE8_extRoot]
  exact e8_adj_raw x y

theorem e8_check : ((List.range (Tag.E8.rank + 1)).sublists.all fun zl =>
    !(fun _ : List ℕ => true) zl ||
      zl.all fun x => e8Conn.any (sameSet (compIdx (Tag.E8.rank + 1) (treePath e8Anc) zl x))) =
        true := by
  decide +kernel

theorem e8_lt : ∀ c ∈ e8Conn, ∀ w ∈ c, w < Tag.E8.rank + 1 := by
  decide +kernel

theorem e8_card : ∀ c ∈ e8Conn, (c.map (idxNode (r := Tag.E8.rank))).toFinset.card = c.length := by
  decide +kernel

theorem e8_count_raw : ∀ c ∈ e8Conn, 2 ≤ c.length →
    kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e8APaths, sameSet c (P.map nodeIdx) = true := by
  decide +kernel

theorem e8_count : ∀ c ∈ e8Conn, 2 ≤ c.length →
    kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      c.length * (c.length + 1) → ∃ P ∈ e8APaths, sameSet c (P.map nodeIdx) = true :=
  e8_count_raw

theorem e8_paths_raw : ∀ P ∈ e8APathsRaw, P.Nodup ∧ 2 ≤ P.length ∧
    (∀ c d : Fin P.length, iform (e8ExtVec (P.get c)) (e8ExtVec (P.get d)) = chainGram c d) ∧
    ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
      (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e8EdgeIdx := by
  decide +kernel

theorem e8_paths :
    ∀ P ∈ e8APaths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length,
        iform (kacE8.extRoot (P.get c)) (kacE8.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ e8EdgeIdx := by
  rw [kacE8_extRoot]
  exact e8_paths_raw

theorem e8_edgeIdx_mem : ∀ x y : Option (Fin 8), (nodeIdx x, nodeIdx y) ∈ e8EdgeIdx →
    (x, y) ∈ e8EdgesRaw := by
  decide +kernel

section Frames

theorem e8_frames {L : Type} [Field L] : ∀ x y : Option (Fin Tag.E8.rank),
    (nodeIdx x, nodeIdx y) ∈ e8EdgeIdx →
      ∃ (ρ : SL(3, L) →* ModGL Tag.E8 L) (σ : Fin 3 → Fin 3 → Fin Tag.E8.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = kacE8.extRoot x ∧
          σ 1 2 = kacE8.extRoot y := by
  intro x y h
  rw [kacE8_extRoot]
  exact exists_a2Frame_of_mem_e8Edges (e8_edgeIdx_mem x y h)

theorem exists_frame_of_typeA_E8_T_of_prime {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL Tag.E8 L) (σ : Fin ν → Fin ν → Fin Tag.E8.rank → ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ :=
  exists_frame_of_typeA_T_of_prime (Or.inr (Or.inr (Or.inr rfl)))
    kacE8 facts_E8 e8_tree e8_adj e8_check
    e8_lt e8_card e8_count e8_paths e8_frames S hp hpL hTp i h2 hn

end Frames

end CFSG.HardMathSupport.Timmesfeld.CrossChar
