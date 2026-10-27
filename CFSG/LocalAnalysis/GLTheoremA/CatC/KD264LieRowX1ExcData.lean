module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcGood

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice (toVec isRoot_toVec isRoot_iff_exists_mem)

section Bridge

variable {τ : Tag}

theorem hord_of_checks (u : Fin τ.rank → ZMod 3) (ordL : List (List ℤ))
    (hsound : ∀ l ∈ ordL, l ∈ τ.artifactRoots ∧ dotT u (toVec τ.rank l) = 0)
    (hcomplete : ∀ l ∈ τ.artifactRoots, dotT u (toVec τ.rank l) = 0 → l ∈ ordL) :
    ∀ γ, (IsRoot τ γ ∧ dotT u γ = 0) ↔ γ ∈ ordL.map (toVec τ.rank) := by
  intro γ
  constructor
  · rintro ⟨hγ, hd⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hγ
    exact List.mem_map.2 ⟨l, hcomplete l hl hd, rfl⟩
  · intro h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2⟩ := hsound l hl
    exact ⟨isRoot_toVec h1, h2⟩

end Bridge

section E7

@[expose] def e7U : Fin 7 → ZMod 3 := ![0, 0, 0, 0, 1, 0, 1]
@[expose] def e7V : Fin 7 → ZMod 3 := ![0, 0, 0, 1, 0, 1, 0]
def e7Ord : List (List ℤ) :=
  [[-1, -2, -2, -3, -2, -2, -1],
   [-1, -2, -2, -3, -2, -1, -1],
   [-1, -1, -2, -3, -2, -2, -1],
   [-1, -1, -2, -2, -2, -2, -1],
   [-1, -1, -1, -2, -2, -2, -1],
   [-1, -1, -1, -1, 0, 0, 0],
   [0, -1, -1, -2, -2, -2, -1],
   [0, -1, -1, -1, 0, 0, 0],
   [0, -1, 0, -1, 0, 0, 0],
   [0, -1, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 1, 0, 1, 0, 0, 0],
   [0, 1, 1, 1, 0, 0, 0],
   [0, 1, 1, 2, 2, 2, 1],
   [1, 1, 1, 1, 0, 0, 0],
   [1, 1, 1, 2, 2, 2, 1],
   [1, 1, 2, 2, 2, 2, 1],
   [1, 1, 2, 3, 2, 2, 1],
   [1, 2, 2, 3, 2, 1, 1],
   [1, 2, 2, 3, 2, 2, 1],
   [-1, -1, -2, -3, -2, -1, -1],
   [-1, -1, -2, -2, -2, -1, -1],
   [-1, -1, -1, -2, -2, -1, -1],
   [0, -1, -1, -2, -2, -1, -1],
   [0, 1, 1, 2, 2, 1, 1],
   [1, 1, 1, 2, 2, 1, 1],
   [1, 1, 2, 2, 2, 1, 1],
   [1, 1, 2, 3, 2, 1, 1],
   [-1, 0, -1, -1, 0, 0, 0],
   [0, 0, -1, -1, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0],
   [1, 0, 1, 1, 0, 0, 0],
   [-1, 0, -1, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0],
   [-1, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0]]
def e7OrdC : List (List ℤ) :=
  [[-1, -1, -2, -2, -2, -1, -1],
   [1, 1, 2, 2, 2, 1, 1],
   [1, 1, 1, 2, 2, 1, 1],
   [1, 0, 1, 0, 0, 0, 0],
   [0, 1, 1, 2, 2, 1, 1],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0],
   [0, -1, -1, -2, -2, -1, -1],
   [-1, 0, -1, 0, 0, 0, 0],
   [-1, -1, -1, -2, -2, -1, -1],
   [1, 0, 0, 0, 0, 0, 0],
   [-1, 0, 0, 0, 0, 0, 0]]
def e7B : List (List ℤ) :=
  [[-1, -2, -2, -3, -2, -2, -1],
   [-1, -2, -2, -3, -2, -1, -1],
   [-1, -1, -2, -3, -2, -2, -1],
   [-1, -1, -2, -2, -2, -2, -1],
   [-1, -1, -1, -2, -2, -2, -1],
   [-1, -1, -1, -1, 0, 0, 0]]
def e7P : List (List ℤ) :=
  [[5, -5, 0, 0, 4, -5, 2],
   [0, 0, 0, 0, -4, 5, -2],
   [0, 5, 0, -5, 2, 0, 1],
   [0, 0, -5, 5, -2, 0, -1],
   [-5, 0, 5, 0, -2, 0, -1],
   [-5, 0, 0, 0, 2, 0, 1]]
def e7N : ℤ := 5
def e7Rel : List ℤ := [0, 0, 0, 0, -1, 0, 2]


theorem e7_sound : ∀ l ∈ e7Ord, l ∈ Tag.E7.artifactRoots ∧
    dotT e7U (toVec Tag.E7.rank l) = 0 := by
  decide +kernel

theorem e7_complete : ∀ l ∈ Tag.E7.artifactRoots, dotT e7U (toVec Tag.E7.rank l) = 0 →
    l ∈ e7Ord := by
  decide +kernel

theorem e7_ordconn : ∀ j : ℕ, j < (e7Ord.map (toVec Tag.E7.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e7Ord.map (toVec Tag.E7.rank)).getD i default)
      ((e7Ord.map (toVec Tag.E7.rank)).getD j default) ≠ 0 := by
  decide +kernel


theorem e7_nodup : (e7Ord.map (toVec Tag.E7.rank)).Nodup := by decide +kernel

theorem e7_nodupC : (e7OrdC.map (toVec Tag.E7.rank)).Nodup := by decide +kernel

theorem e7_length : (e7Ord.map (toVec Tag.E7.rank)).length = 6 * (6 + 1) := by decide +kernel

theorem e7_lengthC : (e7OrdC.map (toVec Tag.E7.rank)).length = 12 := by decide +kernel

theorem e7_Csub : ∀ γ ∈ e7OrdC.map (toVec Tag.E7.rank),
    γ ∈ e7Ord.map (toVec Tag.E7.rank) ∧ dotT e7V γ = 0 := by
  decide +kernel

theorem e7_Cconn : ∀ j : ℕ, j < (e7OrdC.map (toVec Tag.E7.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e7OrdC.map (toVec Tag.E7.rank)).getD i default)
      ((e7OrdC.map (toVec Tag.E7.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e7_num : ∀ m : ℕ, 12 ≤ m * (m - 1) → 4 ≤ m ∧ 6 + 1 < 2 * m := by
  intro m h
  by_cases hm : 4 ≤ m
  · exact ⟨hm, by omega⟩
  · exfalso
    interval_cases m <;> omega

theorem e7_rank : compRank {γ | γ ∈ e7Ord.map (toVec Tag.E7.rank)} = 6 := by
  have hB : ∀ j : Fin 6, toVec Tag.E7.rank (e7B.getD j []) ∈ e7Ord.map (toVec Tag.E7.rank) := by
    decide +kernel
  have hP : ∀ i j : Fin 6, ∑ l, toVec Tag.E7.rank (e7P.getD i []) l *
      toVec Tag.E7.rank (e7B.getD j []) l = if i = j then e7N else 0 := by
    decide +kernel
  have hrel : ∀ l ∈ e7Ord, ∑ i, toVec Tag.E7.rank e7Rel i * toVec Tag.E7.rank l i = 0 := by
    decide +kernel
  have h1 : 6 ≤ compRank {γ | γ ∈ e7Ord.map (toVec Tag.E7.rank)} :=
    le_compRank_of_cert (k := 6) (fun j => toVec Tag.E7.rank (e7B.getD j []))
      (fun j => toVec Tag.E7.rank (e7P.getD j [])) e7N (by decide) hB hP
  have h2 : compRank {γ | γ ∈ e7Ord.map (toVec Tag.E7.rank)} + 1 ≤ Tag.E7.rank :=
    compRank_succ_le_of_relation (toVec Tag.E7.rank e7Rel) (by decide +kernel) (by
      intro γ hγ
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
      exact hrel l hl)
  have h3 : Tag.E7.rank = 7 := rfl
  omega

end E7

section E7Good


theorem e7_good_pair {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E7 L 5)
    (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot Tag.E7 γ → S.ρ γ = -γ)
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (hTor : ∀ a : Fin Tag.E7.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      rootDiagUnit Tag.E7 a ∈ S.D.torus) :
    ∃ J : Subgroup (ModGL Tag.E7 L),
      CFSG.Open.IsSubnormal J (S.Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E7 (thetaTupleG Tag.E7 ζ e7U)} :
          Set (ModGL Tag.E7 L)) ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E7 (thetaTupleG Tag.E7 ζ e7V)} :
          Set (ModGL Tag.E7 L))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
  by
  have h1 := hord_of_checks (τ := Tag.E7) e7U e7Ord e7_sound e7_complete
  have h2 : (e7OrdC.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  refine exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U e7V
    (e7Ord.map (toVec Tag.E7.rank)) (e7OrdC.map (toVec Tag.E7.rank)) 6 12
    h1 e7_ordconn e7_nodup e7_length (by norm_num) e7_rank h2 e7_Csub e7_Cconn e7_nodupC
    e7_lengthC e7_num

end E7Good



section E8

@[expose] def e8U : Fin 8 → ZMod 3 := ![0, 1, 0, 0, 0, 0, 0, 0]
@[expose] def e8V : Fin 8 → ZMod 3 := ![0, 0, 0, 0, 0, 1, 0, 1]
def e8Ord : List (List ℤ) :=
  [[-2, -3, -4, -6, -5, -4, -3, -2],
   [-2, -3, -4, -6, -5, -4, -3, -1],
   [-2, -3, -4, -6, -5, -4, -2, -1],
   [-2, -3, -4, -6, -5, -3, -2, -1],
   [-2, -3, -4, -6, -4, -3, -2, -1],
   [-2, -3, -4, -5, -4, -3, -2, -1],
   [-2, -3, -3, -5, -4, -3, -2, -1],
   [-1, -3, -3, -5, -4, -3, -2, -1],
   [-1, 0, -1, -1, -1, -1, -1, -1],
   [0, 0, -1, -1, -1, -1, -1, -1],
   [0, 0, 0, -1, -1, -1, -1, -1],
   [0, 0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 1, 1, 1, 1, 1],
   [0, 0, 1, 1, 1, 1, 1, 1],
   [1, 0, 1, 1, 1, 1, 1, 1],
   [1, 3, 3, 5, 4, 3, 2, 1],
   [2, 3, 3, 5, 4, 3, 2, 1],
   [2, 3, 4, 5, 4, 3, 2, 1],
   [2, 3, 4, 6, 4, 3, 2, 1],
   [2, 3, 4, 6, 5, 3, 2, 1],
   [2, 3, 4, 6, 5, 4, 2, 1],
   [2, 3, 4, 6, 5, 4, 3, 1],
   [2, 3, 4, 6, 5, 4, 3, 2],
   [-1, 0, -1, -1, -1, -1, -1, 0],
   [0, 0, -1, -1, -1, -1, -1, 0],
   [0, 0, 0, -1, -1, -1, -1, 0],
   [0, 0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 1, 0],
   [0, 0, 1, 1, 1, 1, 1, 0],
   [1, 0, 1, 1, 1, 1, 1, 0],
   [-1, 0, -1, -1, -1, -1, 0, 0],
   [0, 0, -1, -1, -1, -1, 0, 0],
   [0, 0, 0, -1, -1, -1, 0, 0],
   [0, 0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 1, 1, 1, 0, 0],
   [0, 0, 1, 1, 1, 1, 0, 0],
   [1, 0, 1, 1, 1, 1, 0, 0],
   [-1, 0, -1, -1, -1, 0, 0, 0],
   [0, 0, -1, -1, -1, 0, 0, 0],
   [0, 0, 0, -1, -1, 0, 0, 0],
   [0, 0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 0, 0],
   [1, 0, 1, 1, 1, 0, 0, 0],
   [-1, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0, 0],
   [1, 0, 1, 1, 0, 0, 0, 0],
   [-1, 0, -1, 0, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0, 0],
   [-1, 0, 0, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0]]
def e8OrdC : List (List ℤ) :=
  [[-1, 0, -1, -1, -1, 0, 0, 0],
   [1, 0, 1, 1, 1, 0, 0, 0],
   [1, 0, 1, 1, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, -1, -1, 0, 0, 0],
   [0, 0, -1, -1, -1, 0, 0, 0],
   [-1, 0, 0, 0, 0, 0, 0, 0],
   [-1, 0, -1, 0, 0, 0, 0, 0],
   [-1, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0, 0],
   [0, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0, 0]]
def e8B : List (List ℤ) :=
  [[-2, -3, -4, -6, -5, -4, -3, -2],
   [-2, -3, -4, -6, -5, -4, -3, -1],
   [-2, -3, -4, -6, -5, -4, -2, -1],
   [-2, -3, -4, -6, -5, -3, -2, -1],
   [-2, -3, -4, -6, -4, -3, -2, -1],
   [-2, -3, -4, -5, -4, -3, -2, -1],
   [-2, -3, -3, -5, -4, -3, -2, -1],
   [-1, -3, -3, -5, -4, -3, -2, -1]]
def e8P : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, 0, -3],
   [0, 1, 0, 0, 0, 0, -3, 3],
   [0, 1, 0, 0, 0, -3, 3, 0],
   [0, 1, 0, 0, -3, 3, 0, 0],
   [0, 1, 0, -3, 3, 0, 0, 0],
   [0, -2, -3, 3, 0, 0, 0, 0],
   [-3, -2, 3, 0, 0, 0, 0, 0],
   [3, -2, 0, 0, 0, 0, 0, 0]]
def e8N : ℤ := 3


theorem e8_sound : ∀ l ∈ e8Ord, l ∈ Tag.E8.artifactRoots ∧
    dotT e8U (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8_complete : ∀ l ∈ Tag.E8.artifactRoots, dotT e8U (toVec Tag.E8.rank l) = 0 →
    l ∈ e8Ord := by
  decide +kernel

theorem e8_ordconn : ∀ j : ℕ, j < (e8Ord.map (toVec Tag.E8.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e8Ord.map (toVec Tag.E8.rank)).getD i default)
      ((e8Ord.map (toVec Tag.E8.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e8_nodup : (e8Ord.map (toVec Tag.E8.rank)).Nodup := by decide +kernel

theorem e8_nodupC : (e8OrdC.map (toVec Tag.E8.rank)).Nodup := by decide +kernel

theorem e8_length : (e8Ord.map (toVec Tag.E8.rank)).length = 8 * (8 + 1) := by decide +kernel

theorem e8_lengthC : (e8OrdC.map (toVec Tag.E8.rank)).length = 20 := by decide +kernel

theorem e8_Csub : ∀ γ ∈ e8OrdC.map (toVec Tag.E8.rank),
    γ ∈ e8Ord.map (toVec Tag.E8.rank) ∧ dotT e8V γ = 0 := by
  decide +kernel

theorem e8_Cconn : ∀ j : ℕ, j < (e8OrdC.map (toVec Tag.E8.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e8OrdC.map (toVec Tag.E8.rank)).getD i default)
      ((e8OrdC.map (toVec Tag.E8.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e8_num : ∀ m : ℕ, 20 ≤ m * (m - 1) → 4 ≤ m ∧ 8 + 1 < 2 * m := by
  intro m h
  by_cases hm : 5 ≤ m
  · exact ⟨by omega, by omega⟩
  · exfalso
    interval_cases m <;> omega

theorem e8_rank : compRank {γ | γ ∈ e8Ord.map (toVec Tag.E8.rank)} = 8 := by
  have hB : ∀ j : Fin 8, toVec Tag.E8.rank (e8B.getD j []) ∈ e8Ord.map (toVec Tag.E8.rank) := by
    decide +kernel
  have hP : ∀ i j : Fin 8, ∑ l, toVec Tag.E8.rank (e8P.getD i []) l *
      toVec Tag.E8.rank (e8B.getD j []) l = if i = j then e8N else 0 := by
    decide +kernel
  have h1 : 8 ≤ compRank {γ | γ ∈ e8Ord.map (toVec Tag.E8.rank)} :=
    le_compRank_of_cert (k := 8) (fun j => toVec Tag.E8.rank (e8B.getD j []))
      (fun j => toVec Tag.E8.rank (e8P.getD j [])) e8N (by decide) hB hP
  have h2 := compRank_le_rank (τ := Tag.E8) {γ | γ ∈ e8Ord.map (toVec Tag.E8.rank)}
  have h3 : Tag.E8.rank = 8 := rfl
  omega

end E8

section E8Good


theorem e8_good_pair {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.E8 L 5)
    (hq2 : S.D.q = 2) (hAlg : S.IsAlgebraic) (hρ : ∀ γ, IsRoot Tag.E8 γ → S.ρ γ = -γ)
    {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3)
    (hTor : ∀ a : Fin Tag.E8.rank → Lˣ, (∀ i, a i ^ 3 = 1) →
      rootDiagUnit Tag.E8 a ∈ S.D.torus) :
    ∃ J : Subgroup (ModGL Tag.E8 L),
      CFSG.Open.IsSubnormal J (S.Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E8 (thetaTupleG Tag.E8 ζ e8U)} :
          Set (ModGL Tag.E8 L)) ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E8 (thetaTupleG Tag.E8 ζ e8V)} :
          Set (ModGL Tag.E8 L))) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  have h1 := hord_of_checks (τ := Tag.E8) e8U e8Ord e8_sound e8_complete
  have h2 : (e8OrdC.map (toVec Tag.E8.rank)) ≠ [] := by decide +kernel
  refine exc_component_of_data (Or.inr rfl) S hq2 hAlg hρ hζ hζ' hTor e8U e8V
    (e8Ord.map (toVec Tag.E8.rank)) (e8OrdC.map (toVec Tag.E8.rank)) 8 20
    h1 e8_ordconn e8_nodup e8_length (by norm_num) e8_rank h2 e8_Csub e8_Cconn e8_nodupC
    e8_lengthC e8_num

end E8Good

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
