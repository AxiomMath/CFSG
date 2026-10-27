module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.Blueprint.ChevalleyPinned

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def e6LineChar {K : Type} [Field K] (ω : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  ![1, 1, 1, ω, 1, 1]

@[expose] def e6KacNode : Fin Tag.E6.rank := ⟨3, by decide⟩

@[expose] def e6A2Roots (u v : Fin Tag.E6.rank → ℤ) : Finset (Fin Tag.E6.rank → ℤ) :=
  {u, v, u + v, -u, -v, -(u + v)}

@[expose] def e6LineRoots : Fin 3 → Finset (Fin Tag.E6.rank → ℤ)
  | 0 => e6A2Roots ![1, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 0, 0]
  | 1 => e6A2Roots ![0, 0, 0, 0, 1, 0] ![0, 0, 0, 0, 0, 1]
  | 2 => e6A2Roots ![0, 1, 0, 0, 0, 0] ![1, 1, 2, 3, 2, 1]

@[expose] def e6LineWord : List (Fin 6) := [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def e6LineWeyl : WeylGroup .E6 :=
  (e6LineWord.map (simple .E6)).prod

@[expose] def e6LineFactor
    (K : Type) [Field K] (i : Fin 3) : Subgroup (ModGL .E6 K) :=
  rootSpan .E6 K (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))

theorem e6LineRoots_subset (i : Fin 3) : e6LineRoots i ⊆ rootFinset .E6 := by
  revert i; decide +kernel

theorem isRoot_of_mem_e6LineRoots {i : Fin 3} {α : Fin Tag.E6.rank → ℤ}
    (h : α ∈ e6LineRoots i) : IsRoot .E6 α :=
  mem_rootFinset.1 (e6LineRoots_subset i h)

theorem card_e6LineRoots (i : Fin 3) : (e6LineRoots i).card = 6 := by
  revert i; decide +kernel

theorem card_biUnion_e6LineRoots : (Finset.univ.biUnion e6LineRoots).card = 18 := by
  decide +kernel

theorem neg_mem_e6LineRoots {i : Fin 3} {α : Fin Tag.E6.rank → ℤ} (h : α ∈ e6LineRoots i) :
    -α ∈ e6LineRoots i := by
  have key : ∀ i : Fin 3, ∀ α ∈ e6LineRoots i, -α ∈ e6LineRoots i := by decide +kernel
  exact key i α h

theorem three_dvd_iff_mem_e6LineRoots {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) :
    (3 : ℤ) ∣ α e6KacNode ↔ ∃ i, α ∈ e6LineRoots i := by
  have key : ∀ α ∈ rootFinset .E6, ((3 : ℤ) ∣ α e6KacNode ↔ ∃ i, α ∈ e6LineRoots i) := by
    decide +kernel
  exact key α (mem_rootFinset.2 hα)

@[expose] def e6WordAct (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  l.foldr (reflect .E6) v

theorem prod_simple_smul_eq_e6WordAct (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (l.map (simple .E6)).prod • v = e6WordAct l v := by
  induction l with
  | nil => simp [e6WordAct]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_smul, simple_smul, ih, e6WordAct,
      List.foldr_cons]

theorem e6LineWeyl_smul (v : Fin Tag.E6.rank → ℤ) : e6LineWeyl • v = e6WordAct e6LineWord v :=
  prod_simple_smul_eq_e6WordAct _ _

theorem smul_mem_e6LineRoots {i : Fin 3} {α : Fin Tag.E6.rank → ℤ} (h : α ∈ e6LineRoots i) :
    e6LineWeyl • α ∈ e6LineRoots (i + 1) := by
  have key : ∀ i : Fin 3, ∀ α ∈ e6LineRoots i, e6WordAct e6LineWord α ∈ e6LineRoots (i + 1) := by
    decide +kernel
  rw [e6LineWeyl_smul]
  exact key i α h

theorem e6LineWeyl_pow_three : e6LineWeyl ^ 3 = 1 := by
  refine ext_single fun j => ?_
  have key : ∀ j : Fin Tag.E6.rank, e6WordAct e6LineWord (e6WordAct e6LineWord
      (e6WordAct e6LineWord (Pi.single j 1))) = Pi.single j 1 := by decide +kernel
  rw [one_smul, pow_succ, pow_succ, pow_one, mul_smul, mul_smul, e6LineWeyl_smul,
    e6LineWeyl_smul, e6LineWeyl_smul]
  exact key j

theorem rootSpan_iUnion_e6LineRoots (K : Type) [Field K] :
    rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) =
      e6LineFactor K 0 ⊔ e6LineFactor K 1 ⊔ e6LineFactor K 2 := by
  have h : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) =
      ⨆ i : Fin 3, e6LineFactor K i := by
    simp only [e6LineFactor, rootSpan, iSup_iUnion]
  rw [h]
  refine le_antisymm (iSup_le fun i => ?_)
    (sup_le (sup_le (le_iSup _ 0) (le_iSup _ 1)) (le_iSup _ 2))
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem rootSubgroup_le_e6LineFactor (K : Type) [Field K] {i : Fin 3}
    {α : Fin Tag.E6.rank → ℤ} (h : α ∈ e6LineRoots i) :
    rootSubgroup .E6 K α ≤ e6LineFactor K i :=
  le_iSup₂_of_le α (Finset.mem_coe.2 h) le_rfl

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
