module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ6

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Count

variable {τ : Tag} {J : Set (Fin τ.rank)}

theorem mem_degSet_iff {d : ℤ} (hd : 1 ≤ d) {α : Fin τ.rank → ℤ} :
    α ∈ degSet τ J d ↔ IsRoot τ α ∧ 0 < height α ∧ d ≤ parabolicDegree τ J α :=
  ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.2⟩, fun ⟨hr, hp, hd'⟩ =>
    ⟨mem_parabolicRadicalRoots_of_degree hr hp (by omega), hd'⟩⟩

end Count

section D4

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem parabolicDegree_J013 (v : Fin Tag.D4.rank → ℤ) :
    parabolicDegree Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) v = v 2 := by
  classical
  unfold parabolicDegree
  have h : (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} := by decide
  rw [h]
  simp

theorem parabolicDegree_J2 (v : Fin Tag.D4.rank → ℤ) :
    parabolicDegree Tag.D4 ({2} : Set (Fin Tag.D4.rank)) v = v 0 + v 1 + v 3 := by
  classical
  unfold parabolicDegree
  have h : (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp
  ring

theorem degSet_J013 {d : ℤ} (hd : 1 ≤ d) :
    degSet Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) d =
      ↑((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ => 0 < height v ∧ d ≤ v 2) := by
  ext α
  rw [mem_degSet_iff hd, Finset.coe_filter, parabolicDegree_J013]
  simp [mem_rootFinset]

theorem degSet_J2 {d : ℤ} (hd : 1 ≤ d) :
    degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) d =
      ↑((rootFinset Tag.D4).filter fun v : Fin Tag.D4.rank → ℤ =>
        0 < height v ∧ d ≤ v 0 + v 1 + v 3) := by
  ext α
  rw [mem_degSet_iff hd, Finset.coe_filter, parabolicDegree_J2]
  simp [mem_rootFinset]

theorem ncard_degSet_J013_one :
    (degSet Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 1).ncard = 9 := by
  rw [degSet_J013 le_rfl, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_degSet_J013_two :
    (degSet Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 2).ncard = 1 := by
  rw [degSet_J013 (by norm_num), Set.ncard_coe_finset]
  decide +kernel

theorem degSet_J013_three {d : ℤ} (hd : 3 ≤ d) :
    degSet Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) d = ∅ := by
  rw [degSet_J013 (by omega)]
  refine Finset.coe_eq_empty.2 (Finset.filter_eq_empty_iff.2 fun v hv => ?_)
  have h : ∀ v ∈ rootFinset Tag.D4, ¬(0 < height v ∧ 3 ≤ v 2) := by decide +kernel
  intro h'
  exact h v hv ⟨h'.1, by omega⟩

theorem ncard_degSet_J2_one :
    (degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 1).ncard = 11 := by
  rw [degSet_J2 le_rfl, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_degSet_J2_two :
    (degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 2).ncard = 5 := by
  rw [degSet_J2 (by norm_num), Set.ncard_coe_finset]
  decide +kernel

theorem ncard_degSet_J2_three :
    (degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 3).ncard = 2 := by
  rw [degSet_J2 (by norm_num), Set.ncard_coe_finset]
  decide +kernel

theorem degSet_J2_four {d : ℤ} (hd : 4 ≤ d) :
    degSet Tag.D4 ({2} : Set (Fin Tag.D4.rank)) d = ∅ := by
  rw [degSet_J2 (by omega)]
  refine Finset.coe_eq_empty.2 (Finset.filter_eq_empty_iff.2 fun v hv => ?_)
  have h : ∀ v ∈ rootFinset Tag.D4, ¬(0 < height v ∧ 4 ≤ v 0 + v 1 + v 3) := by decide +kernel
  intro h'
  exact h v hv ⟨h'.1, by omega⟩

end D4

section Layers

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem degSeries_J013_three {d : ℤ} (hd : 3 ≤ d) :
    degSeries Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) d = ⊥ := by
  unfold degSeries rootSpan
  rw [degSet_J013_three hd]
  simp

theorem degSeries_J2_four {d : ℤ} (hd : 4 ≤ d) :
    degSeries Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) d = ⊥ := by
  unfold degSeries rootSpan
  rw [degSet_J2_four hd]
  simp

theorem ncard_layer_J013_one :
    (degLayerRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 1).ncard = 8 := by
  have h := ncard_degSet_eq (τ := Tag.D4) (J := ({0, 1, 3} : Set (Fin Tag.D4.rank))) 1
  rw [ncard_degSet_J013_one] at h
  have h2 := ncard_degSet_J013_two
  norm_num at h
  omega

theorem ncard_layer_J013_two :
    (degLayerRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) 2).ncard = 1 := by
  have h := ncard_degSet_eq (τ := Tag.D4) (J := ({0, 1, 3} : Set (Fin Tag.D4.rank))) 2
  rw [ncard_degSet_J013_two, degSet_J013_three (by norm_num), Set.ncard_empty] at h
  norm_num at h
  omega

theorem ncard_layer_J2_one :
    (degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 1).ncard = 6 := by
  have h := ncard_degSet_eq (τ := Tag.D4) (J := ({2} : Set (Fin Tag.D4.rank))) 1
  rw [ncard_degSet_J2_one] at h
  have h2 := ncard_degSet_J2_two
  norm_num at h
  omega

theorem ncard_layer_J2_three :
    (degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 3).ncard = 2 := by
  have h := ncard_degSet_eq (τ := Tag.D4) (J := ({2} : Set (Fin Tag.D4.rank))) 3
  rw [ncard_degSet_J2_three, degSet_J2_four (by norm_num), Set.ncard_empty] at h
  norm_num at h
  omega

end Layers

end CFSG.LocalAnalysis.GLTheoremA
