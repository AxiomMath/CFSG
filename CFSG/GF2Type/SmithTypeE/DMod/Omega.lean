module

public import CFSG.GF2Type.SmithTypeE.DMod.Siegel
public import CFSG.LargeExtraspecial.S45QOmegaMinus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.ClassicalGroups.Orthogonal (eichler)

theorem finrank_V12 : Module.finrank (ZMod 2) V12 = 12 := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

theorem isometries_eq_orthogonalGroup :
    CFSG.Open.timmesfeldIsometries q12 = TauCeti.QuadraticMap.orthogonalGroup Q12 := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  rfl

theorem omegaPlus_eq_omegaGroup :
    CFSG.Open.timmesfeldOmegaPlus 6 = omegaGroup Q12 Q12_polarBilin_nondegenerate := by
  have h := CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup
    Q12_polarBilin_nondegenerate (by rw [finrank_V12]; norm_num)
  rw [← h, ← isometries_eq_orthogonalGroup]
  rfl

theorem isSimpleGroup_omegaPlus : IsSimpleGroup (CFSG.Open.timmesfeldOmegaPlus 6) := by
  rw [omegaPlus_eq_omegaGroup]
  exact S45Q.isSimpleGroup_omegaGroup_of_six_le Q12_polarBilin_nondegenerate
    (by rw [finrank_V12]; norm_num)

theorem eichler_eq_siegelEquiv {u w : V12} (h : TsPair u w) :
    eichler Q12 u w = siegelEquiv u w := by
  obtain ⟨hu, hw, huw⟩ := h
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply_zmod2 (q := Q12) (by rw [Q12_apply]; exact hu)
    (by rw [polar_Q12]; exact huw) x, siegelEquiv_apply ⟨hu, hw, huw⟩, polar_Q12, polar_Q12,
    Q12_apply, hw, zero_mul, add_zero]
  abel

theorem siegelEquiv_mem_omega {u w : V12} (h : TsPair u w) (hu : u ≠ 0) :
    siegelEquiv u w ∈ CFSG.Open.timmesfeldOmegaPlus 6 := by
  rw [omegaPlus_eq_omegaGroup, ← eichler_eq_siegelEquiv h]
  exact S4.pointRadical_le_omegaGroup Q12_polarBilin_nondegenerate hu (by rw [Q12_apply]; exact h.1)
    (eichler_mem_pointRadical (by rw [Q12_apply]; exact h.1) (by rw [polar_Q12]; exact h.2.2))

end CFSG.GF2Type.SmithTypeE.DMod
