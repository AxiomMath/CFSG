module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.GL52.Simple

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.GroupTheory.GL52

theorem statedSL_five_zmod_two_eq_top : StatedSL 5 (ZMod 2) = ⊤ :=
  eq_top_iff.2 fun A _ => Subgroup.subset_closure (det_G52 A)

theorem statedScalars_five_zmod_two_eq_bot : StatedScalars (Fin 5) (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [Subsingleton.elim u 1, map_one]
  exact Subgroup.one_mem _

@[expose] noncomputable def statedProjSL52Equiv : StatedProj (StatedSL 5 (ZMod 2)) ≃* G52 :=
  have hbot : (StatedScalars (Fin 5) (ZMod 2)).subgroupOf (StatedSL 5 (ZMod 2)) = ⊥ := by
    rw [statedScalars_five_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    ((MulEquiv.subgroupCongr statedSL_five_zmod_two_eq_top).trans Subgroup.topEquiv)

theorem statedClassicalModel_psl52_of_mulEquiv {G : Type} [Group G] (h : Nonempty (G ≃* G52)) :
    StatedClassicalModel G .PSL 5 2 1 := by
  obtain ⟨e⟩ := h
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance,
    by simp, ⟨e.trans statedProjSL52Equiv.symm⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

end CFSG.CGT.L5R
