module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferAutomorphism

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

theorem beta_d (j : Fin 64) : beta (d j : NativeSporadic.M12) = d (bTab j) :=
  Subtype.ext (beta_apply_of_mem (pair_mem_d j))

theorem beta_coe (s : S) : beta (s : NativeSporadic.M12) = βS s := by
  obtain ⟨j, rfl⟩ := d_surjective s
  rw [beta_d, βS_d]

theorem beta_mem_S {x : NativeSporadic.M12} (hx : x ∈ S) : beta x ∈ S := by
  have := beta_coe ⟨x, hx⟩
  simp only at this
  rw [this]
  exact (βS ⟨x, hx⟩).2

theorem beta_map_S : S.map beta.toMonoidHom = S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact beta_mem_S hx
  · intro x hx
    refine ⟨beta x, beta_mem_S hx, ?_⟩
    change beta (beta x) = x
    rw [← MulAut.mul_apply, beta_mul_self, MulAut.one_apply]

theorem beta_r (i : Fin 1485) : beta (r i) = aS i * r (σI i) :=
  Subtype.ext (beta_apply_of_mem (pair_mem_r i))

theorem tau0_snd (x : R) : ((tau0 x).snd : NativeSporadic.M12) = beta x.snd := by
  rw [proj_tau0, beta_coe]

theorem tau_snd (x : R) : ((tau x).snd : NativeSporadic.M12) = beta x.snd := by
  rw [proj_tau, beta_coe]

theorem autIndex_eq (i : Fin 1485) : isRightTransversal.autIndex beta i = σI i :=
  isRightTransversal.autIndex_eq_of_eq beta (aS i).2 (beta_r i)

theorem autCoef_eq (i : Fin 1485) : isRightTransversal.autCoef beta i = aS i :=
  Subtype.ext (isRightTransversal.coe_autCoef_eq_of_eq beta (aS i).2 (beta_r i))

theorem transportCoord_eq (i : Fin 1485) (h : S) :
    isRightTransversal.transportCoord beta tau0 i (h : NativeSporadic.M12) = coef i h := by
  rw [IsRightTransversal.transportCoord, autCoef_eq, coef_eq, act_eq, autCoef_eq]
  rfl

theorem transportSum_eq (h : S) :
    isRightTransversal.transportSum beta tau0 (h : NativeSporadic.M12) = Λ h := by
  rw [IsRightTransversal.transportSum, Λ]
  exact Finset.sum_congr rfl fun i _ => transportCoord_eq i h

theorem inducedAut_eq (s : S) : inducedAut tau0_snd s = βS s :=
  Subtype.ext ((coe_inducedAut tau0_snd s).trans (beta_coe s))

theorem restrictAut_eq_tau :
    isRightTransversal.restrictAut tau0_snd mu transfer₂_add_coboundary_mu = tau := by
  refine MulEquiv.ext fun x => ?_
  rw [IsRightTransversal.restrictAut_apply, tau_apply, inducedAut_eq, transportSum_eq, lam_eq]
  refine CocycleExtension.ext ?_ rfl
  change x.fst + Λ x.snd + mu x.snd + mu (βS x.snd) = x.fst + (Λ x.snd + mu x.snd + mu (βS x.snd))
  ring

end CFSG.ComponentClassification.M12Cover.InternalSylow
