module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.ComponentClassification.PerfectAutomorphisms

theorem centerQuotientHom_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) :
    MulAut.congr (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
        (Subgroup.map_center_eq e)) (centerQuotientHom G α) =
      centerQuotientHom H (MulAut.congr e α) := by
  set Φ := QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
    (Subgroup.map_center_eq e) with hΦ
  ext q
  obtain ⟨x, rfl⟩ := Φ.surjective q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  change Φ ((onCenterQuotient α) (QuotientGroup.mk' (Subgroup.center G) g)) =
    (onCenterQuotient (MulAut.congr e α))
      (Φ (QuotientGroup.mk' (Subgroup.center G) g))
  rw [onCenterQuotient_apply_mk]
  rw [hΦ]
  conv_rhs => rw [QuotientGroup.congr_mk']
  conv_lhs => rw [QuotientGroup.congr_mk']
  rw [onCenterQuotient_apply_mk, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end CFSG.ComponentClassification.PerfectAutomorphisms

end
