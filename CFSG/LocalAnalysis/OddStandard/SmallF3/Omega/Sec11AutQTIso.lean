module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11AutQTCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem twoCore_iso_of_theta {G : Type} [Group G] [Finite G] (K1 K2 : Subgroup G)
    (hc : ⁅K1, K2⁆ = ⊥) (hcard : Nat.card ↥(K1 ⊔ K2) = 288) (e1 : ↥K1 ≃* SL23)
    (e2 : ↥K2 ≃* SL23) {M : Type} [Group M] (Θ : SL23 × SL23 →* M)
    (hΘ : ∀ A B : SL23, A ^ 4 = 1 → B ^ 4 = 1 →
      (Θ (A, B) = 1 ↔ (A = 1 ∧ B = 1) ∨ (A = -1 ∧ B = -1))) :
    Nonempty (↥(twoCoreIn (K1 ⊔ K2)) ≃* ↥((sl23Q8.prod sl23Q8).map Θ)) := by
  obtain ⟨Ψ, hΨ, hrange⟩ := aqt_exists_psi hc e1 e2
  have hker := aqt_ker_iff e1 e2 hcard hΨ hrange
  have hcore := aqt_twoCore_eq hrange hker
  let f : ↥(sl23Q8.prod sl23Q8) →* G := Ψ.comp (sl23Q8.prod sl23Q8).subtype
  let g : ↥(sl23Q8.prod sl23Q8) →* M := Θ.comp (sl23Q8.prod sl23Q8).subtype
  have hfg : f.ker = g.ker := by
    ext ⟨⟨A, B⟩, hq⟩
    have hA : A ^ 4 = 1 := (Subgroup.mem_prod.mp hq).1
    have hB : B ^ 4 = 1 := (Subgroup.mem_prod.mp hq).2
    show Ψ (A, B) = 1 ↔ Θ (A, B) = 1
    rw [hker, hΘ A B hA hB]
  have hfr : f.range = (sl23Q8.prod sl23Q8).map Ψ := by
    rw [show f.range = (Ψ.comp (sl23Q8.prod sl23Q8).subtype).range from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hgr : g.range = (sl23Q8.prod sl23Q8).map Θ := by
    rw [show g.range = (Θ.comp (sl23Q8.prod sl23Q8).subtype).range from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hcore).trans ((MulEquiv.subgroupCongr hfr.symm).trans
    (((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hfg).trans
        (QuotientGroup.quotientKerEquivRange g))).trans (MulEquiv.subgroupCongr hgr)))⟩

end CFSG.OddStandard.SmallF3.Omega
