module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralAutomorphismInner

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.LargeExtraspecial.RepresentationSupport

variable {G : Type} [Group G] [Finite G]

theorem sec5g_exists_mul_centralizer {Q : Subgroup G} (hQe : IsExtraspecialPGroup 2 ↥Q) {d : G}
    (hd : d ∈ normalizer (Q : Set G)) (hc : ∀ q ∈ Q, d * q * d⁻¹ * q⁻¹ ∈ centerIn Q) :
    ∃ x ∈ Q, x⁻¹ * d ∈ centralizer (Q : Set G) := by
  let α : MulAut ↥Q := Q.normalizerMonoidHom ⟨d, hd⟩
  have hα : ∀ q : ↥Q, (α q : G) = d * q * d⁻¹ := fun q => rfl
  have h1 : ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥Q α = 1 := by
    ext y
    induction y using QuotientGroup.induction_on with
    | _ q =>
      rw [ExtraspecialOddQuotientAutFaithfulness.quotientHom_mk]
      show ((α q : ↥Q) : ↥Q ⧸ Subgroup.center ↥Q) = (q : ↥Q ⧸ Subgroup.center ↥Q)
      rw [QuotientGroup.eq]
      obtain ⟨c, hcc, hceq⟩ := hc ((q : G)⁻¹) (inv_mem q.2)
      have hce : (α q)⁻¹ * q = c := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα]
        have hceq' : (c : G) = d * (q : G)⁻¹ * d⁻¹ * (q : G)⁻¹⁻¹ := hceq
        rw [hceq']
        group)
      rw [hce]
      exact hcc
  obtain ⟨x, hx⟩ := ExtraspecialTwoCentralAutomorphismInner.exists_inner hQe α h1
  refine ⟨(x : G), x.2, ?_⟩
  rw [mem_centralizer_iff]
  intro q hq
  have h2 := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : G)) hx
  have h3 : d * q * d⁻¹ = (x : G) * q * (x : G)⁻¹ := by
    simpa [hα, MulAut.conj_apply] using h2
  calc q * ((x : G)⁻¹ * d) = (x : G)⁻¹ * ((x : G) * q * (x : G)⁻¹) * d := by group
    _ = (x : G)⁻¹ * (d * q * d⁻¹) * d := by rw [h3]
    _ = (x : G)⁻¹ * d * q := by group

end CFSG.OddStandard.SmallF3.Omega
