module

public import CFSG.LargeExtraspecial.S7Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S7

namespace CaseI25Fusion

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem conj_mem_Lbar_of_mem_normalizer {x : S.O} (hx : x ∈ S.Mbar)
    (hxN : x * t * x⁻¹ ∈ normalizer (S.Lbar g : Set S.O)) : x * t * x⁻¹ ∈ S.Lbar g := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hx
  have hfix := fix_of_mem_normalizer H hxN
  have htw : (t : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) =
      (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
    have h1 := congrArg (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) hfix
    rwa [S4.coe_mul_apply, S4.coe_mul_apply, S4.inv_apply_apply_O] at h1
  have hw : S.width = 6 := (width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ).trans h6
  have hdim : finrank (ZMod 2) (S4.Wt S g t) = 6 := by
    have h1 := S4.finrank_Wt (S := S) (g := g) (t := t)
    have h2 := S.finrank_Qt_eq_two_mul_width
    omega
  have hVW : S4.Vt S g t = S4.Wt S g t :=
    Submodule.eq_of_le_of_finrank_le (S4.Vt_le_Wt H ht1) (by omega)
  have hmemW : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ∈
      S4.Wt S g t := by
    rw [← (S4.commSpace_t_eq H C ht ht1 hVQ).2,
      CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace]
    exact htw
  have hmem : (((S.ρ k)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹)) ∈ S4.Vt S g t := by
    have e : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ = g * S.z * g⁻¹ := by
      simp [mul_assoc]
    rw [e, hVW]
    exact hmemW
  have key := S7.conj_mem_Lbar_of_inv_apply_mem H ht
    (S7.orbit67_of_omegaCase hCE H hNo C hΩ h6.ge) k 1 hmem
  have e2 : ((1 : S.M) : G) * g = g := by simp
  rw [e2] at key
  exact key

end CaseI25Fusion

end CFSG.GF2Type.Smith1979
