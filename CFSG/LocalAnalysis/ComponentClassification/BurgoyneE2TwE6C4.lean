module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Rig
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6F4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


variable {K : Type} [Field K] [Finite K]

theorem burgCoreFor_twistedE6_signedGraph {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    BurgCoreFor (twE6SignAut σ) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (show 1 ≤ f * 2 by omega) (by rw [hK, ← pow_mul])
    rw [ringChar.eq K p]
    exact hp2
  have hq : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨μ, hμq⟩ := exists_unit_pow_sub_one_eq_neg_one hq hK
  have hμ : σ (μ : K) = -μ := by
    have hq1 : 1 ≤ p ^ f := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
    rw [hσ, show p ^ f = p ^ f - 1 + 1 by omega, pow_succ, ← Units.val_pow_eq_pow_val, hμq,
      Units.val_neg, Units.val_one, neg_one_mul]
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  have hJC := twE6C4Sub_le_graphFixedRootGroup hK2 σ hμ
  set J := (twE6C4Sub σ μ).subgroupOf C₀ with hJ
  have hF : ∀ g : C₀, g ∈ fixedSubgroup (twE6SignAut σ) ↔
      twistA K * (g : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) * twistA K := by
    intro g
    change twE6SignAut σ g = g ↔ _
    rw [← Subtype.coe_inj, coe_twE6SignAut hp hp2 hf hK σ hσ, mul_inv_eq_iff_eq_mul]
  have hJq : IsQuasisimple J :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm
      (isQuasisimple_twE6C4Sub hK2 σ μ)
  refine burgCoreFor_of_normal_quasisimple (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (J := J) (fun j hj => (hF j).2 (twE6C4Sub_commute σ μ hj)) (fun g hg j hj => ?_) hJq
    fun β hβ hfix => eq_one_of_odd_fix_twE6C4Sub hp hp2 hf hK σ hσ hμ hβ fun x hx => hfix x hx
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact twE6C4Sub_conj_mem hK2 σ hμ g.2 ((hF g).1 hg) hj

@[expose] def BurgoyneE2TwistedE6NonGraphInput : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 2 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), orderOf α = 2 →
          (∀ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
            ψ * α * ψ⁻¹ ≠ fieldActor (t := TwistTag.E6) σ σ) →
          (∀ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
            ψ * α * ψ⁻¹ ≠ twE6SignAut σ) →
          BurgCoreFor α ∨ BurgTorusFor α

theorem burgoyneE2TwistedE6NonF4Input_of_nonGraph (h : BurgoyneE2TwistedE6NonGraphInput) :
    BurgoyneE2TwistedE6NonF4Input := by
  intro p f hp hp2 hf K _ _ hK σ hσ α hα hF4
  by_cases hc : ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ = twE6SignAut σ
  · obtain ⟨ψ, hψ⟩ := hc
    have hc := (burgCoreFor_twistedE6_signedGraph hp hp2 hf hK σ hσ).conj ψ⁻¹
    rw [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at hc
    exact Or.inl hc
  · push Not at hc
    exact h p f hp hp2 hf K hK σ hσ α hα hF4 hc

end CFSG.ComponentClassification.Burgoyne.E2
