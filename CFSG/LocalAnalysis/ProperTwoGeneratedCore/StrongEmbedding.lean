module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionFusion
public import CFSG.Foundations.Basic
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem involution_transporter_mem_of_centralizer_closure
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (hcentralizers : ∀ t ∈ H, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2)
    (g : G) (hgH : g⁻¹ * t * g ∈ H) : g ∈ H := by
  obtain ⟨h, hhH, hh⟩ := two_generated_core_controls_involution_fusion S H hSH hcore t htH ht g hgH
  have hdiscrepancy : g * h⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have heq := congrArg (fun x : G => g * x * h⁻¹) hh
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using heq
  have hprod := H.mul_mem (hcentralizers t htH ht hdiscrepancy) hhH
  simpa only [inv_mul_cancel_right] using hprod

theorem odd_conjugate_intersection_of_centralizer_closure
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (hcentralizers : ∀ t ∈ H, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ H)
    (g : G) (hg : g ∉ H) : Odd (Nat.card ↥(H ⊓ H.conjBy g⁻¹)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnotodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    (Nat.not_odd_iff_even.mp hnotodd).two_dvd
  have htorder : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htconj : g * (t : G) * g⁻¹ ∈ H := by
    have hpreimage := Subgroup.mem_map_equiv.mp t.property.2
    simpa only [MulAut.conj_symm_apply, inv_inv] using hpreimage
  have hginverse := involution_transporter_mem_of_centralizer_closure S H hSH hcore hcentralizers
    t t.property.1 htorder g⁻¹ (by simpa only [inv_inv] using htconj)
  exact hg (H.inv_mem_iff.mp hginverse)

theorem strongly_embedded_of_full_core_centralizer_closure
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H) (hrank : 2 ≤ twoRank G)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (hcentralizers : ∀ t ∈ H, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ H) :
    CFSG.IsStronglyEmbedded H := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGeven : 2 ∣ Nat.card G := prime_dvd_card_of_pRank_pos 2 ⊤ (by
    change 0 < twoRank G
    omega)
  have hHeven : Even (Nat.card H) := even_iff_two_dvd.mpr
    ((S.dvd_card_of_dvd_card hGeven).trans (Subgroup.card_dvd_of_le hSH))
  exact ⟨hH, hHeven,
    odd_conjugate_intersection_of_centralizer_closure S H hSH hcore hcentralizers⟩

theorem strongly_embedded_order_of_full_core_centralizer_closure
    (S : Sylow 2 G) (H : Subgroup G) (hH : H ≠ ⊤)
    (hSH : (S : Subgroup G) ≤ H) (hrank : 2 ≤ twoRank G)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (hcentralizers : ∀ t ∈ H, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ H) :
    BenderSuzuki.IsStronglyEmbeddedOrder H := by
  obtain ⟨hproper, heven, hintersection⟩ :=
    strongly_embedded_of_full_core_centralizer_closure S H hH hSH hrank hcore hcentralizers
  refine ⟨hproper, heven, ?_⟩
  intro g hg
  have hinverse := hintersection g⁻¹ (fun hginv => hg (H.inv_mem_iff.mp hginv))
  simpa only [CFSG.conjugate, inv_inv] using hinverse

end CFSG.ProperTwoGeneratedCore
