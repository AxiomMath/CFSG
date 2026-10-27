module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts
import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.AGLEmbedding (exists_mul_eq_of_kOutTwoGroup mem_inf_of_pow_eq_one_of_decomp)

theorem normalizer_of_exponent_three_onan_type {Y : Type} [Group Y] [Finite Y] (R : Sylow 3 Y)
    (K : Subgroup Y) [K.Normal] {z : Y} (hout : CFSG.AGLEmbedding.KOutTwoGroup K)
    (hzK : z ∈ K) (hzR : z ∈ (R : Subgroup Y))
    (hexp : ∀ t ∈ (R : Subgroup Y) ⊓ K, t ^ 3 = 1)
    (hcomm : ∀ x ∈ (R : Subgroup Y) ⊓ K, ∀ y ∈ (R : Subgroup Y) ⊓ K,
      x * y * x⁻¹ * y⁻¹ ∈ zpowers z)
    (hΩ : ∀ c ∈ (R : Subgroup Y) ⊓ centralizer (K : Set Y), orderOf c = 3 → c ∈ zpowers z)
    {D : Subgroup Y} (hDR : D ≤ R) (hD3 : ∀ x ∈ D, x ^ 3 = 1) (hzD : z ∈ D) :
    (R : Subgroup Y) ≤ normalizer (D : Set Y) := by
  have hdec : ∀ r ∈ (R : Subgroup Y), ∃ t ∈ (R : Subgroup Y) ⊓ K,
      ∃ c ∈ (R : Subgroup Y) ⊓ centralizer (K : Set Y), t * c = r := fun r hr =>
    exists_mul_eq_of_kOutTwoGroup Nat.prime_three (by norm_num) R hout hr
  have hDS : ∀ x ∈ D, x ∈ (R : Subgroup Y) ⊓ K := fun x hx =>
    mem_inf_of_pow_eq_one_of_decomp Nat.prime_three hzR hzK hΩ hdec hexp (hDR hx) (hD3 x hx)
  have hzDle : zpowers z ≤ D := zpowers_le.mpr hzD
  intro r hr
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec r hr
  have hxS := hDS x hx
  have hcx : c * x = x * c := (mem_centralizer_iff.mp hc.2 x hxS.2).symm
  have hcxc : c * x * c⁻¹ = x := by rw [hcx]; group
  have h1 : t * c * x * (t * c)⁻¹ = (t * x * t⁻¹ * x⁻¹) * x :=
    calc t * c * x * (t * c)⁻¹ = t * (c * x * c⁻¹) * t⁻¹ := by group
      _ = t * x * t⁻¹ := by rw [hcxc]
      _ = (t * x * t⁻¹ * x⁻¹) * x := by group
  rw [h1]
  exact D.mul_mem (hzDle (hcomm t ht x hxS)) hx

end CFSG.LocalAnalysis.RankThreeTheoremC
