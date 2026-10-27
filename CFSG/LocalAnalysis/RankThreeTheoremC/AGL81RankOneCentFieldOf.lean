module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQFieldInvertThree
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQFieldInvert
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

namespace FieldOf

open Subgroup

theorem fieldInvert_of_mulAut {p : ℕ} (hp : p = 3 ∨ p = 5) {A : Type} [Group A] {K : Subgroup A}
    [K.Normal] (hC : centralizer (K : Set A) = ⊥)
    (hK : ∀ ψ : MulAut ↥K, ψ ^ p = 1 → (¬ ∃ y : ↥K, ψ = MulAut.conj y) → ∀ t : ↥K,
      orderOf t = p → ψ t = t → ∃ s : ↥K, s ^ 2 = 1 ∧ ψ s = s ∧ s * t * s⁻¹ = t⁻¹)
    {φ : A} (hφ : orderOf φ = p) (hφK : φ ∉ K) {x : A}
    (hx : x ∈ K ⊓ centralizer ({φ} : Set A)) (hxo : orderOf x = p) :
    ∃ t ∈ K ⊓ centralizer ({φ} : Set A), orderOf t = 2 ∧ t * x * t⁻¹ = x⁻¹ := by
  set ψ : MulAut ↥K := MulAut.conjNormal φ with hψdef
  have hψp : ψ ^ p = 1 := by
    rw [hψdef, ← map_pow, ← hφ, pow_orderOf_eq_one, map_one]
  have hout : ¬ ∃ y : ↥K, ψ = MulAut.conj y := by
    rintro ⟨y, hy⟩
    have hmem : (y : A)⁻¹ * φ ∈ centralizer (K : Set A) := by
      rw [mem_centralizer_iff]
      intro k hk
      have h := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : A)) hy
      simp only [hψdef, MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h
      calc k * ((y : A)⁻¹ * φ) = (y : A)⁻¹ * (y * k * (y : A)⁻¹) * φ := by group
        _ = (y : A)⁻¹ * (φ * k * φ⁻¹) * φ := by rw [h]
        _ = (y : A)⁻¹ * φ * k := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hmem
    exact hφK (hmem ▸ y.2)
  obtain ⟨hxK, hxφ⟩ := hx
  have hxφ' : x * φ = φ * x := mem_centralizer_singleton_iff.1 hxφ
  have hψx : ψ ⟨x, hxK⟩ = ⟨x, hxK⟩ := by
    apply Subtype.ext
    rw [hψdef, MulAut.conjNormal_apply]
    calc φ * x * φ⁻¹ = x * φ * φ⁻¹ := by rw [hxφ']
      _ = x := by group
  have hxo' : orderOf (⟨x, hxK⟩ : ↥K) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hxo
  obtain ⟨s, hs2, hsψ, hsx⟩ := hK ψ hψp hout ⟨x, hxK⟩ hxo' hψx
  have hsx' : (s : A) * x * (s : A)⁻¹ = x⁻¹ := by
    have h := congrArg Subtype.val hsx
    simpa using h
  have hsφ : (s : A) * φ = φ * s := by
    have h := congrArg Subtype.val hsψ
    rw [hψdef, MulAut.conjNormal_apply] at h
    calc (s : A) * φ = φ * s * φ⁻¹ * φ := by rw [h]
      _ = φ * s := by group
  refine ⟨s, ⟨s.2, mem_centralizer_singleton_iff.2 hsφ⟩, ?_, hsx'⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by simpa using congrArg Subtype.val hs2) ?_
  intro h1
  rw [h1, one_mul, inv_one, mul_one] at hsx'
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hsx']
    exact mul_inv_cancel x
  have hdvd : p ∣ 2 := hxo ▸ orderOf_dvd_of_pow_eq_one hx2
  rcases hp with rfl | rfl <;> norm_num at hdvd

end FieldOf

theorem kFactFieldAutInvert_holds :
    KFactFieldAutInvert := by
  intro p A _ _ K hKn hC hK φ hφ hφK x hx hxo
  rcases hK with ⟨rfl, d, q, hq2, hq3, hdq, he⟩ | ⟨rfl, d, hd, he⟩
  · exact FieldOf.fieldInvert_of_mulAut (Or.inl rfl) hC
      (kFactCaseTwoFieldInvertThree ↥K ⟨d, Or.inl ⟨rfl, q, hq2, hq3, hdq⟩, he⟩) hφ hφK hx hxo
  · exact FieldOf.fieldInvert_of_mulAut (Or.inr rfl) hC
      (kFactCaseTwoFieldInvert ↥K ⟨d, Or.inr ⟨rfl, hd⟩, he⟩) hφ hφK hx hxo

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
