module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Comp
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ComponentClassification.Sol78

theorem Ivk714Hyp.card_layer_eq {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) :
    ∃ o : ℕ, Odd o ∧ Nat.card ↥(layer ↥(fixedSubgroup K z)) = 2520 * o := by
  obtain ⟨φ⟩ := h
  refine ⟨Nat.card (pPrimeCore 2 ↥(layer ↥(fixedSubgroup K z))), ?_, ?_⟩
  · exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(layer ↥(fixedSubgroup K z))),
      Nat.card_congr φ.toEquiv, card_alt7]

theorem alt7_exists_noncomm_sylow :
    ∃ Q : Sylow 2 (alternatingGroup (Fin 7)), ∃ a ∈ (Q : Subgroup (alternatingGroup (Fin 7))),
      ∃ b ∈ (Q : Subgroup (alternatingGroup (Fin 7))), a * b ≠ b * a := by
  have hcard : Nat.card (closure ({dtA, dtB} : Set (alternatingGroup (Fin 7)))) = 8 :=
    le_antisymm (card_closure_pair_le_eight (by decide) (by decide) (by decide))
      le_card_closure_dtA_dtB
  have hp : IsPGroup 2 (closure ({dtA, dtB} : Set (alternatingGroup (Fin 7)))) :=
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨Q, dtA, hQ (subset_closure (by simp)), dtB, hQ (subset_closure (by simp)), fun h => ?_⟩
  have h2 : (dtA * dtB) ^ 2 = 1 := by
    have ha : dtA * dtA = 1 := by decide
    have hb : dtB * dtB = 1 := by decide
    calc (dtA * dtB) ^ 2 = dtA * dtB * (dtA * dtB) := by rw [pow_two]
      _ = dtA * (dtB * dtA) * dtB := by group
      _ = dtA * (dtA * dtB) * dtB := by rw [h]
      _ = (dtA * dtA) * (dtB * dtB) := by group
      _ = 1 := by rw [ha, hb, mul_one]
  have := orderOf_dtA_mul_dtB_sq
  rw [h2, orderOf_one] at this
  omega

theorem Ivk714Hyp.exists_nonabelian_two_subgroup {K : Type} [Group K] [Finite K] {z : MulAut K}
    (h : Ivk714Hyp K z) :
    ∃ H : Subgroup K, IsPGroup 2 ↥H ∧ ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  obtain ⟨B, -, -, ⟨hq⟩, -⟩ := h.exists_component
  let σ : ↥B →* alternatingGroup (Fin 7) := hq.toMonoidHom.comp (QuotientGroup.mk' _)
  have hσ : Function.Surjective σ := hq.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨Q, a, ha, b, hb, hab⟩ := alt7_exists_noncomm_sylow
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hσ 2 Q
  refine ⟨(P : Subgroup ↥B).map B.subtype, P.2.map B.subtype, ?_⟩
  have hPQ : (P : Subgroup ↥B).map σ = (Q : Subgroup (alternatingGroup (Fin 7))) := by
    rw [← Sylow.coe_mapSurjective hσ, hP]
  have ha' : a ∈ (P : Subgroup ↥B).map σ := by rw [hPQ]; exact ha
  have hb' : b ∈ (P : Subgroup ↥B).map σ := by rw [hPQ]; exact hb
  obtain ⟨x, hx, rfl⟩ := ha'
  obtain ⟨y, hy, rfl⟩ := hb'
  refine ⟨(x : K), ⟨x, hx, rfl⟩, (y : K), ⟨y, hy, rfl⟩, fun hxy => hab ?_⟩
  have : x * y = y * x := Subtype.ext hxy
  rw [← map_mul, ← map_mul, this]

end CFSG.GH74.GLS.IVK
