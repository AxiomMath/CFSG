module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalOuter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

theorem l34UnbalancingUnitaryStep :
    L34UnbalancingUnitaryStep := by
  intro G _ _ a x J htri hL
  obtain ⟨-, hxo, -, hJa, hJc, hxJ, hDJ⟩ := htri
  have hJ : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
  have hset : {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} =
      {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := by
    ext y
    simp
  have hxJ' : closure {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} = J := by
    rw [hset]
    exact hxJ
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  have hDo : ∀ d ∈ ((pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype ⊓ centralizer ({a} : Set G) : Subgroup G),
      d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype :=
    fun d hd => (mem_inf.mp hd).1
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨r, hrR, hr⟩ := exists_realization q hqS hqsurj (betaHat J hxN) (fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e)
  have hr2 : r * r = 1 := by
    have hc : r * r ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun s hs => ?_, R.mul_mem hrR hrR⟩
      obtain ⟨e, rfl⟩ := hqsurj s hs
      have h1 := hr (betaHat J hxN e)
      rw [betaHat_betaHat J hxN hx2, hr e] at h1
      calc q e * (r * r) = r * (r * q e * r⁻¹) * r⁻¹ * (r * r) := by rw [← h1]
        _ = r * r * q e := by group
    rw [centralizer_S_inf_R] at hc
    exact (mem_bot.mp hc)
  by_cases hr1 : r = 1
  · exfalso
    refine false_of_closure_le hL hxJ' fun d hd j hj => ?_
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exact comm_mem_zStarIn_of_realization hqker hxN (fun e => by rw [hr, hr1]; group) hj
  have hord : orderOf (⟨r, hrR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => hr1 (congrArg Subtype.val h)
    simp only [OneMemClass.coe_one, pow_two]
    exact hr2
  have frame : ∀ {ρ₀ : Equiv.Perm (Fin 42)}, ∀ c ∈ R, r = c * ρ₀ * c⁻¹ →
      ∃ q' : Jhat J →* Equiv.Perm (Fin 42), (∀ e, q' e ∈ S) ∧ (∀ s ∈ S, ∃ e, q' e = s) ∧
        q'.ker = center (Jhat J) ∧ (∀ e ∈ q'.ker, e ^ 3 = 1 → e = 1) ∧
        ∀ e, q' (betaHat J hxN e) = ρ₀ * q' e * ρ₀⁻¹ := by
    intro ρ₀ c hcR hc
    obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem hcR)
    refine ⟨(MulAut.conj c⁻¹).toMonoidHom.comp q, hS', hsurj', by rw [hker', hqker],
      by rw [hker']; exact h3, fun e => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hr e, hc]
    group
  rcases (PSL3Four.orderOf_eq_two_iff _).1 hord with h | h | h | h
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨q', hS', hsurj', hker', h3', hβ'⟩ := frame c hcR hc
    exact (false_of_inner hJ hL hxN hx2 hS' hsurj' hker' h3' hβ' hDJ hDo).elim
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨q', hS', hsurj', hker', -, hβ'⟩ := frame c hcR hc
    exact (false_of_field_graph hL hxN hx2 hS' hsurj' hker' (Or.inl rfl) hβ' hDJ hDo).elim
  · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj h
    obtain ⟨q', hS', hsurj', hker', -, hβ'⟩ := frame c hcR hc
    exact (false_of_field_graph hL hxN hx2 hS' hsurj' hker' (Or.inr rfl) hβ' hDJ hDo).elim
  · refine ⟨hxN, hx2, fun hxW => ?_, ?_⟩
    · obtain ⟨e₀, he₀⟩ := exists_inner hxW hxN
      have hS : (q e₀)⁻¹ ∈ S := S.inv_mem (hqS e₀)
      have heq := realization_unique hqsurj hrR (S_le_R hS) hr (fun e => by
        rw [he₀, map_mul, map_mul, map_inv, inv_inv])
      exact not_mem_S_of_isConj h not_mem_S_r₄ (heq ▸ hS)
    · rw [card_set_eq_of_realization hxN hqS hqsurj hqker hr]
      congr 1
      rw [card_centralizer_S_of_isConj h]
      exact card_C₄

end CFSG.ComponentClassification.GrSLit.L34Facts
