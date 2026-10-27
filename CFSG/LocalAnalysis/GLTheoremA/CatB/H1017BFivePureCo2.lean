module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2FiveRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Blueprint CFSG.RankThree.Native CFSG.Sporadic.Co2Cert Subgroup
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance


private theorem exists_line_mem_of_card {N : Subgroup (Equiv.Perm (Fin 2300))}
    (hNQ : N ≤ co2FiveQ) (hN : Nat.card N = 5 ^ 2) (r : Fin 2) :
    ∃ n ∈ N, ∃ j : Fin 31, co2FiveRecordOf j = r ∧ ∃ a : ℕ, ¬ 5 ∣ a ∧ co2FiveLine j ^ a = n := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hr : r = 0 ∨ r = 1 := by
    revert r
    decide
  rcases hr with rfl | rfl
  · exact ⟨_, CFSG.HardMathSupport.Solomon.Coordinator.Co2Spor.x0_mem_of_card_25 hNQ
      (by rw [hN]; norm_num), 0, rfl, 1, by norm_num, pow_one _⟩
  · obtain ⟨n, hn, hnx⟩ : ∃ n ∈ N, n ∉ zpowers (co2FiveLine 0) := by
      by_contra hall
      push Not at hall
      have h := card_le_of_le (show N ≤ zpowers (co2FiveLine 0) from hall)
      rw [hN, Nat.card_zpowers, CFSG.RankThree.Native.orderOf_co2FiveLine] at h
      norm_num at h
    have hn1 : n ≠ 1 := fun h => hnx (h ▸ one_mem _)
    have ho : orderOf n = 5 := orderOf_eq_prime (co2FiveQ_pow_five (hNQ hn)) hn1
    have hmem : zpowers n ∈
        {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} :=
      ⟨zpowers_le.2 (hNQ hn), by rw [Nat.card_zpowers, ho]⟩
    rw [co2FiveQ_lines.1] at hmem
    obtain ⟨j, hj⟩ := hmem
    have hj' : zpowers (co2FiveLine j) = zpowers n := hj
    have hnj : n ∈ zpowers (co2FiveLine j) := by
      rw [hj']
      exact mem_zpowers n
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      have hj00 : j = 0 := Fin.ext h0
      rw [hj00] at hnj
      exact hnx hnj
    obtain ⟨a, ha⟩ : ∃ a : ℕ, co2FiveLine j ^ a = n := (mem_powers_iff_mem_zpowers).2 hnj
    refine ⟨n, hn, j, by simp [co2FiveRecordOf, hj0], a, ?_, ha⟩
    rintro ⟨m, rfl⟩
    rw [pow_mul, ← CFSG.RankThree.Native.orderOf_co2FiveLine j, pow_orderOf_eq_one,
      one_pow] at ha
    exact hn1 ha.symm

theorem exists_lineType_mem_of_card_co2 {M : Subgroup NativeSporadic.Co2}
    (hM : Nat.card M = 5 ^ 2) (r : Fin 2) :
    ∃ σ ∈ M, ∃ (a : ℕ) (k : NativeSporadic.Co2), ¬ 5 ∣ a ∧
      k * σ * k⁻¹ = co2LineElt (co2FiveRepLine r) ^ a := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let ψ : NativeSporadic.Co2 →* Equiv.Perm (Fin 2300) := co2P.subtype.comp co2PermHom'
  have hinj : Function.Injective co2PermHom' := co2PermEquiv.injective
  have hψ : Function.Injective ψ := co2P.subtype_injective.comp hinj
  have hM₁P : M.map ψ ≤ co2P := by
    rintro _ ⟨σ, -, rfl⟩
    exact (co2PermHom' σ).2
  have hM₁c : Nat.card (M.map ψ) = 5 ^ 2 := by rw [card_map_of_injective hψ, hM]
  obtain ⟨g, hgP, hg⟩ := CFSG.HardMathSupport.Solomon.Coordinator.Co2Spor.exists_conj_le_of_full
    co2FiveQ_le_P
    (by rw [card_co2FiveQ, CFSG.RankThree.Native.factorization_card_co2P_five]; norm_num)
    hM₁P (IsPGroup.of_card hM₁c)
  have hNQ : (M.map ψ).map (MulAut.conj g⁻¹).toMonoidHom ≤ co2FiveQ := by
    rintro _ ⟨m, hm, rfl⟩
    have := hg m hm
    simpa [MulAut.conj_apply] using this
  have hNc : Nat.card ((M.map ψ).map (MulAut.conj g⁻¹).toMonoidHom) = 5 ^ 2 := by
    rw [card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective,
      hM₁c]
  obtain ⟨n, hn, j, hj, a, ha, hna⟩ := exists_line_mem_of_card hNQ hNc r
  obtain ⟨m, hm, rfl⟩ := hn
  obtain ⟨σ, hσ, rfl⟩ := hm
  obtain ⟨hhP, hconj⟩ := co2FiveTransporter_spec j
  rw [hj] at hconj
  set h := co2FiveTransporter j with hhdef
  have hx : h⁻¹ * co2FiveLine j * h = co2FiveLine (co2FiveRepLine r) := by
    rw [← hconj]
    group
  have e1 : g⁻¹ * ψ σ * g = co2FiveLine j ^ a := by
    rw [hna]
    simp [MulAut.conj_apply]
  have hkey : (g * h)⁻¹ * ψ σ * (g * h) = co2FiveLine (co2FiveRepLine r) ^ a := by
    have e2 := conj_pow (a := h⁻¹) (b := co2FiveLine j) (i := a)
    rw [inv_inv] at e2
    calc (g * h)⁻¹ * ψ σ * (g * h) = h⁻¹ * (g⁻¹ * ψ σ * g) * h := by group
      _ = h⁻¹ * co2FiveLine j ^ a * h := by rw [e1]
      _ = (h⁻¹ * co2FiveLine j * h) ^ a := e2.symm
      _ = co2FiveLine (co2FiveRepLine r) ^ a := by rw [hx]
  have hcP : g * h ∈ co2P := co2P.mul_mem hgP hhP
  have hkeyP : (⟨g * h, hcP⟩ : ↥co2P)⁻¹ * co2PermHom' σ * ⟨g * h, hcP⟩ =
      (⟨co2FiveLine (co2FiveRepLine r), co2FiveLine_mem _⟩ : ↥co2P) ^ a := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hkey
  refine ⟨σ, hσ, a, (co2PermEquiv.symm ⟨g * h, hcP⟩)⁻¹, ha, ?_⟩
  have e := congrArg co2PermEquiv.symm hkeyP
  rw [map_mul, map_mul, map_inv, map_pow, co2PermHom'_apply, MulEquiv.symm_apply_apply] at e
  rw [inv_inv, co2LineElt, ← e]

end CFSG.LocalAnalysis.GLTheoremA.H1017
