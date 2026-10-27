module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row

open CFSG Subgroup

variable {Q : Type*} [Group Q]

theorem pPrimeCore_eq_bot_of_quasisimple [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 2 (center Q)) {x : Q} (hx : orderOf x = 2) : pPrimeCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine pPrimeCore_eq_bot_iff.2 fun K hK hc => ?_
  rcases LocalCores.quasisimple_normal_subgroups hQ hK with h | h
  · exfalso
    have h2 : 2 ∣ Nat.card K := by
      rw [h, Subgroup.card_top, ← hx]
      exact orderOf_dvd_natCard x
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h2) (by norm_num)
  · obtain ⟨k, hk⟩ := (hZ.to_le h).exists_card_eq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Subgroup.eq_bot_of_card_eq K (by rw [hk, pow_zero])
    · exfalso
      have h2 : 2 ∣ Nat.card K := by
        rw [hk]
        exact dvd_pow_self 2 hk0.ne'
      exact absurd (Nat.Coprime.eq_one_of_dvd hc h2) (by norm_num)

theorem fusionZStar_eq_center_of_pPrimeCore_eq_bot (hO : pPrimeCore 2 Q = ⊥) :
    Open.fusionZStar Q = center Q := by
  have hF : Open.fusionOddCore Q = ⊥ := sSup_eq_bot.2 fun N hN =>
    (pPrimeCore_eq_bot_iff.1 hO) N hN.1 (Nat.coprime_two_left.2 hN.2)
  ext x
  simp only [Open.fusionZStar, Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro h m
    have h1 := h (QuotientGroup.mk' _ m)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    rw [hF, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  · intro h y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul, h m]

theorem isTwoQuasisimple_of_quasisimple [Finite Q] (hQ : IsQuasisimple Q)
    (hZ : IsPGroup 2 (center Q)) {x : Q} (hx : orderOf x = 2) : IsTwoQuasisimple Q := by
  have hO := pPrimeCore_eq_bot_of_quasisimple hQ hZ hx
  let e : Q ⧸ pPrimeCore 2 Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  exact ⟨hQ.1, LocalCores.isQuasisimple_of_mulEquiv e.symm hQ⟩

noncomputable def quotientPPrimeCoreEquiv (hO : pPrimeCore 2 Q = ⊥) : Q ⧸ pPrimeCore 2 Q ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot

variable {G : Type*} [Group G]

theorem isTwoComponentIn_of_normalizes {J A : Subgroup G} (hJA : J ≤ A)
    (hn : ∀ a ∈ A, ∀ j ∈ J, a * j * a⁻¹ ∈ J) (hJ : IsTwoQuasisimple ↥J) :
    IsTwoComponentIn J A := by
  refine ⟨hJA, ?_, hJ⟩
  have hN : (J.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff hJA).2 fun j a hj ha => hn a ha j hj
  exact hN.isSubnormal

end CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row
