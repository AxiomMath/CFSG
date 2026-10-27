module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGal
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.AutL2Facts

theorem fg_pow_three_of_fixed {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 81)
    {σ : K ≃+* K} (hσ : σ * σ ≠ 1) {t : K} (ht : σ t = t) : t ^ 3 = t := by
  have hK' : Nat.card K = 3 ^ 4 := by rw [hK]; norm_num
  have hcard : Nat.card (K ≃+* K) = 4 := card_ringAut K Nat.prime_three hK'
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK'])
  haveI : ExpChar K 3 := ExpChar.prime Nat.prime_three
  let φ : K ≃+* K := frobeniusEquiv K 3
  have hφ : ∀ s : K, φ s = s ^ 3 := fun s => rfl
  let S : Subgroup (K ≃+* K) :=
    { carrier := {τ | τ t = t}
      mul_mem' := fun {a b} ha hb => by
        change a t = t at ha
        change b t = t at hb
        show a (b t) = t
        rw [hb, ha]
      one_mem' := rfl
      inv_mem' := fun {a} ha => by
        change a t = t at ha
        show a.symm t = t
        rw [RingEquiv.symm_apply_eq]
        exact ha.symm }
  have hord : orderOf σ = 4 := by
    have hdvd : orderOf σ ∣ 4 := hcard ▸ orderOf_dvd_natCard σ
    have h1 : orderOf σ ≠ 1 := fun h => hσ (by
      rw [orderOf_eq_one_iff.mp h]
      simp)
    have h2 : orderOf σ ≠ 2 := fun h => hσ (by
      rw [← pow_two]
      exact h ▸ pow_orderOf_eq_one σ)
    have hpos : 0 < orderOf σ := orderOf_pos σ
    have hle : orderOf σ ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have h3 : orderOf σ ≠ 3 := fun h3 => by
      rw [h3] at hdvd
      exact absurd hdvd (by decide)
    omega
  have htop : Subgroup.zpowers σ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hφmem : φ ∈ Subgroup.zpowers σ := by
    rw [htop]
    exact Subgroup.mem_top _
  have hle : Subgroup.zpowers σ ≤ S := (Subgroup.zpowers_le).mpr ht
  exact (hφ t).symm.trans (hle hφmem)

end CFSG.OddStandard.SmallF3.Omega
