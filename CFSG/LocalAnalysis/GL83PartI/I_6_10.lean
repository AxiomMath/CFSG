module

public import CFSG.Open.Defs

public section

namespace GL83

open CFSG.Open

@[expose] def I_6_10_1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ Nat.card (Subgroup.center K) → ∀ Q : Sylow p K,
      ¬ IsMulCommutative (Q : Subgroup K) ∧
        ¬ IsCyclic ((Q : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)))

section Proof

variable {K : Type*} [Group K] [Finite K]

theorem not_isMulCommutative_sylow_of_perfect {p : ℕ} [Fact p.Prime] (hperf : commutator K = ⊤)
    (hdvd : p ∣ Nat.card (Subgroup.center K)) (Q : Sylow p K) :
    ¬ IsMulCommutative (Q : Subgroup K) := by
  intro hab
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (z : K) = p := (Subgroup.orderOf_coe z).trans hz
  have hgc : (z : K) ∈ Subgroup.center K := z.2
  have hNle : Subgroup.zpowers (z : K) ≤ Subgroup.center K := Subgroup.zpowers_le.2 hgc
  have : (Subgroup.zpowers (z : K)).Normal := Subgroup.normal_of_le_center hNle
  have hNp : IsPGroup p (Subgroup.zpowers (z : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hgQ : (z : K) ∈ (Q : Subgroup K) := hNp.le_sylow_of_normal Q (Subgroup.mem_zpowers _)
  let ϕ : (Q : Subgroup K) →* Abelianization (Q : Subgroup K) := Abelianization.of
  have htr : MonoidHom.transfer ϕ = 1 := by
    ext x
    have hx : x ∈ commutator K := by rw [hperf]; trivial
    exact Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hx
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * (z : K) ^ k * g₀ ∈ (Q : Subgroup K) →
      g₀⁻¹ * (z : K) ^ k * g₀ = (z : K) ^ k := by
    intro k g₀ _
    have hc := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hgc k) g₀⁻¹
    rw [hc, inv_mul_cancel_right]
  have h2 := MonoidHom.transfer_eq_pow ϕ (z : K) key
  rw [htr] at h2
  have h3 : ϕ ⟨(z : K) ^ (Q : Subgroup K).index, MonoidHom.transfer_eq_pow_aux (z : K) key⟩ = 1 :=
    h2.symm
  have h4 : (⟨(z : K) ^ (Q : Subgroup K).index, MonoidHom.transfer_eq_pow_aux (z : K) key⟩ :
      (Q : Subgroup K)) ∈ commutator (Q : Subgroup K) := by
    rw [← Abelianization.ker_of]
    exact h3
  rw [commutator_eq_bot, Subgroup.mem_bot] at h4
  have h5 : (z : K) ^ (Q : Subgroup K).index = 1 := congrArg Subtype.val h4
  have h6 : orderOf (z : K) ∣ (Q : Subgroup K).index := orderOf_dvd_of_pow_eq_one h5
  rw [hord] at h6
  exact Q.not_dvd_index h6

end Proof

theorem I_6_10_1_proved : I_6_10_1 := by
  intro K _ _ hK p hp _ hdvd Q
  have : Fact p.Prime := ⟨hp⟩
  have hnonab := not_isMulCommutative_sylow_of_perfect hK.1 hdvd Q
  refine ⟨hnonab, fun hcyc => hnonab ?_⟩
  have := hcyc
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    ((QuotientGroup.mk' (Subgroup.center K)).subgroupMap (Q : Subgroup K)) ?_
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : QuotientGroup.mk' (Subgroup.center K) (x : K) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have h2 : (x : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).1 h1
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)

end GL83
