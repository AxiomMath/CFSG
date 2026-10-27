module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Fusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.I21

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_two_two_fusion (h : Sec622Bar G t u x) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hRS : secTwoR t u ≤ S) (hne : secTwoR t u ≠ S) :
    (∀ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) →
        g * t * g⁻¹ = t ∨ ∃ j : ℕ, g * t * g⁻¹ = t * (x ^ j * u ^ 2)) ∧
      ∀ j : ℕ, ∃ g : G, g * t * g⁻¹ = t * (x ^ j * u ^ 2) := by
  obtain ⟨y, -, -, -, hy⟩ := h.secTwo.exists_conj_t_eq hS hRS hne
  refine ⟨fun g hg => (h.conj_t_inter_C ⟨y, hy⟩ _ hg).mp ⟨g, rfl⟩, fun j => ?_⟩
  exact ⟨x ^ (3 * j) * y, h.conj_t_x_pow y hy j⟩

theorem sec622_constrained (h : SecTwoHyp G t u) {Q : Subgroup G} (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (hCQ : centralizer (Q : Set G) ≤ Q) : Sec622T1 u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hQn
  rcases h.center_or_wreathS3 hQ2 hCQ with hz | ⟨A, hAn, -, hA16, -, -, hzA, -⟩
  · have hz2 : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.u_pow_four
    refine ⟨zpowers (u ^ 2), ?_, ?_, mem_zpowers _⟩
    · have hzc : ∀ g : G, g * u ^ 2 * g⁻¹ = u ^ 2 := fun g => by
        have := Subgroup.mem_center_iff.mp hz g
        change g * u ^ 2 = u ^ 2 * g at this
        rw [this, mul_inv_cancel_right]
      exact ⟨fun a ha g => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
        rw [← conj_zpow, hzc]
        exact zpow_mem (mem_zpowers _) k⟩
    · rw [IsPGroup.iff_card, Nat.card_zpowers]
      have hd : orderOf (u ^ 2) ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hz2)
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      exact ⟨k, hk⟩
  · refine ⟨A, hAn, ?_, hzA⟩
    rw [IsPGroup.iff_card, hA16]
    exact ⟨4, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits
