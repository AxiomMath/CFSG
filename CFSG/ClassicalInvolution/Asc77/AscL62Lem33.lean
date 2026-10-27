module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem lemma_3_3_member (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K R V : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) (hV : IsPGroup 2 ↥V)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hVR : Commutes V R) :
    ⁅V, K⁆ ≤ oddCoreOf K :=
  Subgroup.commutator_le.mpr fun v hv k hk =>
    AscL62.centSylow hp hq hΩ hK hR hV (fun _ hy => mem_normalizer_iff_conjSub_eq.mp (hVK hy))
      (fun r hr w hw => (hVR w hw r hr).symm) k hk v hv

theorem lemma_3_3_member_element (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) {t : G}
    (ht : ∃ n : ℕ, orderOf t = 2 ^ n) (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htR : ∀ r ∈ R, r * t = t * r) : ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  obtain ⟨n, hn⟩ := ht
  have hV : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr htK
  have hcomm : Commutes (Subgroup.zpowers t) R := by
    intro v hv r hr
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute t r from (htR r hr).symm) m).eq
  intro k hk
  exact lemma_3_3_member hp hq hΩ hK hR hV hle hcomm (Subgroup.commutator_mem_commutator
    (Subgroup.mem_zpowers t) hk)

theorem lemma_3_3_member_involution (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) {t : G} (ht : t * t = 1)
    (htK : t ∈ Subgroup.normalizer (K : Set G)) (htR : ∀ r ∈ R, r * t = t * r) :
    ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  refine lemma_3_3_member_element hp hq hΩ hK hR ?_ htK htR
  have h2 : orderOf t ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact ht)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact ⟨m, hm⟩

end CFSG.ClassicalInvolution.Asc77
