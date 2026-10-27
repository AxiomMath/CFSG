module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Shape

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem false_of_involution_avoids_index_two {G : Type*} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {Q U : Subgroup G}
    (hQ : IsPGroup 2 Q) (hQidx : ¬ 2 ∣ Q.index) (hUQ : U ≤ Q) (hUidx : U.relIndex Q = 2) {z : G}
    (hzQ : z ∈ Q) (hzU : z ∉ U) (hz2 : z * z = 1) (havoid : ∀ g : G, g⁻¹ * z * g ∉ U) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := fun h => hzU (h ▸ U.one_mem)
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hQ hQidx hUQ
    hUidx hzQ hzU (fun y _ hyU => by
      rw [hord]
      have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
      by_contra hlt
      have h1 : orderOf y = 1 := by have := orderOf_pos y; omega
      exact hy1 (orderOf_eq_one_iff.1 h1)) havoid
  rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
  · have hcard : Nat.card G = 2 := by rw [h, Subgroup.index_bot] at hNidx; exact hNidx
    have : IsCyclic G := isCyclic_of_prime_card hcard
    let _ : CommGroup G := IsCyclic.commGroup
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm a b)
  · rw [h, Subgroup.index_top] at hNidx
    exact absurd hNidx (by norm_num)

namespace OuterConfig

variable {G : Type} [Group G] {A : Subgroup G} {z t : G} {T : Subgroup G}
  (h : OuterConfig G A z t T)

include h in
theorem card_le_of_two_subgroup_cent_conj [Finite G] {g : G} {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRc : R ≤ centralizer ({g * z * g⁻¹} : Set G)) : Nat.card R ≤ Nat.card T := by
  set R₁ : Subgroup G := R.map (MulAut.conj g⁻¹).toMonoidHom with hR₁
  have hR₁2 : IsPGroup 2 R₁ := hR.map _
  have hR₁z : R₁ ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hrη := mem_centralizer_singleton_iff.1 (hRc hr)
    show g⁻¹ * r * g⁻¹⁻¹ * z = z * (g⁻¹ * r * g⁻¹⁻¹)
    simp only [inv_inv]
    calc g⁻¹ * r * g * z = g⁻¹ * (r * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * r) * g := by rw [hrη]
      _ = z * (g⁻¹ * r * g) := by group
  obtain ⟨k, -, hk⟩ := h.exists_conj_into_T hR₁2 hR₁z
  set R₂ : Subgroup G := R₁.map (MulAut.conj k⁻¹).toMonoidHom with hR₂
  have hR₂T : R₂ ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    have := hk y hy
    simpa [MulAut.conj_apply] using this
  have hc₁ : Nat.card R₁ = Nat.card R := Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hc₂ : Nat.card R₂ = Nat.card R₁ := Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  rw [← hc₁, ← hc₂]
  exact Subgroup.card_le_of_le hR₂T

include h in
theorem not_conj_of_large_two_subgroup [Finite G] {η : G} {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRc : R ≤ centralizer ({η} : Set G)) (hlarge : Nat.card T < Nat.card R) (g : G) :
    η ≠ g * z * g⁻¹ := by
  intro hη
  rw [hη] at hRc
  exact absurd (h.card_le_of_two_subgroup_cent_conj hR hRc) (not_le.2 hlarge)

end OuterConfig

end CFSG.EvenSporadicStandard.Fin76b
