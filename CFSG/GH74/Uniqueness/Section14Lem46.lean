module

public import CFSG.GH74.Uniqueness.Section14Lem46b

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

namespace Sec146

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem main_u [Finite X] {u : X} (hu : u ∈ U) (hu1 : u ≠ 1)
    (huS : ∀ s ∈ S2, s * u * s⁻¹ * u⁻¹ ∈ Mo) :
    K ≤ normalizer (S2 : Set X) ∧ Nat.card S2 = 2 ^ n * Nat.card T ∧ (∀ x ∈ S2, x * x ∈ T) ∧
      (∀ a ∈ S2, a ∉ T → ∀ b ∈ S2, b ∉ T → ∃ k ∈ K, (k * a * k⁻¹)⁻¹ * b ∈ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := stabCoset Mo u
  set θ := stabCosetHom Mo (Mo_comm F) u with hθ
  have hS2N₀ : S2 ≤ N₀ := fun s hs => ⟨S2_le_C0 F hs, huS s hs⟩
  have hTN₀ : T ≤ N₀ := F.T_le_S2.trans hS2N₀
  have hker : ∀ g : ↥N₀, θ g = 1 ↔ (g : X) ∈ T := by
    intro g
    rw [hθ, stabCosetHom_eq_one_iff, ← F.cent_Mo_u u hu hu1, mem_inf,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨g.2.1, h⟩, fun h => h.2⟩
  have hkerT : θ.ker = T.subgroupOf N₀ := by
    ext g
    rw [MonoidHom.mem_ker, hker, mem_subgroupOf]
  have hcard : Nat.card N₀ = Nat.card T * Nat.card θ.range := by
    have h1 := Subgroup.card_mul_index θ.ker
    rw [Subgroup.index_ker, hkerT,
      show Nat.card (T.subgroupOf N₀) = Nat.card T from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN₀).toEquiv] at h1
    exact h1.symm
  have hrange : Nat.card θ.range ∣ 2 ^ n := by
    rw [← F.card_Mo]
    exact Subgroup.card_subgroup_dvd_card _
  have hN₀2 : IsPGroup 2 N₀ := by
    obtain ⟨a, ha⟩ := F.T_sylow.isPGroup.exists_card_eq
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrange
    exact IsPGroup.of_card (n := a + b) (by rw [hcard, ha, hb, pow_add])
  have hconj : ∀ g ∈ N₀, ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro g hg x hx
    have hxN : x ∈ N₀ := hTN₀ hx
    have hgxN : g * x * g⁻¹ ∈ N₀ := mul_mem (mul_mem hg hxN) (inv_mem hg)
    have h1 : θ ⟨x, hxN⟩ = 1 := (hker ⟨x, hxN⟩).mpr hx
    have h2 : (⟨g * x * g⁻¹, hgxN⟩ : ↥N₀) = ⟨g, hg⟩ * ⟨x, hxN⟩ * (⟨g, hg⟩ : ↥N₀)⁻¹ := rfl
    have h3 : θ ⟨g * x * g⁻¹, hgxN⟩ = 1 := by
      rw [h2, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    exact (hker _).mp h3
  have hN₀NT : N₀ ≤ normalizer (T : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj g hg x, fun hx => ?_⟩
    have := hconj g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hN₀eq : N₀ = S2 := (F.S2_sylow.eq_of_le hS2N₀ hN₀NT hN₀2)
  have hKkey : ∀ k ∈ K, ∀ g ∈ N₀, k * g * k⁻¹ ∈ N₀ := by
    intro k hk g hg
    obtain ⟨hgC, hgu⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro m hm
      have hm' : k⁻¹ * m * k⁻¹⁻¹ ∈ Mo := K_norm_Mo F _ (inv_mem hk) m hm
      rw [inv_inv] at hm'
      have h1 := (mem_centralizer_iff.mp hgC) _ hm'
      calc m * (k * g * k⁻¹) = k * ((k⁻¹ * m * k) * g) * k⁻¹ := by group
        _ = k * (g * (k⁻¹ * m * k)) * k⁻¹ := by rw [h1]
        _ = k * g * k⁻¹ * m := by group
    · have hc : Commute k u := K_comm_U F k hk u hu
      have hku' : k⁻¹ * u * k = u := by rw [hc.inv_left.eq, inv_mul_cancel_right]
      have huk : u * k⁻¹ * u⁻¹ = k⁻¹ := by rw [← hc.inv_left.eq, mul_inv_cancel_right]
      have e : k * g * k⁻¹ * u * (k * g * k⁻¹)⁻¹ * u⁻¹ =
          k * (g * u * g⁻¹ * u⁻¹) * k⁻¹ := by
        calc k * g * k⁻¹ * u * (k * g * k⁻¹)⁻¹ * u⁻¹
            = k * g * (k⁻¹ * u * k) * g⁻¹ * k⁻¹ * u⁻¹ := by group
          _ = k * g * u * g⁻¹ * k⁻¹ * u⁻¹ := by rw [hku']
          _ = k * (g * u * g⁻¹ * u⁻¹) * (u * k⁻¹ * u⁻¹) := by group
          _ = k * (g * u * g⁻¹ * u⁻¹) * k⁻¹ := by rw [huk]
      rw [e]
      exact K_norm_Mo F k hk _ hgu
  have hKN : K ≤ normalizer (S2 : Set X) := by
    rw [← hN₀eq]
    intro k hk
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hKkey k hk g, fun hg => ?_⟩
    have := hKkey k⁻¹ (inv_mem hk) _ hg
    simpa [mul_assoc] using this
  have hθK : ∀ (k : X) (hk : k ∈ K) (g : ↥N₀),
      ((θ ⟨k * g * k⁻¹, hKkey k hk g g.2⟩ : ↥Mo) : X) = k * (θ g : X) * k⁻¹ := by
    intro k hk g
    rw [hθ, stabCosetHom_apply, stabCosetHom_apply]
    have hc : Commute k u := K_comm_U F k hk u hu
    have hku' : k⁻¹ * u * k = u := by rw [hc.inv_left.eq, inv_mul_cancel_right]
    have huk : u * k⁻¹ * u⁻¹ = k⁻¹ := by rw [← hc.inv_left.eq, mul_inv_cancel_right]
    calc k * (g : X) * k⁻¹ * u * (k * (g : X) * k⁻¹)⁻¹ * u⁻¹
        = k * g * (k⁻¹ * u * k) * (g : X)⁻¹ * k⁻¹ * u⁻¹ := by group
      _ = k * g * u * (g : X)⁻¹ * k⁻¹ * u⁻¹ := by rw [hku']
      _ = k * ((g : X) * u * (g : X)⁻¹ * u⁻¹) * (u * k⁻¹ * u⁻¹) := by group
      _ = k * ((g : X) * u * (g : X)⁻¹ * u⁻¹) * k⁻¹ := by rw [huk]
  have hrange_ne : θ.range ≠ ⊥ := by
    obtain ⟨y, hyS, hyT⟩ := exists_S2_not_T F
    intro hbot
    apply hyT
    have : θ ⟨y, hS2N₀ hyS⟩ ∈ θ.range := ⟨_, rfl⟩
    rw [hbot, mem_bot] at this
    exact (hker _).mp this
  have hrange_top : θ.range = ⊤ := by
    obtain ⟨m₀, hm₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hrange_ne
    obtain ⟨g₀, hg₀⟩ := m₀.2
    rw [eq_top_iff]
    intro m _
    by_cases hm1 : m = 1
    · rw [hm1]
      exact one_mem _
    have hm₀X : ((m₀ : ↥Mo) : X) ≠ 1 := fun h1 => hm₀1 (Subtype.ext (Subtype.ext h1))
    have hmX : (m : X) ≠ 1 := fun h1 => hm1 (Subtype.ext h1)
    obtain ⟨k, hk, hkm⟩ := F.K_trans _ (m₀ : ↥Mo).2 hm₀X _ m.2 hmX
    refine ⟨⟨k * g₀ * k⁻¹, hKkey k hk g₀ g₀.2⟩, Subtype.ext ?_⟩
    rw [hθK k hk g₀, hg₀]
    exact hkm
  refine ⟨hKN, ?_, ?_, ?_⟩
  · rw [← hN₀eq, hcard, hrange_top, card_top, F.card_Mo, mul_comm]
  · intro x hx
    have hxN := hS2N₀ hx
    have h1 : θ (⟨x, hxN⟩ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul]
      exact Subtype.ext (F.Mo_sq _ (θ ⟨x, hxN⟩).2)
    exact (hker _).mp h1
  · intro a ha haT b hb hbT
    have haN := hS2N₀ ha
    have hbN := hS2N₀ hb
    have ha1 : ((θ ⟨a, haN⟩ : ↥Mo) : X) ≠ 1 := fun h1 =>
      haT ((hker _).mp (Subtype.ext h1))
    have hb1 : ((θ ⟨b, hbN⟩ : ↥Mo) : X) ≠ 1 := fun h1 =>
      hbT ((hker _).mp (Subtype.ext h1))
    obtain ⟨k, hk, hkab⟩ := F.K_trans _ (θ ⟨a, haN⟩).2 ha1 _ (θ ⟨b, hbN⟩).2 hb1
    refine ⟨k, hk, ?_⟩
    have hkaN := hKkey k hk a haN
    have h1 : θ ((⟨k * a * k⁻¹, hkaN⟩ : ↥N₀)⁻¹ * ⟨b, hbN⟩) = 1 := by
      rw [map_mul, map_inv]
      have h2 : θ ⟨k * a * k⁻¹, hkaN⟩ = θ ⟨b, hbN⟩ :=
        Subtype.ext ((hθK k hk ⟨a, haN⟩).trans hkab)
      rw [h2, inv_mul_cancel]
    exact (hker _).mp h1

end Sec146

end CFSG.GH74.Uniqueness
