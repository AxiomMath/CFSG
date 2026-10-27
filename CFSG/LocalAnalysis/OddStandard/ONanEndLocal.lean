module

public import CFSG.GH74.GLS.Stage12.McLEndgame

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Uniqueness CFSG.GH74.GLS.Stage12.McLRec

variable {G : Type} [Group G] [Finite G]

theorem no_strongly_embedded_of_local
    (hs : IsSimpleGroup G)
    (hN : ∀ u : G, orderOf u = 2 → ∀ S : Subgroup G, IsPGroup 2 S →
      S ≤ centralizer ({u} : Set G) →
      (∀ k ∈ centralizer ({u} : Set G), k ∈ normalizer (S : Set G)) →
      Nat.card S ≤ 4)
    (hfour : ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧ x ≠ y)
    (h8 : 8 ≤ 2 ^ (Nat.card G).factorization 2) (M : Subgroup G) (hM : CFSG.IsStronglyEmbedded M)
    (hcent : ∀ u : G, u ∈ M → orderOf u = 2 → centralizer ({u} : Set G) ≤ M) : False := by
  obtain ⟨x, y, hx, hy, hxy, hne⟩ := hfour
  have hrank := two_le_open_pRank_top hx hy hxy hne
  have hL := involutionClosure_eq_top hs hx
  have hev : Even (Nat.card G) := by
    have h2 : 2 ∣ Nat.card G := by
      have := orderOf_dvd_natCard x
      rwa [hx] at this
    exact even_iff_two_dvd.mpr h2
  rcases S_SE_proof G M hM with h | ⟨-, -, hB⟩
  · rw [hL] at h
    omega
  · obtain ⟨S, hSp, hScard, hSM, hMN⟩ := exists_sylow_normalized_of_borel hs hev _ hL M hB
    have hS2 : 2 < Nat.card S := by omega
    obtain ⟨z', hz'S, hz'o, hz'c⟩ := exists_central_involution S hSp hS2
    have hz'M : z' ∈ M := hSM hz'S
    have hKM : centralizer ({z'} : Set G) ≤ M := hcent z' hz'M hz'o
    have hSK : S ≤ centralizer ({z'} : Set G) := by
      intro s hsS
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hz'c s hsS).symm
    have hle := hN z' hz'o S hSp hSK (fun k hk => hMN (hKM hk))
    omega

theorem eq_top_of_local
    (hs : IsSimpleGroup G)
    (hN : ∀ u : G, orderOf u = 2 → ∀ S : Subgroup G, IsPGroup 2 S →
      S ≤ centralizer ({u} : Set G) →
      (∀ k ∈ centralizer ({u} : Set G), k ∈ normalizer (S : Set G)) →
      Nat.card S ≤ 4)
    (hfour : ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧ x ≠ y)
    (h8 : 8 ≤ 2 ^ (Nat.card G).factorization 2) (H : Subgroup G) (hev : Even (Nat.card H))
    (hone : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (f : G) (hfH : f ∈ H) (hf : orderOf f = 2)
    (hcard : Nat.card (centralizer ({f} : Set G)) ≤
      Nat.card (centralizer ({(⟨f, hfH⟩ : H)} : Set H))) : H = ⊤ := by
  by_contra hH
  have hmap :
      (centralizer ({(⟨f, hfH⟩ : H)} : Set H)).map H.subtype ≤ centralizer ({f} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact congrArg Subtype.val (hy' ⟨f, hfH⟩ rfl)
  have hcard' : Nat.card (centralizer ({f} : Set G)) ≤
      Nat.card ((centralizer ({(⟨f, hfH⟩ : H)} : Set H)).map H.subtype) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hcard
  have heq := Subgroup.eq_of_le_of_card_ge hmap hcard'
  have hCf : centralizer ({f} : Set G) ≤ H := by
    rw [← heq]
    exact Subgroup.map_subtype_le _
  have hcent : ∀ u : G, u ∈ H → orderOf u = 2 → centralizer ({u} : Set G) ≤ H := by
    intro u hu ho
    have hu'o : orderOf (⟨u, hu⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact ho
    have hf'o : orderOf (⟨f, hfH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk]; exact hf
    obtain ⟨c, hc⟩ := isConj_iff.mp (hone ⟨f, hfH⟩ ⟨u, hu⟩ hf'o hu'o)
    have hc' : (c : G) * f * (c : G)⁻¹ = u := by
      have := congrArg Subtype.val hc
      simpa using this
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hk
    have hk' : ((c : G)⁻¹ * k * (c : G)) ∈ centralizer ({f} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hc'] at hk
      calc (c : G)⁻¹ * k * (c : G) * f
          = (c : G)⁻¹ * (k * ((c : G) * f * (c : G)⁻¹)) * (c : G) := by group
        _ = (c : G)⁻¹ * (((c : G) * f * (c : G)⁻¹) * k) * (c : G) := by rw [hk]
        _ = f * ((c : G)⁻¹ * k * (c : G)) := by group
    have h1 := hCf hk'
    have h2 : k = (c : G) * ((c : G)⁻¹ * k * (c : G)) * (c : G)⁻¹ := by group
    rw [h2]
    exact H.mul_mem (H.mul_mem c.2 h1) (H.inv_mem c.2)
  exact no_strongly_embedded_of_local hs hN hfour h8 H
    (isStronglyEmbedded_of_centralizers H hH hev hone hcent) hcent

end CFSG.OddStandard.ONanRec
