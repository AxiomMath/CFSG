module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21A6

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M24Std.CResH4

theorem natCard_z2s6 : Nat.card (Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) = 1440 := by
  rw [Nat.card_prod, card_perm_six]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [this]

variable {G : Type} [Group G] [Finite G] {z : G}

theorem natCard_centralizer_eq {U : Subgroup G} {u k : G} (hu : u ∈ U)
    (hk : k ∈ centralizer (U : Set G)) :
    Nat.card (U ⊓ centralizer ({u * k} : Set G) : Subgroup G) =
      Nat.card (centralizer ({(⟨u, hu⟩ : U)} : Set U)) := by
  have : (centralizer ({(⟨u, hu⟩ : U)} : Set U)).map U.subtype =
      U ⊓ centralizer ({u * k} : Set G) := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine mem_inf.2 ⟨y'.2, ?_⟩
      have h1 : (y' : G) * u = u * (y' : G) :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy')
      have h2 : (y' : G) * k = k * (y' : G) := mem_centralizer_iff.1 hk _ y'.2
      rw [mem_centralizer_singleton_iff]
      calc (y' : G) * (u * k) = (y' * u) * k := by rw [mul_assoc]
        _ = (u * y') * k := by rw [h1]
        _ = u * (y' * k) := by rw [mul_assoc]
        _ = u * (k * y') := by rw [h2]
        _ = (u * k) * y' := by rw [mul_assoc]
    · intro hy
      obtain ⟨hyU, hyc⟩ := mem_inf.1 hy
      refine ⟨⟨y, hyU⟩, ?_, rfl⟩
      have h1 := mem_centralizer_singleton_iff.1 hyc
      have h2 : y * k = k * y := mem_centralizer_iff.1 hk _ hyU
      show (⟨y, hyU⟩ : U) ∈ centralizer ({(⟨u, hu⟩ : U)} : Set U)
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      show y * u = u * y
      have : y * u * k = u * y * k := by
        calc y * u * k = y * (u * k) := by rw [mul_assoc]
          _ = u * k * y := h1
          _ = u * (k * y) := by rw [mul_assoc]
          _ = u * (y * k) := by rw [h2]
          _ = u * y * k := by rw [mul_assoc]
      exact mul_right_cancel this
  rw [← this, Subgroup.card_map_of_injective U.subtype_injective]

theorem not_mem_sup_centralizer_of_table (hz : orderOf z = 2)
    (φ : ↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (U : Subgroup G) [U.Normal] (hZ : ∀ u : U, (∀ g : U, g * u = u * g) → u = 1)
    (hbig : 1440 < Nat.card U)
    (hTab : ∀ u : U, u * u = 1 → u ≠ 1 →
      ¬ (Nat.card (centralizer ({u} : Set U)) = 1 ∨ Nat.card (centralizer ({u} : Set U)) = 2 ∨
        Nat.card (centralizer ({u} : Set U)) = 360 ∨ Nat.card (centralizer ({u} : Set U)) = 720 ∨
        Nat.card (centralizer ({u} : Set U)) = 1440)) :
    z ∉ U ⊔ centralizer (U : Set G) := by
  intro hmem
  obtain ⟨u, hu, k, hk, hzuk⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hcomm : ∀ y ∈ U, y * k = k * y := fun y hy => mem_centralizer_iff.1 hk y hy
  have huk : u * k = k * u := hcomm u hu
  have hsq : u * u * (k * k) = 1 := by
    have h1 : (u * k) * (u * k) = u * u * (k * k) := by
      calc (u * k) * (u * k) = u * (k * u) * k := by simp only [mul_assoc]
        _ = u * (u * k) * k := by rw [huk]
        _ = u * u * (k * k) := by simp only [mul_assoc]
    rw [← h1, hzuk]
    exact htt
  have hu2 : u * u = 1 := by
    have hkk : ∀ y ∈ U, y * (k * k) = (k * k) * y := by
      intro y hy
      rw [← mul_assoc, hcomm y hy, mul_assoc, hcomm y hy, ← mul_assoc]
    have hinv : u * u = (k * k)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hc : ∀ g : U, g * (⟨u * u, mul_mem hu hu⟩ : U) = (⟨u * u, mul_mem hu hu⟩ : U) * g := by
      intro g
      apply Subtype.ext
      show (g : G) * (u * u) = (u * u) * g
      rw [hinv]
      exact (Commute.inv_right (hkk g g.2 : Commute (g : G) (k * k))).eq
    have := congrArg Subtype.val (hZ _ hc)
    exact this
  by_cases hu1 : u = 1
  · have hzk : z = k := by rw [← hzuk, hu1, one_mul]
    have hle : U ≤ centralizer ({z} : Set G) := by
      intro y hy
      rw [mem_centralizer_singleton_iff, hzk]
      exact hcomm y hy
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr φ.toEquiv, natCard_z2s6] at h1
    omega
  · have h1 := card_normal_z2s6 _ (normal_map_inf_centralizer (E := U) φ)
    rw [card_map_inf_centralizer φ, ← hzuk, natCard_centralizer_eq hu hk] at h1
    refine hTab ⟨u, hu⟩ (Subtype.ext hu2) (fun h => hu1 (congrArg Subtype.val h)) ?_
    exact h1

theorem noBadCent_of_noTen {U : Type} [Group U] [Finite U] [IsSimpleGroup U]
    (hbig : 2 < Nat.card U) (hten : ∀ g : U, orderOf g ≠ 10) (u : U) (hu : u * u = 1)
    (hu1 : u ≠ 1) :
    ¬ (Nat.card (centralizer ({u} : Set U)) = 1 ∨ Nat.card (centralizer ({u} : Set U)) = 2 ∨
      Nat.card (centralizer ({u} : Set U)) = 360 ∨ Nat.card (centralizer ({u} : Set U)) = 720 ∨
      Nat.card (centralizer ({u} : Set U)) = 1440) := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
  have huC : u ∈ centralizer ({u} : Set U) := mem_centralizer_singleton_iff.2 rfl
  have h5 : (5 : ℕ) ∣ Nat.card (centralizer ({u} : Set U)) →
      False := by
    intro hd
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := centralizer ({u} : Set U)) 5 hd
    have hyU : orderOf (y : U) = 5 := by rw [← hy]; exact (Subgroup.orderOf_coe y)
    have hcomm : Commute u (y : U) := (mem_centralizer_singleton_iff.1 y.2).symm
    have : orderOf (u * (y : U)) = 10 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hord, hyU]; norm_num), hord, hyU]
    exact hten _ this
  rintro (h | h | h | h | h)
  · have : 1 < Nat.card (centralizer ({u} : Set U)) := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨Nat.card_pos.ne', fun h1 => hu1 ?_⟩
      have := Subgroup.eq_bot_of_card_eq _ h1
      have hm : u ∈ (⊥ : Subgroup U) := this ▸ huC
      exact Subgroup.mem_bot.1 hm
    omega
  ·
    have hU2 : ∀ V : Subgroup U, IsPGroup 2 V → V ≤ (⊤ : Subgroup U) →
        V ≤ centralizer ({u} : Set U) → Nat.card V ≤ 2 := fun V _ _ hV =>
      (Subgroup.card_le_of_le hV).trans h.le
    have hX : ∀ N : Subgroup U, N.Normal → Odd (Nat.card N) → N = ⊥ := by
      intro N hN hodd
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h0 | h0
      · exact h0
      · exfalso
        have hdvd : 2 ∣ Nat.card U := hord ▸ orderOf_dvd_natCard u
        rw [h0, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
    have htop := CResH4.normal_eq_zpowers (⊤ : Subgroup U) (Subgroup.mem_top u) hu hu1 hU2 hX
    have hc : Nat.card U = 2 := by
      rw [← Subgroup.card_top (G := U), htop, Nat.card_zpowers, hord]
    omega
  · exact h5 (by rw [h]; norm_num)
  · exact h5 (by rw [h]; norm_num)
  · exact h5 (by rw [h]; norm_num)

end CFSG.EvenSporadicStandard.M22Std
