module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47NineGrp

public section

namespace CFSG.ComponentClassification.FooteLit

open Subgroup

variable {G : Type*} [Group G]

theorem eq_top_of_three_centralizers_of_arith [Finite G]
    {U U' : Subgroup G} (hU : Nat.card U = 4) (hU' : Nat.card U' = 4)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU'c : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a)
    {z u u' : G} (hzU : z ∈ U) (hzU' : z ∈ U') (hz1 : z ≠ 1) (hu : u ∈ U) (hu' : u' ∈ U')
    (huu' : u * u' ≠ u' * u) (hcz : Nat.card (centralizer ({z} : Set G)) = 8)
    (hcu : Nat.card (centralizer ({u} : Set G)) = 8)
    (hcu' : Nat.card (centralizer ({u'} : Set G)) = 8) {J : Subgroup G}
    (hJz : centralizer ({z} : Set G) ≤ J) (hJu : centralizer ({u} : Set G) ≤ J)
    (hJu' : centralizer ({u'} : Set G) ≤ J)
    (harith : J ≠ ⊤ → ∀ n : ℕ, 0 < n → 8 ∣ n → n ≠ 8 → n ∣ Nat.card J → n = Nat.card J) :
    J = ⊤ := by
  by_contra hJ
  have key : ∀ (V : Subgroup G) (v v' : G), Nat.card V = 4 →
      (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) → z ∈ V → v ∈ V →
      Nat.card (centralizer ({v} : Set G)) = 8 → centralizer ({v} : Set G) ≤ J →
      v' ∈ centralizer ({z} : Set G) → v' ∉ centralizer ({v} : Set G) →
      J ≤ normalizer (V : Set G) := by
    intro V v v' hV hVc hzV hvV hcv hJv hv'z hv'v
    have hzN : centralizer ({z} : Set G) ≤ J ⊓ normalizer (V : Set G) :=
      le_inf hJz (Foote47.centralizer_le_normalizer_of_card_four hV hVc hzV hcz)
    have hvN : centralizer ({v} : Set G) ≤ J ⊓ normalizer (V : Set G) :=
      le_inf hJv (Foote47.centralizer_le_normalizer_of_card_four hV hVc hvV hcv)
    have h8 : 8 ∣ Nat.card (J ⊓ normalizer (V : Set G) : Subgroup G) :=
      hcz ▸ card_dvd_of_le hzN
    have hNJ : Nat.card (J ⊓ normalizer (V : Set G) : Subgroup G) ∣ Nat.card J :=
      card_dvd_of_le inf_le_left
    have hN8 : Nat.card (J ⊓ normalizer (V : Set G) : Subgroup G) ≠ 8 := by
      intro h
      have e1 := eq_of_le_of_card_ge hzN (by rw [h, hcz])
      have e2 := eq_of_le_of_card_ge hvN (by rw [h, hcv])
      exact hv'v (by rw [e2, ← e1]; exact hv'z)
    have heq := harith hJ _ Nat.card_pos h8 hN8 hNJ
    have hNJ' : J ⊓ normalizer (V : Set G) = J := eq_of_le_of_card_ge inf_le_left heq.ge
    rw [← hNJ']
    exact inf_le_right
  have hNU := key U u u' hU hUc hzU hu hcu hJu
    (Foote47.le_centralizer_of_forall_comm hU'c hzU' hu')
    (fun h => huu' (mem_centralizer_singleton_iff.mp h).symm)
  have hNU' := key U' u' u hU' hU'c hzU' hu' hcu' hJu'
    (Foote47.le_centralizer_of_forall_comm hUc hzU hu)
    (fun h => huu' (mem_centralizer_singleton_iff.mp h))
  have hJz' : J ≤ centralizer ({z} : Set G) := by
    intro g hg
    have h1 : g * z * g⁻¹ ∈ U := (mem_normalizer_iff.mp (hNU hg) z).mp hzU
    have h2 : g * z * g⁻¹ ∈ U' := (mem_normalizer_iff.mp (hNU' hg) z).mp hzU'
    have hne1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hcap : g * z * g⁻¹ = z := by
      by_contra hne
      have hzI : z ∈ U ⊓ U' := ⟨hzU, hzU'⟩
      have hwI : g * z * g⁻¹ ∈ U ⊓ U' := ⟨h1, h2⟩
      have hd : Nat.card (U ⊓ U' : Subgroup G) ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hU]
        exact card_dvd_of_le inf_le_left
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      interval_cases k
      · rw [pow_zero] at hk'
        have : Subsingleton (U ⊓ U' : Subgroup G) := (Nat.card_eq_one_iff_unique.mp hk').1
        exact hz1 (congrArg Subtype.val
          (Subsingleton.elim (⟨z, hzI⟩ : (U ⊓ U' : Subgroup G)) 1))
      · rw [pow_one] at hk'
        obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : (U ⊓ U' : Subgroup G))).mp hk'
        have e1 := hy ⟨z, hzI⟩ (fun h => hz1 (congrArg Subtype.val h))
        have e2 := hy ⟨_, hwI⟩ (fun h => hne1 (congrArg Subtype.val h))
        exact hne (congrArg Subtype.val (e2.trans e1.symm))
      · have e1 : U ⊓ U' = U := eq_of_le_of_card_ge inf_le_left (by rw [hU, hk']; norm_num)
        have e2 : U ⊓ U' = U' := eq_of_le_of_card_ge inf_le_right (by rw [hU', hk']; norm_num)
        have hu'U : u' ∈ U := by rw [← e1, e2]; exact hu'
        exact huu' (hUc u hu u' hu'U)
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hcap]
  have e : centralizer ({u} : Set G) = centralizer ({z} : Set G) :=
    eq_of_le_of_card_ge (hJu.trans hJz') (by rw [hcu, hcz])
  have hu'z : u' ∈ centralizer ({z} : Set G) := Foote47.le_centralizer_of_forall_comm hU'c hzU' hu'
  rw [← e] at hu'z
  exact huu' (mem_centralizer_singleton_iff.mp hu'z).symm

theorem seven_le_index_of_card_eq_168 [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 168)
    {J : Subgroup G} (hJ : J ≠ ⊤) : 7 ≤ J.index := by
  have hcore : J.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (by rw [← h]; exact J.normalCore_le)) hJ
  have hdvd := J.index_normalCore_dvd_factorial_index
  rw [hcore, index_bot, hG] at hdvd
  by_contra hlt
  push Not at hlt
  have hpos : 0 < J.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := J))
  interval_cases h : J.index <;> norm_num [Nat.factorial] at hdvd

theorem eq_of_dvd_of_le_twentyfour {n j : ℕ} (hn0 : 0 < n) (h8 : 8 ∣ n) (hn8 : n ≠ 8)
    (hnj : n ∣ j) (hj : j ∣ 168) (hj24 : j ≤ 24) : n = j := by
  have hj0 : 0 < j := Nat.pos_of_dvd_of_pos hj (by norm_num)
  have hle : n ≤ j := Nat.le_of_dvd hj0 hnj
  have h8j : 8 ∣ j := dvd_trans h8 hnj
  have hj' : j = 8 ∨ j = 24 := by
    interval_cases j <;> omega
  rcases hj' with rfl | rfl
  · interval_cases n <;> omega
  · interval_cases n <;> omega

theorem eq_top_of_three_centralizers_le_168 [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 168)
    {U U' : Subgroup G} (hU : Nat.card U = 4) (hU' : Nat.card U' = 4)
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU'c : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a)
    {z u u' : G} (hzU : z ∈ U) (hzU' : z ∈ U') (hz1 : z ≠ 1) (hu : u ∈ U) (hu' : u' ∈ U')
    (huu' : u * u' ≠ u' * u) (hcz : Nat.card (centralizer ({z} : Set G)) = 8)
    (hcu : Nat.card (centralizer ({u} : Set G)) = 8)
    (hcu' : Nat.card (centralizer ({u'} : Set G)) = 8) {J : Subgroup G}
    (hJz : centralizer ({z} : Set G) ≤ J) (hJu : centralizer ({u} : Set G) ≤ J)
    (hJu' : centralizer ({u'} : Set G) ≤ J) : J = ⊤ := by
  refine eq_top_of_three_centralizers_of_arith hU hU' hUc hU'c hzU hzU' hz1 hu hu' huu' hcz hcu
    hcu' hJz hJu hJu' fun hJ n hn0 h8 hn8 hnJ => ?_
  have h7 := seven_le_index_of_card_eq_168 hG hJ
  have hmul := J.card_mul_index
  rw [hG] at hmul
  have hJ24 : Nat.card J ≤ 24 := by nlinarith
  exact eq_of_dvd_of_le_twentyfour hn0 h8 hn8 hnJ ⟨_, hmul.symm⟩ hJ24

end CFSG.ComponentClassification.FooteLit
