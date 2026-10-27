module

public import CFSG.LargeExtraspecial.S5Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem orderOf_eq_three (H : S4.Hyp4 S g) (hNo : S4.NoA2 S g) (C : S4.Cons311 S g)
    {y : S.O} {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e) (hy : orderOf y = p ^ e)
    (hyM : y ∈ S.Mbar) (hinv : ∀ s ∈ S.Lbar g, s * y * s⁻¹ ∈ zpowers y) : orderOf y = 3 := by
  classical
  have hA2 : ∀ s ∈ S.Lbar g, s * s = 1 := fun s hs => S4.mul_self_of_mem_Lbar S H.conj_mem hs
  obtain ⟨t, htL, ht1, hty⟩ := exists_ne_one_commute_of_four_le hA2 (four_le_card_Lbar H C) hp
    hp2 hy hinv
  have hodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, hy]
    exact (hp.odd_of_ne_two hp2).pow
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    exact absurd hy.symm (Nat.pow_eq_one.not.mpr (by
      push Not
      exact ⟨hp.one_lt.ne', he.ne'⟩))
  have hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ zpowers y, s * x * s⁻¹ ∈ zpowers y := by
    intro s hs x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact zpow_mem (hinv s hs) i
  have hcomm : ∀ s : S.O, s * y = y * s → ∀ x ∈ zpowers y, s * x = x * s := by
    intro s hs x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_right hs i).eq
  rcases timmesfeld_4_8_M H hNo C htL ht1 (zpowers_le.mpr hyM) hodd
      (fun h => hy1 (zpowers_eq_bot.mp h))
      (fun x hx => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        exact ((Commute.zpow_left hty.symm i)).eq)
      hnorm (fun x hx hc => eq_one_of_mem_of_commute H hodd hx hc) with h3 | ⟨-, h8, hCL⟩
  · rwa [Nat.card_zpowers] at h3
  · exfalso
    obtain ⟨s₀, hs₀, hs₀y⟩ : ∃ s₀ ∈ S.Lbar g, s₀ * y ≠ y * s₀ := by
      by_contra hcon
      push Not at hcon
      exact hy1 (eq_one_of_mem_of_commute H hodd (mem_zpowers y) hcon)
    have hconj : ∀ s ∈ S.Lbar g, s * y * s⁻¹ = y ∨ s * y * s⁻¹ = y⁻¹ := fun s hs =>
      conj_eq_self_or_inv hp hp2 hy (hA2 s hs) (hinv s hs)
    have hs₀inv : s₀ * y * s₀⁻¹ = y⁻¹ := by
      refine (hconj s₀ hs₀).resolve_left fun h => hs₀y ?_
      calc s₀ * y = s₀ * y * s₀⁻¹ * s₀ := by group
        _ = y * s₀ := by rw [h]
    have hsub : ((S.Lbar g : Subgroup S.O) : Set S.O) ⊆ ↑({1, t, s₀, s₀ * t} : Finset S.O) := by
      intro s hs
      have hs' : s ∈ S.Lbar g := hs
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases hconj s hs' with h | h
      · have hsy : s * y = y * s := by
          calc s * y = s * y * s⁻¹ * s := by group
            _ = y * s := by rw [h]
        rcases hCL s hs' (hcomm s hsy) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
      · have hsy : (s₀ * s) * y = y * (s₀ * s) := by
          have e : (s₀ * s) * y * (s₀ * s)⁻¹ = y := by
            calc (s₀ * s) * y * (s₀ * s)⁻¹ = s₀ * (s * y * s⁻¹) * s₀⁻¹ := by group
              _ = (s₀ * y * s₀⁻¹)⁻¹ := by rw [h]; group
              _ = y := by rw [hs₀inv, inv_inv]
          calc (s₀ * s) * y = (s₀ * s) * y * (s₀ * s)⁻¹ * (s₀ * s) := by group
            _ = y * (s₀ * s) := by rw [e]
        have hs₀s : s = s₀ * (s₀ * s) := by
          rw [← mul_assoc, hA2 s₀ hs₀, one_mul]
        rcases hCL (s₀ * s) (mul_mem hs₀ hs') (hcomm _ hsy) with h1 | h1
        · right; right; left
          rw [hs₀s, h1, mul_one]
        · right; right; right
          rw [hs₀s, h1]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
    have h2 : ({1, t, s₀, s₀ * t} : Finset S.O).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      exact Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))
    have h3 : Nat.card (S.Lbar g) ≤ 4 := (h1.trans h2)
    omega

theorem timmesfeld_5_3 (H : S4.Hyp4 S g) (hNo : S4.NoA2 S g) (C : S4.Cons311 S g)
    {K : Subgroup S.O} (hKM : K ≤ S.Mbar) (hcyc : IsCyclic K) (hodd : Odd (Nat.card K))
    (hK : K ≠ ⊥) (hnorm : ∀ s ∈ S.Lbar g, ∀ x ∈ K, s * x * s⁻¹ ∈ K) :
    Nat.card K = 3 ∧ ⁅K, S.Lbar g⁆ ≠ ⊥ := by
  refine ⟨?_, fun h => hK ?_⟩
  · obtain ⟨k, hk⟩ := hcyc.exists_generator
    have hkord : orderOf (k : S.O) = Nat.card K := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hk]
    have hm1 : 1 < Nat.card K := (Subgroup.one_lt_card_iff_ne_bot K).mpr hK
    refine eq_three_of_forall_prime_dvd hm1 fun p hp hpm => ?_
    have hm0 : Nat.card K ≠ 0 := by omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm)
    have hpe : p ^ (Nat.card K).factorization p ∣ Nat.card K := Nat.ordProj_dvd _ p
    have hfac : 0 < (Nat.card K).factorization p := hp.factorization_pos_of_dvd hm0 hpm
    set q := p ^ (Nat.card K).factorization p with hq
    set d := Nat.card K / q with hd
    have hdm : d * q = Nat.card K := Nat.div_mul_cancel hpe
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdm
      exact hm0 hdm.symm
    have hdk : d ∣ orderOf (k : S.O) := hkord ▸ Dvd.intro _ hdm
    have hyord : orderOf ((k : S.O) ^ d) = q := by
      rw [orderOf_pow_of_dvd hd0 hdk, hkord, hd, Nat.div_div_self hpe hm0]
    have hyK : (k : S.O) ^ d ∈ K := K.pow_mem k.2 d
    have hinv : ∀ s ∈ S.Lbar g, s * (k : S.O) ^ d * s⁻¹ ∈ zpowers ((k : S.O) ^ d) := by
      intro s hs
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hk ⟨_, hnorm s hs _ hyK⟩)
      have hj' : (k : S.O) ^ j = s * (k : S.O) ^ d * s⁻¹ := by
        have := congrArg Subtype.val hj
        simpa using this
      have h1 : (s * (k : S.O) ^ d * s⁻¹) ^ q = 1 := by
        rw [conj_pow, ← hyord, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      have h2 : (k : S.O) ^ (j * (q : ℤ)) = 1 := by
        rw [zpow_mul, hj', zpow_natCast, h1]
      have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      rw [hkord, ← hdm, Nat.cast_mul] at h3
      have hpos : (q : ℤ) ≠ 0 := by
        rw [hq]
        exact_mod_cast (pow_pos hp.pos _).ne'
      obtain ⟨i, hi⟩ := (mul_dvd_mul_iff_right hpos).mp h3
      refine mem_zpowers_iff.mpr ⟨i, ?_⟩
      rw [← hj', hi, zpow_mul, zpow_natCast]
    have h3 := orderOf_eq_three H hNo C hp hp2 hfac hyord (hKM hyK) hinv
    rw [hyord] at h3
    exact h3
  · rw [eq_bot_iff]
    intro x hx
    have hxc := (commutator_eq_bot_iff_le_centralizer.mp h) hx
    exact (Subgroup.mem_bot).mpr
      (eq_one_of_mem_of_commute H hodd hx fun s hs => mem_centralizer_iff.mp hxc s hs)

