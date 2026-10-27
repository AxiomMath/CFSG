module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.GH74.GLS.Stage4.Q9.TIAssembly

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem innerL_minusOne_sq : innerL minusOne ^ 2 = 1 := by
  rw [← map_pow, minusOne_sq, map_one]

theorem innerL_minusOne_mul_self : innerL minusOne * innerL minusOne = 1 := by
  rw [← pow_two]; exact innerL_minusOne_sq

theorem innerL_minusOne_ne_one : innerL minusOne ≠ 1 := fun h =>
  minusOne_ne_one (innerL_injective (h.trans (map_one innerL).symm))

theorem innerL_minusOne_comm (l : Lg) : l * innerL minusOne = innerL minusOne * l :=
  Subgroup.mem_center_iff.mp innerL_minusOne_mem_center l

@[expose] def kappaC : ↥Chat := ⟨kappa0, kappa0_mem⟩

@[simp] theorem kappaC_coe : (kappaC : Lg × Lg) = (innerL minusOne, innerL minusOne) := rfl

theorem Chat_ext {a b : ↥Chat} (h1 : a.1.1 = b.1.1) (h2 : a.1.2 = b.1.2) : a = b :=
  Subtype.ext (Prod.ext h1 h2)

theorem Chat_ext_iff {a b : ↥Chat} : a = b ↔ a.1.1 = b.1.1 ∧ a.1.2 = b.1.2 :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => Chat_ext h.1 h.2⟩

theorem kappaC_mem_center : kappaC ∈ Subgroup.center ↥Chat := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Chat_ext (innerL_minusOne_comm _) (innerL_minusOne_comm _)

theorem kappaC_sq : kappaC ^ 2 = 1 :=
  Chat_ext innerL_minusOne_sq innerL_minusOne_sq

theorem kappaC_ne_one : kappaC ≠ 1 := fun h =>
  innerL_minusOne_ne_one (congrArg (fun c : ↥Chat => c.1.1) h)

theorem orderOf_kappaC : orderOf kappaC = 2 :=
  orderOf_eq_prime kappaC_sq kappaC_ne_one

instance : (Subgroup.zpowers kappaC).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr kappaC_mem_center)

abbrev Cq : Type := ↥Chat ⧸ Subgroup.zpowers kappaC

@[expose] def mkC : ↥Chat →* Cq := QuotientGroup.mk' _

noncomputable instance : Fintype Cq := Fintype.ofFinite Cq

theorem mkC_surjective : Function.Surjective mkC := QuotientGroup.mk_surjective

theorem mem_zpowers_kappaC_iff {x : ↥Chat} :
    x ∈ Subgroup.zpowers kappaC ↔ x = 1 ∨ x = kappaC := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hx)
    rw [← pow_mod_orderOf, orderOf_kappaC]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · left; rw [h, pow_zero]
    · right; rw [h, pow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem mkC_eq_mkC_iff {a b : ↥Chat} : mkC a = mkC b ↔ b = a ∨ b = a * kappaC := by
  show (a : Cq) = (b : Cq) ↔ _
  rw [QuotientGroup.eq, mem_zpowers_kappaC_iff, inv_mul_eq_one, inv_mul_eq_iff_eq_mul,
    eq_comm (a := a)]

theorem mkC_eq_one_iff {c : ↥Chat} : mkC c = 1 ↔ c = 1 ∨ c = kappaC :=
  (QuotientGroup.eq_one_iff c).trans mem_zpowers_kappaC_iff

theorem mkC_kappaC : mkC kappaC = 1 := mkC_eq_one_iff.mpr (Or.inr rfl)

theorem card_fiber_mkC [DecidableEq Cq] (x : Cq) :
    (Finset.univ.filter fun c : ↥Chat => mkC c = x).card = 2 := by
  obtain ⟨c₀, rfl⟩ := mkC_surjective x
  have h : (Finset.univ.filter fun c : ↥Chat => mkC c = mkC c₀) = {c₀, c₀ * kappaC} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [eq_comm, mkC_eq_mkC_iff]
  have hne : c₀ ≠ c₀ * kappaC := fun h => kappaC_ne_one (by simpa using h.symm)
  rw [h, Finset.card_pair hne]

theorem sum_mkC {M : Type*} [AddCommMonoid M] (F : Cq → M) :
    2 • ∑ x : Cq, F x = ∑ c : ↥Chat, F (mkC c) := by
  classical
  calc 2 • ∑ x : Cq, F x = ∑ x : Cq, 2 • F x := by rw [Finset.smul_sum]
    _ = ∑ x ∈ Finset.univ.image mkC, 2 • F x := by
        rw [Finset.image_univ_of_surjective mkC_surjective]
    _ = ∑ c : ↥Chat, F (mkC c) := by
        rw [Finset.sum_comp F mkC]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [card_fiber_mkC x]

theorem sum_mkC_nat (F : Cq → ℕ) : 2 * ∑ x : Cq, F x = ∑ c : ↥Chat, F (mkC c) := by
  rw [← sum_mkC, smul_eq_mul]

theorem card_filter_mkC (P : Cq → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : Cq => P x).card * 2 =
      (Finset.univ.filter fun c : ↥Chat => P (mkC c)).card := by
  rw [Finset.card_filter, Finset.card_filter, mul_comm]
  exact sum_mkC_nat fun x => if P x then 1 else 0

theorem natCard_subtype_mkC (P : Cq → Prop) :
    Nat.card {c : ↥Chat // P (mkC c)} = 2 * Nat.card {x : Cq // P x} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, mul_comm]
  exact (card_filter_mkC P).symm

@[expose] def inl1 : SL2 →* ↥Chat where
  toFun M := ⟨(innerL M, 1), by rw [mem_Chat_iff]; simp [parityL_innerL]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' M N := by apply Subtype.ext; simp

@[expose] def inr1 : SL2 →* ↥Chat where
  toFun M := ⟨(1, innerL M), by rw [mem_Chat_iff]; simp [parityL_innerL]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' M N := by apply Subtype.ext; simp

@[simp] theorem inl1_coe (M : SL2) : (inl1 M : Lg × Lg) = (innerL M, 1) := rfl

@[simp] theorem inr1_coe (M : SL2) : (inr1 M : Lg × Lg) = (1, innerL M) := rfl

@[expose] def zq : Cq := mkC (inl1 minusOne)

@[expose] def K1q : Subgroup Cq := (inl1.range).map mkC

@[expose] def K2q : Subgroup Cq := (inr1.range).map mkC

theorem inl1_minusOne_mul_kappaC : inl1 minusOne * kappaC = inr1 minusOne :=
  Chat_ext innerL_minusOne_mul_self (one_mul _)

theorem mkC_eq_zq_iff {c : ↥Chat} : mkC c = zq ↔ c = inl1 minusOne ∨ c = inr1 minusOne := by
  show mkC c = mkC (inl1 minusOne) ↔ _
  rw [eq_comm, mkC_eq_mkC_iff, inl1_minusOne_mul_kappaC]

theorem mkC_pow_eq_zq_iff (c : ↥Chat) (n : ℕ) :
    (mkC c) ^ n = zq ↔ c ^ n = inl1 minusOne ∨ c ^ n = inr1 minusOne := by
  rw [← map_pow, mkC_eq_zq_iff]

theorem inl1_minusOne_mem_center : inl1 minusOne ∈ Subgroup.center ↥Chat := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Chat_ext (innerL_minusOne_comm _) (by simp)

theorem zq_mem_center : zq ∈ Subgroup.center Cq := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨d, rfl⟩ := mkC_surjective y
  rw [zq, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp inl1_minusOne_mem_center d]

theorem mem_centralizer_zq (x : Cq) : x ∈ Subgroup.centralizer ({zq} : Set Cq) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp zq_mem_center x)

theorem orderOf_Chat
    (c : ↥Chat) : orderOf c = Nat.lcm (ordL c.1.1) (ordL c.1.2) := by
  rw [← Subgroup.orderOf_coe, Prod.orderOf, orderOf_Lg, orderOf_Lg]

theorem pow_eq_kappaC_iff (c : ↥Chat) (n : ℕ) :
    c ^ n = kappaC ↔ c.1.1 ^ n = innerL minusOne ∧ c.1.2 ^ n = innerL minusOne :=
  Chat_ext_iff

theorem pow_eq_inl1_minusOne_iff (c : ↥Chat) (n : ℕ) :
    c ^ n = inl1 minusOne ↔ c.1.1 ^ n = innerL minusOne ∧ c.1.2 ^ n = 1 :=
  Chat_ext_iff

theorem pow_eq_inr1_minusOne_iff (c : ↥Chat) (n : ℕ) :
    c ^ n = inr1 minusOne ↔ c.1.1 ^ n = 1 ∧ c.1.2 ^ n = innerL minusOne :=
  Chat_ext_iff

theorem orderOf_mkC_dvd (c : ↥Chat) : orderOf (mkC c) ∣ orderOf c := orderOf_map_dvd mkC c

theorem pow_orderOf_mkC (c : ↥Chat) :
    c ^ orderOf (mkC c) = 1 ∨ c ^ orderOf (mkC c) = kappaC := by
  have h : mkC (c ^ orderOf (mkC c)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  exact mkC_eq_one_iff.mp h

theorem orderOf_dvd_two_mul_orderOf_mkC (c : ↥Chat) : orderOf c ∣ 2 * orderOf (mkC c) := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_mul']
  rcases pow_orderOf_mkC c with h | h
  · rw [h, one_pow]
  · rw [h, kappaC_sq]

theorem orderOf_mkC (c : ↥Chat) :
    orderOf (mkC c) =
      (let o := orderOf c; if Even o ∧ c ^ (o / 2) = kappaC then o / 2 else o) := by
  have h1 := orderOf_mkC_dvd c
  have h2 := orderOf_dvd_two_mul_orderOf_mkC c
  have hpos : 0 < orderOf c := orderOf_pos c
  have hnpos : 0 < orderOf (mkC c) := orderOf_pos _
  have hcn := pow_orderOf_mkC c
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  set n := orderOf (mkC c) with hn
  set o := orderOf c with ho
  have hts : t * s = 2 := by
    apply Nat.eq_of_mul_eq_mul_left hnpos
    calc n * (t * s) = (n * t) * s := (mul_assoc _ _ _).symm
      _ = o * s := by rw [← ht]
      _ = 2 * n := hs.symm
      _ = n * 2 := mul_comm _ _
  have ht_le : t ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨s, hts.symm⟩
  have ht_pos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · simp [h] at hts
    · exact h
  show n = if Even o ∧ c ^ (o / 2) = kappaC then o / 2 else o
  split_ifs with hcond
  · obtain ⟨⟨m, hm⟩, hk⟩ := hcond
    have h3 : n ∣ o / 2 := by
      rw [hn, orderOf_dvd_iff_pow_eq_one, ← map_pow, hk, mkC_kappaC]
    have h4 := Nat.le_of_dvd (by omega) h3
    interval_cases t <;> omega
  · interval_cases t
    · omega
    · exfalso
      apply hcond
      have hc : c ^ n = kappaC := by
        rcases hcn with h | h
        · exfalso
          have h5 := Nat.le_of_dvd hnpos (orderOf_dvd_of_pow_eq_one h)
          omega
        · exact h
      refine ⟨⟨n, by omega⟩, ?_⟩
      rw [show o / 2 = n by omega]
      exact hc

theorem orderOf_mkC_components (c : ↥Chat) :
    orderOf (mkC c) =
      (let o := Nat.lcm (ordL c.1.1) (ordL c.1.2);
        if Even o ∧ c.1.1 ^ (o / 2) = innerL minusOne ∧ c.1.2 ^ (o / 2) = innerL minusOne
          then o / 2 else o) := by
  rw [orderOf_mkC]
  simp only [orderOf_Chat, pow_eq_kappaC_iff]

theorem ordL_pos
    (l : Lg) : 0 < ordL l := Nat.pos_of_ne_zero (ordL_ne_zero l)

theorem pow_eq_one_iff_ordL
    (l : Lg) (k : ℕ) : l ^ k = 1 ↔ ordL l ∣ k := by
  rw [← orderOf_Lg, orderOf_dvd_iff_pow_eq_one]

theorem pow_eq_innerL_minusOne_iff (l : Lg) (k : ℕ) :
    l ^ k = innerL minusOne ↔
      (Even (ordL l) ∧ l ^ (ordL l / 2) = innerL minusOne ∧ k % ordL l = ordL l / 2) := by
  have hpos : 0 < ordL l := ordL_pos l
  constructor
  · intro h
    have hr : l ^ (k % ordL l) = innerL minusOne := by
      rw [← h, ← orderOf_Lg, pow_mod_orderOf]
    have hlt : k % ordL l < ordL l := Nat.mod_lt _ hpos
    have hdvd : ordL l ∣ (k % ordL l) * 2 := by
      rw [← pow_eq_one_iff_ordL, pow_mul, hr, innerL_minusOne_sq]
    set r := k % ordL l with hrdef
    set o := ordL l with hodef
    obtain ⟨t, ht⟩ := hdvd
    have ht2 : t < 2 := by
      by_contra hge
      have : o * 2 ≤ o * t := Nat.mul_le_mul_left o (not_lt.mp hge)
      omega
    interval_cases t
    · exfalso
      have h0 : r = 0 := by omega
      rw [h0, pow_zero] at hr
      exact innerL_minusOne_ne_one hr.symm
    · refine ⟨⟨r, by omega⟩, ?_, by omega⟩
      rw [show o / 2 = r by omega]
      exact hr
  · rintro ⟨-, h2, h3⟩
    rw [← pow_mod_orderOf, orderOf_Lg, h3, h2]

@[expose] def muFlag (l : Lg) : Prop :=
  Even (ordL l) ∧ l ^ (ordL l / 2) = innerL minusOne

instance (l : Lg) : Decidable (muFlag l) :=
  inferInstanceAs (Decidable (Even (ordL l) ∧ l ^ (ordL l / 2) = innerL minusOne))

theorem pow_eq_innerL_minusOne_iff_muFlag (l : Lg) (k : ℕ) :
    l ^ k = innerL minusOne ↔ muFlag l ∧ k % ordL l = ordL l / 2 := by
  rw [pow_eq_innerL_minusOne_iff, muFlag, and_assoc]

theorem minusOne_mul_self : minusOne * minusOne = 1 := by
  rw [← pow_two]; exact minusOne_sq

theorem eq_inl1_minusOne_iff (c : ↥Chat) : c = inl1 minusOne ↔ c.1.1 = innerL minusOne ∧ c.1.2 = 1 :=
  Chat_ext_iff

theorem eq_inr1_minusOne_iff (c : ↥Chat) : c = inr1 minusOne ↔ c.1.1 = 1 ∧ c.1.2 = innerL minusOne :=
  Chat_ext_iff

theorem three_dvd_lcm_iff (a b : ℕ) : 3 ∣ Nat.lcm a b ↔ 3 ∣ a ∨ 3 ∣ b := by
  constructor
  · intro h
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp (h.trans (Nat.lcm_dvd_mul a b))
  · rintro (h | h)
    · exact h.trans (Nat.dvd_lcm_left a b)
    · exact h.trans (Nat.dvd_lcm_right a b)

theorem three_dvd_orderOf_mkC_iff (c : ↥Chat) : 3 ∣ orderOf (mkC c) ↔ 3 ∣ orderOf c := by
  constructor
  · intro h
    exact h.trans (orderOf_mkC_dvd c)
  · intro h
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num)
      (h.trans (orderOf_dvd_two_mul_orderOf_mkC c))

theorem mkC_mem_S3set_iff (c : ↥Chat) :
    mkC c ∈ S3set zq ↔ 3 ∣ ordL c.1.1 ∨ 3 ∣ ordL c.1.2 := by
  show mkC c ∈ Subgroup.centralizer ({zq} : Set Cq) ∧ 3 ∣ orderOf (mkC c) ↔ _
  rw [and_iff_right (mem_centralizer_zq _), three_dvd_orderOf_mkC_iff, orderOf_Chat,
    three_dvd_lcm_iff]

theorem mkC_mem_S2set_iff (c : ↥Chat) :
    mkC c ∈ S2set zq ↔ ∃ k : ℕ,
      (muFlag c.1.1 ∧ k % ordL c.1.1 = ordL c.1.1 / 2 ∧ ordL c.1.2 ∣ k) ∨
      (ordL c.1.1 ∣ k ∧ muFlag c.1.2 ∧ k % ordL c.1.2 = ordL c.1.2 / 2) := by
  show mkC c ∈ Subgroup.centralizer ({zq} : Set Cq) ∧ zq ∈ Subgroup.zpowers (mkC c) ↔ _
  rw [and_iff_right (mem_centralizer_zq _), ← mem_powers_iff_mem_zpowers,
    Submonoid.mem_powers_iff]
  refine exists_congr fun k => ?_
  rw [mkC_pow_eq_zq_iff, pow_eq_inl1_minusOne_iff, pow_eq_inr1_minusOne_iff,
    pow_eq_innerL_minusOne_iff_muFlag, pow_eq_innerL_minusOne_iff_muFlag, pow_eq_one_iff_ordL,
    pow_eq_one_iff_ordL, and_assoc]

theorem mkC_mem_K1q_iff (c : ↥Chat) :
    mkC c ∈ K1q ↔ parityL c.1.1 = 1 ∧ (c.1.2 = 1 ∨ c.1.2 = innerL minusOne) := by
  rw [K1q, Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨M, rfl⟩, hy⟩
    rcases mkC_eq_mkC_iff.mp hy with h | h
    · subst h
      simp [parityL_innerL]
    · subst h
      simp [parityL_innerL]
  · rintro ⟨h1, h2 | h2⟩
    · obtain ⟨M, hM⟩ := exists_innerL_of_parityL_eq_one h1
      exact ⟨inl1 M, ⟨M, rfl⟩, mkC_eq_mkC_iff.mpr (Or.inl (Chat_ext hM h2))⟩
    · obtain ⟨M, hM⟩ := exists_innerL_of_parityL_eq_one h1
      refine ⟨inl1 (M * minusOne), ⟨M * minusOne, rfl⟩, mkC_eq_mkC_iff.mpr (Or.inr ?_)⟩
      refine Chat_ext ?_ ?_
      · show c.1.1 = innerL (M * minusOne) * innerL minusOne
        rw [← map_mul, mul_assoc, minusOne_mul_self, mul_one, hM]
      · show c.1.2 = 1 * innerL minusOne
        rw [one_mul, h2]

theorem mkC_mem_K2q_iff (c : ↥Chat) :
    mkC c ∈ K2q ↔ parityL c.1.2 = 1 ∧ (c.1.1 = 1 ∨ c.1.1 = innerL minusOne) := by
  rw [K2q, Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨M, rfl⟩, hy⟩
    rcases mkC_eq_mkC_iff.mp hy with h | h
    · subst h
      simp [parityL_innerL]
    · subst h
      simp [parityL_innerL]
  · rintro ⟨h1, h2 | h2⟩
    · obtain ⟨M, hM⟩ := exists_innerL_of_parityL_eq_one h1
      exact ⟨inr1 M, ⟨M, rfl⟩, mkC_eq_mkC_iff.mpr (Or.inl (Chat_ext h2 hM))⟩
    · obtain ⟨M, hM⟩ := exists_innerL_of_parityL_eq_one h1
      refine ⟨inr1 (M * minusOne), ⟨M * minusOne, rfl⟩, mkC_eq_mkC_iff.mpr (Or.inr ?_)⟩
      refine Chat_ext ?_ ?_
      · show c.1.1 = 1 * innerL minusOne
        rw [one_mul, h2]
      · show c.1.2 = innerL (M * minusOne) * innerL minusOne
        rw [← map_mul, mul_assoc, minusOne_mul_self, mul_one, hM]

theorem mkC_mem_S5set_iff (c : ↥Chat) :
    mkC c ∈ S5set K1q K2q ↔ orderOf (mkC c) = 5 ∧
      ((parityL c.1.1 = 1 ∧ (c.1.2 = 1 ∨ c.1.2 = innerL minusOne)) ∨
        (parityL c.1.2 = 1 ∧ (c.1.1 = 1 ∨ c.1.1 = innerL minusOne))) := by
  show (mkC c ∈ K1q ∨ mkC c ∈ K2q) ∧ orderOf (mkC c) = 5 ↔ _
  rw [mkC_mem_K1q_iff, mkC_mem_K2q_iff, and_comm]

theorem exists_mod_eq_half_and_dvd_iff {a b : ℕ} (ha : 0 < a) :
    (∃ k : ℕ, k % a = a / 2 ∧ b ∣ k) ↔ Nat.gcd a b ∣ a / 2 := by
  constructor
  · rintro ⟨k, hk1, hk2⟩
    have hg3 : Nat.gcd a b ∣ a * (k / a) := (Nat.gcd_dvd_left a b).mul_right _
    have hg2 : Nat.gcd a b ∣ k := (Nat.gcd_dvd_right a b).trans hk2
    have h : Nat.gcd a b ∣ k % a := by
      have h' := Nat.div_add_mod k a
      rw [← h'] at hg2
      exact (Nat.dvd_add_right hg3).mp hg2
    rwa [hk1] at h
  · intro h
    have hmod : a / 2 ≡ 0 [MOD Nat.gcd a b] := (Nat.modEq_zero_iff_dvd).mpr h
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hmod
    refine ⟨k, ?_, (Nat.modEq_zero_iff_dvd).mp hk2⟩
    have hk1' : k % a = a / 2 % a := hk1
    rw [hk1']
    exact Nat.mod_eq_of_lt (by omega)

theorem mkC_mem_S2set_iff_gcd (c : ↥Chat) :
    mkC c ∈ S2set zq ↔
      (muFlag c.1.1 ∧ Nat.gcd (ordL c.1.1) (ordL c.1.2) ∣ ordL c.1.1 / 2) ∨
      (muFlag c.1.2 ∧ Nat.gcd (ordL c.1.1) (ordL c.1.2) ∣ ordL c.1.2 / 2) := by
  rw [mkC_mem_S2set_iff]
  have h1 := ordL_pos c.1.1
  have h2 := ordL_pos c.1.2
  constructor
  · rintro ⟨k, ⟨hf, hk1, hk2⟩ | ⟨hk1, hf, hk2⟩⟩
    · exact Or.inl ⟨hf, (exists_mod_eq_half_and_dvd_iff h1).mp ⟨k, hk1, hk2⟩⟩
    · refine Or.inr ⟨hf, ?_⟩
      rw [Nat.gcd_comm]
      exact (exists_mod_eq_half_and_dvd_iff h2).mp ⟨k, hk2, hk1⟩
  · rintro (⟨hf, h⟩ | ⟨hf, h⟩)
    · obtain ⟨k, hk1, hk2⟩ := (exists_mod_eq_half_and_dvd_iff h1).mpr h
      exact ⟨k, Or.inl ⟨hf, hk1, hk2⟩⟩
    · rw [Nat.gcd_comm] at h
      obtain ⟨k, hk1, hk2⟩ := (exists_mod_eq_half_and_dvd_iff h2).mpr h
      exact ⟨k, Or.inr ⟨hk2, hf, hk1⟩⟩

theorem parityL_conj_innerL (l : Lg) (M : SL2) : parityL (l * innerL M * l⁻¹) = 1 :=
  MonoidHom.mem_ker.mp ((MonoidHom.normal_ker parityL).conj_mem _
    (MonoidHom.mem_ker.mpr (parityL_innerL M)) l)

theorem inl1_range_normal : (inl1.range).Normal :=
  ⟨by
    rintro _ ⟨M, rfl⟩ g
    obtain ⟨M', hM'⟩ := exists_innerL_of_parityL_eq_one (parityL_conj_innerL g.1.1 M)
    exact ⟨M', Chat_ext hM'.symm (by simp)⟩⟩

theorem inr1_range_normal : (inr1.range).Normal :=
  ⟨by
    rintro _ ⟨M, rfl⟩ g
    obtain ⟨M', hM'⟩ := exists_innerL_of_parityL_eq_one (parityL_conj_innerL g.1.2 M)
    exact ⟨M', Chat_ext (by simp) hM'.symm⟩⟩

instance : K1q.Normal := Subgroup.Normal.map inl1_range_normal mkC mkC_surjective

instance : K2q.Normal := Subgroup.Normal.map inr1_range_normal mkC mkC_surjective

theorem orderOf_mkC_flags (c : ↥Chat) :
    orderOf (mkC c) =
      (let o := Nat.lcm (ordL c.1.1) (ordL c.1.2);
        if Even o ∧ (muFlag c.1.1 ∧ o / 2 % ordL c.1.1 = ordL c.1.1 / 2) ∧
            (muFlag c.1.2 ∧ o / 2 % ordL c.1.2 = ordL c.1.2 / 2)
          then o / 2 else o) := by
  rw [orderOf_mkC_components]
  simp only [pow_eq_innerL_minusOne_iff_muFlag]

theorem mkC_mem_Sset_iff (c : ↥Chat) :
    mkC c ∈ Sset zq K1q K2q ↔
      ((muFlag c.1.1 ∧ Nat.gcd (ordL c.1.1) (ordL c.1.2) ∣ ordL c.1.1 / 2) ∨
        (muFlag c.1.2 ∧ Nat.gcd (ordL c.1.1) (ordL c.1.2) ∣ ordL c.1.2 / 2)) ∨
      (3 ∣ ordL c.1.1 ∨ 3 ∣ ordL c.1.2) ∨
      (orderOf (mkC c) = 5 ∧
        ((parityL c.1.1 = 1 ∧ (c.1.2 = 1 ∨ c.1.2 = innerL minusOne)) ∨
          (parityL c.1.2 = 1 ∧ (c.1.1 = 1 ∨ c.1.1 = innerL minusOne)))) := by
  show (mkC c ∈ S2set zq ∨ mkC c ∈ S3set zq) ∨ mkC c ∈ S5set K1q K2q ↔ _
  rw [mkC_mem_S2set_iff_gcd, mkC_mem_S3set_iff, mkC_mem_S5set_iff, or_assoc]

theorem natCard_set_mkC (S : Set Cq) (Q : ↥Chat → Prop) (h : ∀ c, mkC c ∈ S ↔ Q c) :
    Nat.card S * 2 = Nat.card {c : ↥Chat // Q c} := by
  have h1 := natCard_subtype_mkC (fun x => x ∈ S)
  have h2 : Nat.card {c : ↥Chat // mkC c ∈ S} = Nat.card {c : ↥Chat // Q c} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  rw [← h2, h1, mul_comm]

end CFSG.GH74.GLS.Stage4.Q9
