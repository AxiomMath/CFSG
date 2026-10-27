module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L131b
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Grow

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {R : Type} [Group R]

theorem mem_zpowers_invol {c : R} (hcc : c * c = 1) {y : R} (hy : y ∈ zpowers c) :
    y = 1 ∨ y = c := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  rw [zpowers_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx => right; simpa using hx
  | one => left; rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · left; simp
    · right; simp
    · right; simp
    · left; exact hcc
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · left; simp
    · right; exact hci

theorem exp_two_comm (h : ∀ g : R, g * g = 1) (a b : R) : a * b = b * a := by
  have hi : ∀ g : R, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
  calc a * b = (a * b)⁻¹ := (hi _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hi, hi]

theorem exists_central_involution [Finite R] (hR : IsPGroup 2 R) (hnt : Nontrivial R) :
    ∃ c : R, c ∈ center R ∧ c ≠ 1 ∧ c * c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.center_nontrivial
  have hZ : IsPGroup 2 ↥(center R) := hR.to_subgroup _
  have hd : 2 ∣ Nat.card ↥(center R) := by
    rcases hZ.card_eq_or_dvd with h | h
    · exfalso
      have : Subsingleton ↥(center R) := Nat.card_eq_one_iff_unique.1 h |>.1
      exact not_subsingleton _ this
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center R)) 2 hd
  refine ⟨x.1, x.2, ?_, ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · have h2 : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hx])
    have := congrArg Subtype.val h2
    simpa [pow_two] using this

theorem centralizer_eq_four [Finite R] {z c : R} (hz1 : z ≠ 1) (hc1 : c ≠ 1) (hcz : c ≠ z)
    (hcc : c * c = 1) (hcard : Nat.card (centralizer ({z} : Set R)) ≤ 4)
    (hzc : z * c = c * z) (hzz : z * z = 1) :
    ∀ g ∈ centralizer ({z} : Set R), g = 1 ∨ g = z ∨ g = c ∨ g = z * c := by
  classical
  intro g hg
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hmem : ∀ a ∈ ({1, z, c, z * c, g} : Finset R), a ∈ centralizer ({z} : Set R) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · rw [mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]
    · rw [mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hzc
    · rw [mem_centralizer_iff]; intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]
      rw [mul_assoc, ← hzc]
    · exact hg
  have hcardF : ({1, z, c, z * c, g} : Finset R).card = 5 := by
    have e1 : (1 : R) ∉ ({z, c, z * c, g} : Finset R) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hz1.symm, hc1.symm, ?_, h1.symm⟩
      intro h
      have : z = c⁻¹ := eq_inv_of_mul_eq_one_left h.symm
      exact hcz (by rw [this, hci])
    have e2 : z ∉ ({c, z * c, g} : Finset R) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hcz.symm, ?_, h2.symm⟩
      intro h
      have : c = 1 := by
        have := congrArg (fun t => z⁻¹ * t) h
        simpa using this.symm
      exact hc1 this
    have e3 : c ∉ ({z * c, g} : Finset R) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, h3.symm⟩
      intro h
      have : z = 1 := by
        have := congrArg (fun t => t * c⁻¹) h
        simpa using this.symm
      exact hz1 this
    have e4 : z * c ∉ ({g} : Finset R) := by
      simp only [Finset.mem_singleton]
      exact h4.symm
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4, Finset.card_singleton]
  have hle : ({1, z, c, z * c, g} : Finset R).card ≤ Nat.card (centralizer ({z} : Set R)) := by
    have := Set.ncard_le_ncard (s := (({1, z, c, z * c, g} : Finset R) : Set R))
      (t := (centralizer ({z} : Set R) : Set R)) (fun a ha => hmem a (by simpa using ha))
      (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    rwa [← Nat.card_coe_set_eq] at this
  omega

theorem card_cent_quot_le [Finite R] (N : Subgroup R) [N.Normal] (z : R) :
    Nat.card (centralizer ({(QuotientGroup.mk z : R ⧸ N)} : Set (R ⧸ N))) ≤
      Nat.card (centralizer ({z} : Set R)) := by
  set Cq := centralizer ({(QuotientGroup.mk z : R ⧸ N)} : Set (R ⧸ N)) with hCq
  set D : Subgroup R := Cq.comap (QuotientGroup.mk' N) with hD
  have hmem : ∀ r : R, r ∈ D ↔ (QuotientGroup.mk r : R ⧸ N) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk r := by
    intro r
    show QuotientGroup.mk' N r ∈ Cq ↔ _
    rw [hCq, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hCle : centralizer ({z} : Set R) ≤ D := by
    intro g hg
    rw [hmem]
    have := mem_centralizer_iff.1 hg z rfl
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  have h1 : Nat.card D = Nat.card N * Nat.card Cq := by
    have e1 := Subgroup.card_mul_index D
    have e2 := Subgroup.card_mul_index Cq
    have e3 := Subgroup.index_comap_of_surjective Cq (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
    have e4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hi : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [← hD] at e3
    have : Nat.card D * D.index = Nat.card N * Nat.card Cq * D.index := by
      rw [e1, e4, ← e2, e3]; ring
    exact Nat.eq_of_mul_eq_mul_right hi this
  have h2 := card_cls_mul' D z
  have h3 : D ⊓ centralizer ({z} : Set R) = centralizer ({z} : Set R) := inf_eq_right.2 hCle
  rw [h3] at h2
  have hsub : cls D z ⊆ (fun n => z * n) '' (N : Set R) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' := (hmem r).1 hr
    refine ⟨z⁻¹ * (r * z * r⁻¹), ?_, by group⟩
    have : (QuotientGroup.mk (r * z * r⁻¹) : R ⧸ N) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hr', QuotientGroup.mk_inv]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have h5 := (QuotientGroup.eq).1 this.symm
    exact h5
  have h4 : Nat.card (cls D z) ≤ Nat.card N := by
    have a1 : Nat.card (cls D z) = (cls D z).ncard := (Nat.card_coe_set_eq _).symm
    have a2 : (cls D z).ncard ≤ ((fun n => z * n) '' (N : Set R)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have a3 : ((fun n => z * n) '' (N : Set R)).ncard ≤ (N : Set R).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have a4 : (N : Set R).ncard = Nat.card N := Nat.card_coe_set_eq _
    omega
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have h5 : Nat.card N * Nat.card Cq ≤ Nat.card N * Nat.card (centralizer ({z} : Set R)) := by
    calc Nat.card N * Nat.card Cq = Nat.card D := h1.symm
      _ = Nat.card (cls D z) * Nat.card (centralizer ({z} : Set R)) := h2.symm
      _ ≤ Nat.card N * Nat.card (centralizer ({z} : Set R)) := Nat.mul_le_mul_right _ h4
  exact Nat.le_of_mul_le_mul_left h5 hNpos


theorem exists_cyclic_index_two :
    ∀ (n : ℕ) (R : Type) [Group R] [Finite R], Nat.card R = n → IsPGroup 2 R →
      ∀ z : R, z * z = 1 → z ≠ 1 → Nat.card ↥(centralizer ({z} : Set R)) ≤ 4 → 8 ≤ n →
        ∃ a : R, orderOf a * 2 = n ∧ z ∉ zpowers a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ hn hR z hzz hz1 hcard hn8
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzc' : z ∉ center R := by
    intro hz
    have : centralizer ({z} : Set R) = ⊤ := by
      rw [centralizer_eq_top_iff_subset]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact hz
    rw [this, Subgroup.card_top] at hcard
    omega
  have hnt : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial]; omega
  obtain ⟨c, hcZ, hc1, hcc⟩ := exists_central_involution hR hnt
  have hcz : c ≠ z := fun h => hzc' (h ▸ hcZ)
  have hzc : z * c = c * z := (mem_center_iff.1 hcZ) z
  have hC4 := centralizer_eq_four hz1 hc1 hcz hcc hcard hzc hzz
  have hNn : (zpowers c).Normal := normal_of_le_center ((zpowers_le).2 hcZ)
  have hord2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1
  have hNcard : Nat.card (zpowers c) = 2 := by rw [Nat.card_zpowers, hord2]
  have hQcard : Nat.card (R ⧸ zpowers c) * 2 = n := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers c)
    rw [hNcard, hn] at this
    omega
  have hQ2 : IsPGroup 2 (R ⧸ zpowers c) := hR.to_quotient _
  have hzz' : (QuotientGroup.mk z : R ⧸ zpowers c) * QuotientGroup.mk z = 1 := by
    rw [← QuotientGroup.mk_mul, hzz, QuotientGroup.mk_one]
  have hzne : (QuotientGroup.mk z : R ⧸ zpowers c) ≠ 1 := by
    intro h
    rcases mem_zpowers_invol hcc ((QuotientGroup.eq_one_iff z).1 h) with h1 | h1
    · exact hz1 h1
    · exact hcz h1.symm
  have hQc : Nat.card ↥(centralizer ({(QuotientGroup.mk z : R ⧸ zpowers c)} : Set (R ⧸ zpowers c)))
      ≤ 4 := (card_cent_quot_le (zpowers c) z).trans hcard
  have hmkc : (QuotientGroup.mk c : R ⧸ zpowers c) = 1 :=
    (QuotientGroup.eq_one_iff c).2 (mem_zpowers c)
  by_cases hQ8 : 8 ≤ Nat.card (R ⧸ zpowers c)
  · obtain ⟨ā, hā, hzā⟩ := ih (Nat.card (R ⧸ zpowers c)) (by omega) (R ⧸ zpowers c) rfl hQ2 _ hzz'
      hzne hQc hQ8
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ā
    set m := orderOf (QuotientGroup.mk a : R ⧸ zpowers c) with hm
    have hmz : ∀ y : R, y ∈ zpowers a → (QuotientGroup.mk y : R ⧸ zpowers c) ∈
        zpowers (QuotientGroup.mk a : R ⧸ zpowers c) := by
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact mem_zpowers_iff.2 ⟨k, by rw [QuotientGroup.mk_zpow]⟩
    have ham : a ^ m ∈ zpowers c := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact pow_orderOf_eq_one _
    have hmdvd : m ∣ orderOf a := by
      have := orderOf_map_dvd (QuotientGroup.mk' (zpowers c)) a
      exact this
    have hmpos : 0 < m := by omega
    rcases mem_zpowers_invol hcc ham with h1 | h1
    ·
      exfalso
      have hmo : orderOf a = m := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1) hmdvd
      have hm4 : 4 ∣ m := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ2) (QuotientGroup.mk a)
        have hmm : m = 2 ^ k := hk
        have hge : 4 ≤ m := by omega
        have hk2 : 2 ≤ k := by
          by_contra hlt
          push Not at hlt
          have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [hmm]
        exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
      obtain ⟨m', hm'⟩ := hm4
      have hm'pos : 0 < m' := by omega
      have hee : (a ^ (2 * m')) * (a ^ (2 * m')) = 1 := by
        rw [← pow_add, show 2 * m' + 2 * m' = m by omega, ← hmo]
        exact pow_orderOf_eq_one a
      have he1 : a ^ (2 * m') ≠ 1 := by
        apply pow_ne_one_of_lt_orderOf (by omega)
        omega
      have hQcard' : Nat.card (R ⧸ zpowers c) = m * 2 := hā.symm
      have hind : (zpowers (QuotientGroup.mk a : R ⧸ zpowers c)).index = 2 := by
        have h := Subgroup.card_mul_index (zpowers (QuotientGroup.mk a : R ⧸ zpowers c))
        rw [Nat.card_zpowers, ← hm, hQcard'] at h
        exact Nat.eq_of_mul_eq_mul_left hmpos h
      have hQn : (zpowers (QuotientGroup.mk a : R ⧸ zpowers c)).Normal :=
        normal_of_index_eq_two hind
      have hu := hQn.conj_mem (QuotientGroup.mk a) (mem_zpowers _) (QuotientGroup.mk z)
      obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hu
      have hν : (a ^ i)⁻¹ * (z * a * z⁻¹) ∈ zpowers c := by
        apply QuotientGroup.eq.1
        rw [QuotientGroup.mk_zpow, hi, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
      set ν := (a ^ i)⁻¹ * (z * a * z⁻¹) with hνdef
      have hzaz : z * a * z⁻¹ = a ^ i * ν := by rw [hνdef, mul_inv_cancel_left]
      have hνcomm : Commute (a ^ i) ν := by
        rcases mem_zpowers_invol hcc hν with h | h
        · rw [h]; exact Commute.one_right _
        · rw [h]; exact (mem_center_iff.1 hcZ) (a ^ i)
      have hν2 : ν ^ (2 * m') = 1 := by
        rcases mem_zpowers_invol hcc hν with h | h
        · rw [h]; exact one_pow _
        · rw [h, pow_mul, pow_two, hcc, one_pow]
      have hconj : z * a ^ (2 * m') * z⁻¹ = (a ^ (2 * m')) ^ i := by
        calc z * a ^ (2 * m') * z⁻¹ = (z * a * z⁻¹) ^ (2 * m') := conj_pow.symm
          _ = (a ^ i * ν) ^ (2 * m') := by rw [hzaz]
          _ = (a ^ i) ^ (2 * m') * ν ^ (2 * m') := hνcomm.mul_pow _
          _ = (a ^ i) ^ (2 * m') := by rw [hν2, mul_one]
          _ = (a ^ (2 * m')) ^ i := by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have hei : (a ^ (2 * m')) ^ i = 1 ∨ (a ^ (2 * m')) ^ i = a ^ (2 * m') :=
        mem_zpowers_invol hee (mem_zpowers_iff.2 ⟨i, rfl⟩)
      have hfix : z * a ^ (2 * m') * z⁻¹ = a ^ (2 * m') := by
        rcases hei with h | h
        · exfalso
          apply he1
          have h2 : z * a ^ (2 * m') * z⁻¹ = 1 := hconj.trans h
          have h3 : z * a ^ (2 * m') = z := mul_inv_eq_one.1 h2
          exact mul_eq_left.1 h3
        · rw [hconj]; exact h
      have hcent : a ^ (2 * m') ∈ centralizer ({z} : Set R) := by
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact mul_inv_eq_iff_eq_mul.1 hfix
      rcases hC4 _ hcent with h | h | h | h
      · exact he1 h
      · apply hzā
        apply hmz
        exact mem_zpowers_iff.2 ⟨(2 * m' : ℕ), by rw [zpow_natCast]; exact h⟩
      ·
        have h2 : (QuotientGroup.mk a : R ⧸ zpowers c) ^ (2 * m') = 1 := by
          rw [← QuotientGroup.mk_pow, h, hmkc]
        have h3 : m ∣ 2 * m' := orderOf_dvd_of_pow_eq_one h2
        have := Nat.le_of_dvd (by omega) h3
        omega
      · apply hzā
        have hzE : z = a ^ (2 * m') * c := by
          rw [h]
          calc z = z * (c * c) := by rw [hcc, mul_one]
            _ = z * c * c := by rw [mul_assoc]
        have : (QuotientGroup.mk z : R ⧸ zpowers c) = QuotientGroup.mk (a ^ (2 * m')) := by
          rw [hzE, QuotientGroup.mk_mul, hmkc, mul_one]
        rw [this]
        apply hmz
        exact mem_zpowers_iff.2 ⟨(2 * m' : ℕ), by rw [zpow_natCast]⟩
    ·
      have hdvd2 : orderOf a ∣ m * 2 := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_mul, h1, pow_two, hcc]
      obtain ⟨t, ht⟩ := hmdvd
      have ht2 : t ∣ 2 := by
        have : m * t ∣ m * 2 := by rw [← ht]; exact hdvd2
        exact Nat.dvd_of_mul_dvd_mul_left hmpos this
      rcases (Nat.dvd_prime Nat.prime_two).1 ht2 with rfl | rfl
      · exfalso
        have : a ^ m = 1 := by
          have h3 : a ^ orderOf a = 1 := pow_orderOf_eq_one a
          rw [ht, mul_one] at h3
          exact h3
        rw [this] at h1
        exact hc1 h1.symm
      · refine ⟨a, by rw [ht]; omega, ?_⟩
        intro hza
        exact hzā (hmz z hza)
  ·
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    have hn8' : n = 8 := by
      have h1 : 8 ≤ 2 ^ k := by omega
      have h2 : 2 ^ k < 16 := by omega
      have h3 : k = 3 := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      rw [← hn, hk, h3]; norm_num
    have hle2 : ∀ g : R, g * g = 1 → orderOf g ≤ 2 := by
      intro g hg
      have : g ^ 2 = 1 := by rw [pow_two]; exact hg
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
    have hexa : ∃ a : R, orderOf a = 4 := by
      by_contra hno
      push Not at hno
      have hcomm : ∀ a b : R, a * b = b * a := by
        by_cases h8 : ∃ a : R, orderOf a = 8
        · obtain ⟨a, ha⟩ := h8
          have : IsCyclic R := isCyclic_of_orderOf_eq_card a (by rw [ha, hn, hn8'])
          intro x y
          exact (IsCyclic.isMulCommutative (α := R)).is_comm.comm x y
        · push Not at h8
          apply exp_two_comm
          intro g
          obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hR) g
          have hdvd : orderOf g ∣ 8 := by rw [← hn8', ← hn]; exact orderOf_dvd_natCard g
          have hj3 : 2 ^ j ≤ 8 := by rw [← hj]; exact Nat.le_of_dvd (by norm_num) hdvd
          have hj3' : j ≤ 3 := by
            by_contra hgt
            push Not at hgt
            have : 2 ^ 4 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          interval_cases j
          · have : g = 1 := by rw [← orderOf_eq_one_iff, hj]; rfl
            rw [this]; simp
          · have : g ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hj]; norm_num)
            rw [pow_two] at this; exact this
          · exact absurd (by rw [hj]; norm_num : orderOf g = 4) (hno g)
          · exact absurd (by rw [hj]; norm_num : orderOf g = 8) (h8 g)
      exact hzc' (mem_center_iff.2 (fun g => hcomm g z))
    obtain ⟨a, ha⟩ := hexa
    refine ⟨a, by omega, ?_⟩
    intro hza
    have hac : a ∈ centralizer ({z} : Set R) := by
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hza
      exact (Commute.self_zpow a k).symm.eq
    have hzcc : (z * c) * (z * c) = 1 := by
      calc (z * c) * (z * c) = z * (c * z) * c := by group
        _ = z * (z * c) * c := by rw [← hzc]
        _ = (z * z) * (c * c) := by group
        _ = 1 := by rw [hzz, hcc, one_mul]
    rcases hC4 a hac with h | h | h | h
    · rw [h, orderOf_one] at ha; omega
    · have := hle2 z hzz; rw [h] at ha; omega
    · have := hle2 c hcc; rw [h] at ha; omega
    · have := hle2 _ hzcc; rw [h] at ha; omega

section
variable {G : Type*} [Group G]
theorem card_le_cent_sq [Finite G] {K : Subgroup G} (hKsq : ∀ k ∈ K, k * k = 1)
    (hKc : ∀ k ∈ K, ∀ l ∈ K, k * l = l * k) {y : G} (hy : y * y = 1)
    (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) :
    Nat.card K ≤ Nat.card ↥(K ⊓ centralizer ({y} : Set G)) ^ 2 := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hinv : ∀ k ∈ K, k⁻¹ = k := fun k hk => inv_eq_of_mul_eq_one_right (hKsq k hk)
  let φ : ↥K →* ↥K :=
    { toFun := fun k => k * ⟨y * k * y⁻¹, hyK k k.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro k l
        apply Subtype.ext
        show (k : G) * l * (y * ((k : G) * l) * y⁻¹) =
          ((k : G) * (y * k * y⁻¹)) * ((l : G) * (y * l * y⁻¹))
        have h1 : (l : G) * (y * k * y⁻¹) = (y * k * y⁻¹) * l := hKc _ l.2 _ (hyK k k.2)
        calc (k : G) * l * (y * ((k : G) * l) * y⁻¹)
            = k * (l * (y * k * y⁻¹)) * (y * l * y⁻¹) := by group
          _ = k * ((y * k * y⁻¹) * l) * (y * l * y⁻¹) := by rw [h1]
          _ = ((k : G) * (y * k * y⁻¹)) * ((l : G) * (y * l * y⁻¹)) := by group }
  set Cy : Subgroup ↥K := (K ⊓ centralizer ({y} : Set G)).subgroupOf K with hCy
  have hmemCy : ∀ k : ↥K, k ∈ Cy ↔ y * k * y⁻¹ = k := by
    intro k
    rw [hCy, mem_subgroupOf]
    constructor
    · rintro ⟨-, hc⟩
      have := mem_centralizer_iff.1 hc y rfl
      calc y * (k : G) * y⁻¹ = (k * y) * y⁻¹ := by rw [this]
        _ = k := by group
    · intro h
      refine ⟨k.2, ?_⟩
      show (k : G) ∈ centralizer ({y} : Set G)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      calc y * (k : G) = (y * k * y⁻¹) * y := by group
        _ = k * y := by rw [h]
  have hker : φ.ker = Cy := by
    ext k
    rw [MonoidHom.mem_ker, hmemCy]
    constructor
    · intro h
      have h' : (k : G) * (y * k * y⁻¹) = 1 := congrArg Subtype.val h
      have : y * (k : G) * y⁻¹ = (k : G)⁻¹ := eq_inv_of_mul_eq_one_right h'
      rw [this]; exact hinv _ k.2
    · intro h
      apply Subtype.ext
      show (k : G) * (y * k * y⁻¹) = 1
      rw [h]; exact hKsq _ k.2
  have hrange : φ.range ≤ Cy := by
    rintro _ ⟨k, rfl⟩
    rw [hmemCy]
    show y * ((k : G) * (y * k * y⁻¹)) * y⁻¹ = (k : G) * (y * k * y⁻¹)
    have h1 : (y * k * y⁻¹) * k = (k : G) * (y * k * y⁻¹) := hKc _ (hyK k k.2) _ k.2
    calc y * ((k : G) * (y * k * y⁻¹)) * y⁻¹ = (y * k * y⁻¹) * (y * (y * k * y⁻¹) * y⁻¹) := by group
      _ = (y * k * y⁻¹) * ((y * y) * k * (y * y)⁻¹) := by group
      _ = (y * k * y⁻¹) * k := by rw [hy]; group
      _ = (k : G) * (y * k * y⁻¹) := h1
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hc1 : Nat.card φ.range ≤ Nat.card Cy := Subgroup.card_le_of_le hrange
  have hc2 : Nat.card Cy = Nat.card ↥(K ⊓ centralizer ({y} : Set G)) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker] at h1
  calc Nat.card K = Nat.card Cy * Nat.card φ.range := h1.symm
    _ ≤ Nat.card Cy * Nat.card Cy := Nat.mul_le_mul_left _ hc1
    _ = Nat.card Cy ^ 2 := (pow_two _).symm
    _ = Nat.card ↥(K ⊓ centralizer ({y} : Set G)) ^ 2 := by rw [hc2]

end

theorem two_group_klein [Finite R] (hR : IsPGroup 2 R) {z : R} (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hC : Nat.card ↥(centralizer ({z} : Set R)) ≤ 4) (K : Subgroup R) [hKn : K.Normal]
    (hKsq : ∀ k ∈ K, k * k = 1) (hKc : ∀ k ∈ K, ∀ l ∈ K, k * l = l * k)
    (hKz : ∃ k ∈ K, z * k ≠ k * z) :
    z ∉ K ∧ Nat.card K = 4 ∧ (∀ r : R, r ∈ K ∨ r * z ∈ K) ∧
      Nat.card ↥(K ⊓ centralizer ({z} : Set R)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hKi : ∀ k ∈ K, k⁻¹ = k := fun k hk => inv_eq_of_mul_eq_one_right (hKsq k hk)
  have hzK : z ∉ K := by
    intro hz
    obtain ⟨k, hk, hne⟩ := hKz
    exact hne (hKc z hz k hk)
  have hKbot : K ≠ ⊥ := by
    intro h
    obtain ⟨k, hk, hne⟩ := hKz
    rw [h, Subgroup.mem_bot] at hk
    apply hne; rw [hk]; simp
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hKbot
  obtain ⟨⟨c, hcmem⟩, hc1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hcen
  obtain ⟨hcK, hcZ⟩ := hcmem
  have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
  have hcc : c * c = 1 := hKsq c hcK
  have hcz : c ≠ z := fun h => hzK (h ▸ hcK)
  have hzc : z * c = c * z := (mem_center_iff.1 hcZ) z
  have hC4 := centralizer_eq_four hz1 hc1 hcz hcc hC hzc hzz
  have hKC : K ⊓ centralizer ({z} : Set R) = zpowers c := by
    ext g
    constructor
    · rintro ⟨hgK, hgC⟩
      rcases hC4 g hgC with h | h | h | h
      · rw [h]; exact one_mem _
      · exact absurd (h ▸ hgK) hzK
      · rw [h]; exact mem_zpowers c
      · exfalso
        apply hzK
        have : z = g * c := by rw [h, mul_assoc, hcc, mul_one]
        rw [this]
        exact K.mul_mem hgK hcK
    · intro hg
      have hcC : c ∈ centralizer ({z} : Set R) := by
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]; exact hzc
      rcases mem_zpowers_invol hcc hg with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact ⟨hcK, hcC⟩
  have hord2 : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1
  have hcard2 : Nat.card ↥(K ⊓ centralizer ({z} : Set R)) = 2 := by
    rw [hKC, Nat.card_zpowers, hord2]
  have hyK : ∀ k ∈ K, z * k * z⁻¹ ∈ K := fun k hk => hKn.conj_mem k hk z
  have hKle : Nat.card K ≤ 4 := by
    have := card_le_cent_sq hKsq hKc hzz hyK
    rw [hcard2] at this
    simpa using this
  obtain ⟨k₀, hk₀K, hk₀⟩ := hKz
  have hlt : K ⊓ centralizer ({z} : Set R) < K := by
    refine lt_of_le_of_ne inf_le_left (fun h => hk₀ ?_)
    have : k₀ ∈ K ⊓ centralizer ({z} : Set R) := by rw [h]; exact hk₀K
    exact mem_centralizer_iff.1 this.2 z rfl
  have hKcard : Nat.card K = 4 := by
    have hc := Subgroup.card_lt_of_lt hlt
    rw [hcard2] at hc
    obtain ⟨j, hj⟩ := (hR.to_subgroup K).exists_card_eq
    rw [hj] at hc hKle ⊢
    have : j = 2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [this]; norm_num
  have hk₀c : z * k₀ * z⁻¹ = c * k₀ := by
    set k' := z * k₀ * z⁻¹ with hk'
    have hk'K : k' ∈ K := hyK k₀ hk₀K
    have hu : k' * k₀⁻¹ ∈ K ⊓ centralizer ({z} : Set R) := by
      refine ⟨K.mul_mem hk'K (K.inv_mem hk₀K), ?_⟩
      show k' * k₀⁻¹ ∈ centralizer ({z} : Set R)
      rw [mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have e1 : z * k' * z⁻¹ = k₀ := by
        rw [hk']
        calc z * (z * k₀ * z⁻¹) * z⁻¹ = (z * z) * k₀ * (z⁻¹ * z⁻¹) := by group
          _ = k₀ := by rw [hzz, hzi, hzz]; group
      have e2 : z * (k' * k₀⁻¹) * z⁻¹ = k₀ * (z * k₀⁻¹ * z⁻¹) := by
        calc z * (k' * k₀⁻¹) * z⁻¹ = (z * k' * z⁻¹) * (z * k₀⁻¹ * z⁻¹) := by group
          _ = k₀ * (z * k₀⁻¹ * z⁻¹) := by rw [e1]
      have e3 : z * k₀⁻¹ * z⁻¹ = k' := by
        rw [hk', hKi k₀ hk₀K]
      have e4 : z * (k' * k₀⁻¹) * z⁻¹ = k' * k₀⁻¹ := by
        rw [e2, e3, hKi k₀ hk₀K]
        exact hKc _ hk₀K _ hk'K
      exact (mul_inv_eq_iff_eq_mul.1 e4)
    rw [hKC] at hu
    rcases mem_zpowers_invol hcc hu with h | h
    · exfalso
      have : k' = k₀ := by
        have := mul_inv_eq_one.1 h
        exact this
      apply hk₀
      have : z * k₀ * z⁻¹ = k₀ := this
      exact mul_inv_eq_iff_eq_mul.1 this
    · have : k' = c * k₀ := by
        calc k' = (k' * k₀⁻¹) * k₀ := by group
          _ = c * k₀ := by rw [h]
      exact this
  have hD : K ⊔ zpowers z = ⊤ := by
    by_contra hD
    have hlt' : K ⊔ zpowers z < ⊤ := lt_top_iff_ne_top.2 hD
    obtain ⟨n, -, hnD, hnN⟩ := exists_mem_normalizer_not_mem (hR.to_subgroup ⊤) hlt'
    have hzD : z ∈ K ⊔ zpowers z := Subgroup.mem_sup_right (mem_zpowers z)
    have hwD : n * z * n⁻¹ ∈ K ⊔ zpowers z := (mem_normalizer_iff.1 hnN z).1 hzD
    have hKD : K ≤ K ⊔ zpowers z := le_sup_left
    have hcD : c ∈ K ⊔ zpowers z := hKD hcK
    have hCD : ∀ m, m * z = z * m → m ∈ K ⊔ zpowers z := by
      intro m hm
      have hmC : m ∈ centralizer ({z} : Set R) := by
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]; exact hm.symm
      rcases hC4 m hmC with h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact hzD
      · rw [h]; exact hcD
      · rw [h]; exact (K ⊔ zpowers z).mul_mem hzD hcD
    obtain ⟨q, hqK, hw | hw⟩ := (mem_sup_zpowers_invol hzz hyK).1 hwD
    · apply hzK
      have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
      rw [this, hw]
      have := hKn.conj_mem q hqK n⁻¹
      simpa using this
    · have hw2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
        calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
          _ = 1 := by rw [hzz]; group
      rw [hw] at hw2
      have hqC : z * q = q * z := by
        have h1 : z * q * z = q⁻¹ := by
          have : q * z * (q * z) = 1 := hw2
          have h3 : q * (z * q * z) = 1 := by
            calc q * (z * q * z) = q * z * (q * z) := by group
              _ = 1 := this
          exact eq_inv_of_mul_eq_one_right h3
        rw [hKi q hqK] at h1
        calc z * q = z * q * z * z := by rw [mul_assoc (z * q) z z, hzz, mul_one]
          _ = q * z := by rw [h1]
      have hqKC : q ∈ K ⊓ centralizer ({z} : Set R) := by
        refine ⟨hqK, ?_⟩
        show q ∈ centralizer ({z} : Set R)
        rw [mem_centralizer_iff]
        intro w hw'
        rw [Set.mem_singleton_iff] at hw'
        rw [hw']; exact hqC
      rw [hKC] at hqKC
      rcases mem_zpowers_invol hcc hqKC with hq | hq
      · apply hnD
        apply (hCD n)
        have : n * z * n⁻¹ = z := by rw [hw, hq]; group
        calc n * z = (n * z * n⁻¹) * n := by group
          _ = z * n := by rw [this]
      · apply hnD
        have hm : (k₀ * n) * z = z * (k₀ * n) := by
          have hz2 : n * z * n⁻¹ = c * z := by rw [hw, hq]
          have hk0z : k₀ * z * k₀⁻¹ = c * z := by
            have e1 : z * k₀ = c * k₀ * z := by
              calc z * k₀ = (z * k₀ * z⁻¹) * z := by group
                _ = c * k₀ * z := by rw [hk₀c]
            have e2 : k₀ * z * k₀ = c * z := by
              calc k₀ * z * k₀ = k₀ * (z * k₀) := by group
                _ = k₀ * (c * k₀ * z) := by rw [e1]
                _ = c * (k₀ * k₀) * z := by
                  have hcomm := (mem_center_iff.1 hcZ) k₀
                  calc k₀ * (c * k₀ * z) = (k₀ * c) * k₀ * z := by group
                    _ = (c * k₀) * k₀ * z := by rw [hcomm]
                    _ = c * (k₀ * k₀) * z := by group
                _ = c * z := by rw [hKsq k₀ hk₀K, mul_one]
            rw [hKi k₀ hk₀K]; exact e2
          have : k₀ * n * z * (k₀ * n)⁻¹ = z := by
            calc k₀ * n * z * (k₀ * n)⁻¹ = k₀ * (n * z * n⁻¹) * k₀⁻¹ := by group
              _ = k₀ * (c * z) * k₀⁻¹ := by rw [hz2]
              _ = c * (k₀ * z * k₀⁻¹) := by
                have hcomm := (mem_center_iff.1 hcZ) k₀
                calc k₀ * (c * z) * k₀⁻¹ = (k₀ * c) * (z * k₀⁻¹) := by group
                  _ = (c * k₀) * (z * k₀⁻¹) := by rw [hcomm]
                  _ = c * (k₀ * z * k₀⁻¹) := by group
              _ = c * (c * z) := by rw [hk0z]
              _ = z := by rw [← mul_assoc, hcc, one_mul]
          calc k₀ * n * z = (k₀ * n * z * (k₀ * n)⁻¹) * (k₀ * n) := by group
            _ = z * (k₀ * n) := by rw [this]
        have := hCD _ hm
        have e : n = k₀⁻¹ * (k₀ * n) := by group
        rw [e]
        exact (K ⊔ zpowers z).mul_mem ((K ⊔ zpowers z).inv_mem (hKD hk₀K)) this
  refine ⟨hzK, hKcard, ?_, hcard2⟩
  intro r
  have hr : r ∈ K ⊔ zpowers z := by rw [hD]; exact mem_top r
  obtain ⟨q, hqK, h | h⟩ := (mem_sup_zpowers_invol hzz hyK).1 hr
  · exact Or.inl (h ▸ hqK)
  · right
    have : r * z = q := by rw [h, mul_assoc, hzz, mul_one]
    rw [this]; exact hqK

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
