module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma45Sylow
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoGroup

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

section Suzuki

variable {R : Type} [Group R]

private theorem mem_zpowers_invol {c : R} (hcc : c * c = 1) {y : R} (hy : y ∈ zpowers c) :
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

private theorem exp_two_comm (h : ∀ g : R, g * g = 1) (a b : R) : a * b = b * a := by
  have hi : ∀ g : R, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
  calc a * b = (a * b)⁻¹ := (hi _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hi, hi]

private theorem exists_central_involution' [Finite R] (hR : IsPGroup 2 R) (hnt : Nontrivial R) :
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

private theorem centralizer_eq_four [Finite R] {z c : R} (hz1 : z ≠ 1) (hc1 : c ≠ 1)
    (hcz : c ≠ z) (hcc : c * c = 1) (hcard : Nat.card (centralizer ({z} : Set R)) ≤ 4)
    (hzc : z * c = c * z) :
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

private def cls (M : Subgroup R) (x : R) : Set R := {y | ∃ m ∈ M, y = m * x * m⁻¹}

private theorem card_cls_mul [Finite R] (M : Subgroup R) (x : R) :
    Nat.card (cls M x) * Nat.card ↥(M ⊓ centralizer ({x} : Set R)) = Nat.card M := by
  let _inst : MulAction ↥M R := MulAction.compHom R ((MulAut.conj : R →* MulAut R).comp M.subtype)
  have hsm : ∀ (m : ↥M) (g : R), m • g = (m : R) * g * (m : R)⁻¹ := fun m g => rfl
  have h1 : (MulAction.orbit (↥M) x) = cls M x := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, hsm m x⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, (hsm ⟨m, hm⟩ x).symm⟩
  have h2 : Nat.card (MulAction.stabilizer (↥M) x) =
      Nat.card ↥(M ⊓ centralizer ({x} : Set R)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, ?_⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun d => rfl }
    · have hs : (s.1 : ↥M) • x = x := s.2
      rw [hsm] at hs
      show s.1.1 ∈ centralizer ({x} : Set R)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have : (s.1.1 : R) * x * (s.1.1 : R)⁻¹ = x := hs
      calc x * (s.1.1 : R) = ((s.1.1 : R) * x * (s.1.1 : R)⁻¹) * s.1.1 := by rw [this]
        _ = s.1.1 * x := by group
    · show (⟨d.1, d.2.1⟩ : ↥M) • x = x
      rw [hsm]
      have := mem_centralizer_iff.1 d.2.2 x rfl
      show d.1 * x * d.1⁻¹ = x
      calc d.1 * x * d.1⁻¹ = (d.1 * x) * d.1⁻¹ := rfl
        _ = (x * d.1) * d.1⁻¹ := by rw [← this]
        _ = x := by group
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (↥M) x)
  have h4 : Nat.card (MulAction.orbit (↥M) x) = Nat.card (↥M ⧸ MulAction.stabilizer (↥M) x) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥M) x)
  rw [h1] at h4
  rw [h4, h2] at *
  exact h3.symm

private theorem card_cent_quot_le [Finite R] (N : Subgroup R) [N.Normal] (z : R) :
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
  have h2 := card_cls_mul D z
  have h3 : D ⊓ centralizer ({z} : Set R) = centralizer ({z} : Set R) := inf_eq_right.2 hCle
  rw [h3] at h2
  have hsub : cls D z ⊆ (fun n => z * n) '' (N : Set R) := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' := (hmem r).1 hr
    refine ⟨z⁻¹ * (r * z * r⁻¹), ?_, by group⟩
    have : (QuotientGroup.mk (r * z * r⁻¹) : R ⧸ N) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hr', QuotientGroup.mk_inv]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    exact (QuotientGroup.eq).1 this.symm
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

theorem exists_cyclic_index_two_of_card_le_four :
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
  obtain ⟨c, hcZ, hc1, hcc⟩ := exists_central_involution' hR hnt
  have hcz : c ≠ z := fun h => hzc' (h ▸ hcZ)
  have hzc : z * c = c * z := (mem_center_iff.1 hcZ) z
  have hC4 := centralizer_eq_four hz1 hc1 hcz hcc hcard hzc
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
  have hQc : Nat.card ↥(centralizer ({(QuotientGroup.mk z : R ⧸ zpowers c)} :
      Set (R ⧸ zpowers c))) ≤ 4 := (card_cent_quot_le (zpowers c) z).trans hcard
  have hmkc : (QuotientGroup.mk c : R ⧸ zpowers c) = 1 :=
    (QuotientGroup.eq_one_iff c).2 (mem_zpowers c)
  by_cases hQ8 : 8 ≤ Nat.card (R ⧸ zpowers c)
  · obtain ⟨ā, hā, hzā⟩ := ih (Nat.card (R ⧸ zpowers c)) (by omega) (R ⧸ zpowers c) rfl hQ2 _
      hzz' hzne hQc hQ8
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

end Suzuki

variable {G : Type} [Group G] [Finite G]

theorem eight_le_card_inf_centralizer {T : Subgroup G} (hT : IsPGroup 2 T) {F : Subgroup G}
    (hFT : F ≤ T) (hF2 : ∀ x ∈ F, x ^ 2 = 1) (hF8 : Nat.card F = 8) {x : G} (hxT : x ∈ T)
    (hx : orderOf x = 2) : 8 ≤ Nat.card ↥(T ⊓ centralizer ({x} : Set G)) := by
  by_contra hlt
  push Not at hlt
  have hp : IsPGroup 2 ↥(T ⊓ centralizer ({x} : Set G)) := hT.to_le inf_le_left
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hle4 : Nat.card ↥(T ⊓ centralizer ({x} : Set G)) ≤ 4 := by
    rw [hk] at hlt ⊢
    have hk2 : k ≤ 2 := by
      by_contra h
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hT8 : 8 ≤ Nat.card T := hF8 ▸ Subgroup.card_le_of_le hFT
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxx : (⟨x, hxT⟩ : T) * ⟨x, hxT⟩ = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
    exact hx2)
  have hx1 : (⟨x, hxT⟩ : T) ≠ 1 := fun h => by
    have h1 : x = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hx
    omega
  have hc : Nat.card (centralizer ({(⟨x, hxT⟩ : T)} : Set T)) ≤ 4 := by
    have e : (centralizer ({(⟨x, hxT⟩ : T)} : Set T)).map T.subtype =
        T ⊓ centralizer ({x} : Set G) := by
      ext y
      simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨⟨y, hyT⟩, hy, rfl⟩
        exact ⟨hyT, congrArg Subtype.val hy⟩
      · rintro ⟨hyT, hy⟩
        exact ⟨⟨y, hyT⟩, Subtype.ext hy, rfl⟩
    rw [← Subgroup.card_map_of_injective T.subtype_injective, e]
    exact hle4
  obtain ⟨a, ha, -⟩ := exists_cyclic_index_two_of_card_le_four (Nat.card T) T rfl hT
    ⟨x, hxT⟩ hxx hx1 hc hT8
  have hind : (zpowers a).index ≤ 2 := by
    have h1 := (zpowers a).card_mul_index
    rw [Nat.card_zpowers, ← ha] at h1
    have hpos : 0 < orderOf a := orderOf_pos a
    have h2 : (zpowers a).index = 2 := Nat.eq_of_mul_eq_mul_left hpos h1
    omega
  have hrank := CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound
    (H := zpowers a) inferInstance hind
  have hF : CFSG.Open.IsElemAbelian 2 (F.subgroupOf T) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one hF2 a.2 b.2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hF2 _ ha
  have hFcard : Nat.card (F.subgroupOf T) = 2 ^ 3 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hFT).symm.toEquiv, hF8]
    norm_num
  have h3 := SectionRank.le_pRank one_lt_two (le_top : F.subgroupOf T ≤ ⊤) hF hFcard
  rw [← SectionRank.pRank_eq_open_pRank_top] at h3
  omega

omit [Finite G] in
theorem eq_or_eq_or_eq_of_cover {Q Q₀ : Subgroup G} {t z : G} (htt : t * t = 1)
    (hQt : Q ≤ centralizer ({t} : Set G)) (hzt : z * t = t * z)
    (hcover : ∀ x ∈ Q, x ∈ Q₀ ∨ x * t ∈ Q₀) (huniq : ∀ x ∈ Q₀, orderOf x = 2 → x = z)
    {x : G} (hxQ : x ∈ Q) (hx : orderOf x = 2) : x = z ∨ x = t ∨ x = t * z := by
  have hx2 : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  rcases hcover x hxQ with h | h
  · exact Or.inl (huniq x h hx)
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (hQt hxQ)
  have hyy : (x * t) * (x * t) = 1 := by
    calc (x * t) * (x * t) = x * (t * x) * t := by group
      _ = x * (x * t) * t := by rw [← hxt]
      _ = (x * x) * (t * t) := by group
      _ = 1 := by rw [hx2, htt, one_mul]
  have hxe : x = (x * t) * t := by
    calc x = x * (t * t) := by rw [htt, mul_one]
      _ = (x * t) * t := (mul_assoc _ _ _).symm
  by_cases hy1 : x * t = 1
  · right; left
    rw [hxe, hy1, one_mul]
  · right; right
    have hyo : orderOf (x * t) = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    rw [hxe, huniq _ h hyo, hzt]

structure TwoData (T : Subgroup G) (t z : G) (Q₀ : Subgroup G) : Prop where
  hz : orderOf z = 2
  hzT : z ∈ T
  hzc : ∀ x ∈ T, x * z = z * x
  hzZ : ∀ x ∈ T, orderOf x = 2 → (∀ y ∈ T, x * y = y * x) → x = z
  hQ₀ : Q₀ ≤ T ⊓ centralizer ({t} : Set G)
  hzQ₀ : z ∈ Q₀
  htQ₀ : t ∉ Q₀
  hcover : ∀ x ∈ T ⊓ centralizer ({t} : Set G), x ∈ Q₀ ∨ x * t ∈ Q₀
  huniq : ∀ x ∈ Q₀, orderOf x = 2 → x = z
  hroot : ∃ x₀ ∈ Q₀, x₀ ^ 2 = z
  hn : ∃ n ∈ T, n ∈ normalizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ∧
    n * t * n⁻¹ = t * z

theorem exists_twoData {T : Subgroup G} (hT : IsPGroup 2 T) {E : Subgroup G} (hET : E ≤ T)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) {t : G} (htT : t ∈ T)
    (ht : orderOf t = 2)
    (hQ : ∀ F : Subgroup G, F ≤ T ⊓ centralizer ({t} : Set G) → (∀ x ∈ F, x ^ 2 = 1) →
      Nat.card F ≠ 8) :
    ∃ z : G, ∃ Q₀ : Subgroup G, TwoData T t z Q₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  obtain ⟨U, hU, hUT, hTU, u₁, hu₁U, hu₁1, hu₁c⟩ := exists_normal_four_le hT hET hE2 hE8
  obtain ⟨u₂, hu₂U, hu₂1, hu₂₁⟩ := exists_ne_of_isKleinFour hU u₁
  have hu₁2 : u₁ ^ 2 = 1 := sq_eq_one_of_isKleinFour hU hu₁U
  have hu₁u₁ : u₁ * u₁ = 1 := by rw [← sq]; exact hu₁2
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    commute_of_sq_eq_one (fun x hx => sq_eq_one_of_isKleinFour hU hx) ha hb
  have hconj : ∀ x ∈ T, x * u₂ * x⁻¹ = u₂ ∨ x * u₂ * x⁻¹ = u₁ * u₂ := by
    intro x hx
    have hmem : x * u₂ * x⁻¹ ∈ U := (mem_normalizer_iff.mp (hTU hx) u₂).mp hu₂U
    rcases mem_of_isKleinFour hU hu₁U hu₂U hmem hu₁1 hu₂1 hu₂₁.symm with h | h | h | h
    · exfalso
      apply hu₂1
      calc u₂ = x⁻¹ * (x * u₂ * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exfalso
      apply hu₂₁
      calc u₂ = x⁻¹ * (x * u₂ * x⁻¹) * x := by group
        _ = x⁻¹ * (u₁ * x) := by rw [h, mul_assoc]
        _ = u₁ := by rw [← hu₁c x hx, inv_mul_cancel_left]
    · exact Or.inl h
    · exact Or.inr h
  have hCU : ∀ x ∈ T, x * u₂ = u₂ * x → x ∈ centralizer (U : Set G) := by
    intro x hx hxu
    rw [mem_centralizer_iff]
    intro y hy
    rcases mem_of_isKleinFour hU hu₁U hu₂U hy hu₁1 hu₂1 hu₂₁.symm with rfl | rfl | rfl | rfl
    · simp
    · exact (hu₁c x hx).symm
    · exact hxu.symm
    · calc u₁ * u₂ * x = u₁ * (u₂ * x) := mul_assoc _ _ _
        _ = u₁ * (x * u₂) := by rw [← hxu]
        _ = (u₁ * x) * u₂ := (mul_assoc _ _ _).symm
        _ = (x * u₁) * u₂ := by rw [← hu₁c x hx]
        _ = x * (u₁ * u₂) := mul_assoc _ _ _
  have hfix : ∀ x : G, x * u₂ * x⁻¹ = u₂ → x * u₂ = u₂ * x := fun x h => by
    calc x * u₂ = x * u₂ * x⁻¹ * x := by group
      _ = u₂ * x := by rw [h]
  have htCt : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have htU : t * u₂ * t⁻¹ = u₁ * u₂ := by
    rcases hconj t htT with h | h
    · exfalso
      have htCU := hCU t htT (hfix t h)
      by_cases htU' : t ∈ U
      ·
        have hD := card_le_two_mul_card_inf_centralizer_of_or (H := E) (x := u₂)
          (y := u₁ * u₂) fun e he => hconj e (hET he)
        rw [hE8] at hD
        by_cases hDU : E ⊓ centralizer ({u₂} : Set G) ≤ U
        · have hUD : E ⊓ centralizer ({u₂} : Set G) = U :=
            Subgroup.eq_of_le_of_card_ge hDU (by rw [hU.card_four]; omega)
          have hUE : U ≤ E := hUD ▸ inf_le_left
          have hEc : E ≤ centralizer ({u₂} : Set G) := fun e he =>
            mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hE2 he (hUE hu₂U))
          rw [inf_eq_left.mpr hEc] at hUD
          have h4 := hU.card_four
          rw [← hUD, hE8] at h4
          omega
        · obtain ⟨x, hxD, hxU⟩ := IsConcreteLE.not_le_iff_exists.mp hDU
          have hxT : x ∈ T := hET (mem_inf.mp hxD).1
          have hx2 : x ^ 2 = 1 := hE2 x (mem_inf.mp hxD).1
          have hxCU := hCU x hxT (mem_centralizer_singleton_iff.mp (mem_inf.mp hxD).2)
          obtain ⟨h2, h8⟩ := sup_zpowers_spec hU hxU hx2 fun w hw =>
            mem_centralizer_iff.mp hxCU w hw
          refine hQ (U ⊔ zpowers x) (sup_le (le_inf hUT fun u hu => ?_)
            (zpowers_le.mpr (mem_inf.mpr ⟨hxT, ?_⟩))) h2 h8
          · exact mem_centralizer_singleton_iff.mpr (hUc u hu t htU')
          · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxCU t htU').symm
      · obtain ⟨h2, h8⟩ := sup_zpowers_spec hU htU' ht2 fun w hw =>
          mem_centralizer_iff.mp htCU w hw
        refine hQ (U ⊔ zpowers t) (sup_le (le_inf hUT fun u hu => ?_)
          (zpowers_le.mpr (mem_inf.mpr ⟨htT, htCt⟩))) h2 h8
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htCU u hu)
    · exact h
  set Q := T ⊓ centralizer ({t} : Set G) with hQdef
  set Q₀ := Q ⊓ centralizer (U : Set G) with hQ₀def
  have htQ : t ∈ Q := mem_inf.mpr ⟨htT, htCt⟩
  have hQt : Q ≤ centralizer ({t} : Set G) := inf_le_right
  have hzQ₀ : u₁ ∈ Q₀ := mem_inf.mpr ⟨mem_inf.mpr ⟨hUT hu₁U,
    mem_centralizer_singleton_iff.mpr (hu₁c t htT).symm⟩,
    mem_centralizer_iff.mpr fun h hh => hUc h hh u₁ hu₁U⟩
  have htQ₀ : t ∉ Q₀ := by
    intro h
    have h1 : u₂ * t = t * u₂ := mem_centralizer_iff.mp (mem_inf.mp h).2 u₂ hu₂U
    have h2 : t * u₂ * t⁻¹ = u₂ := by rw [← h1]; group
    rw [h2] at htU
    exact hu₁1 (by
      calc u₁ = u₁ * u₂ * u₂⁻¹ := by group
        _ = 1 := by rw [← htU]; group)
  have hcover : ∀ x ∈ Q, x ∈ Q₀ ∨ x * t ∈ Q₀ := by
    intro x hx
    have hxT : x ∈ T := (mem_inf.mp hx).1
    have hxt : x ∈ centralizer ({t} : Set G) := (mem_inf.mp hx).2
    rcases hconj x hxT with h | h
    · exact Or.inl (mem_inf.mpr ⟨hx, hCU x hxT (hfix x h)⟩)
    · right
      have hxtT : x * t ∈ T := mul_mem hxT htT
      have h1 : (x * t) * u₂ * (x * t)⁻¹ = u₂ := by
        calc (x * t) * u₂ * (x * t)⁻¹ = x * (t * u₂ * t⁻¹) * x⁻¹ := by group
          _ = (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) := by rw [htU]; group
          _ = u₁ * (u₁ * u₂) := by rw [h, hu₁c x hxT]; group
          _ = u₂ := by rw [← mul_assoc, hu₁u₁, one_mul]
      exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxtT, mul_mem hxt htCt⟩, hCU _ hxtT (hfix _ h1)⟩
  have huniq : ∀ x ∈ Q₀, orderOf x = 2 → x = u₁ := by
    intro x hx hxo
    by_contra hne
    have hxQ : x ∈ Q := (mem_inf.mp hx).1
    have hxT : x ∈ T := (mem_inf.mp hxQ).1
    have hx2 : x ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; omega
    have hW := isKleinFour_sup_zpowers hu₁2 hx2 hu₁1 hx1 hne (hu₁c x hxT).symm
    have hWQ₀ : zpowers u₁ ⊔ zpowers x ≤ Q₀ := sup_le (zpowers_le.mpr hzQ₀) (zpowers_le.mpr hx)
    have htW : t ∉ zpowers u₁ ⊔ zpowers x := fun h => htQ₀ (hWQ₀ h)
    obtain ⟨h2, h8⟩ := sup_zpowers_spec hW htW ht2 fun w hw =>
      mem_centralizer_singleton_iff.mp (hQt (mem_inf.mp (hWQ₀ hw)).1)
    exact hQ _ (sup_le (hWQ₀.trans inf_le_left) (zpowers_le.mpr htQ)) h2 h8
  have hzZ : ∀ x ∈ T, orderOf x = 2 → (∀ y ∈ T, x * y = y * x) → x = u₁ := by
    intro x hx hxo hcent
    refine huniq x (mem_inf.mpr ⟨mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr
      (hcent t htT)⟩, mem_centralizer_iff.mpr fun h hh => (hcent h (hUT hh)).symm⟩) hxo
  have hroot : ∃ x₀ ∈ Q₀, x₀ ^ 2 = u₁ := by
    have h1 := card_le_two_mul_card_inf_centralizer_of_or (H := Q) (x := u₂) (y := u₁ * u₂)
      fun g hg => hconj g (mem_inf.mp hg).1
    have h2 : Q ⊓ centralizer ({u₂} : Set G) ≤ Q₀ := fun g hg =>
      mem_inf.mpr ⟨(mem_inf.mp hg).1, hCU g (mem_inf.mp (mem_inf.mp hg).1).1
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2)⟩
    have h3 := Subgroup.card_le_of_le h2
    have h4 : 8 ≤ Nat.card Q := eight_le_card_inf_centralizer hT hET hE2 hE8 htT ht
    exact exists_sq_eq_of_unique_involution (hT.to_le (inf_le_left.trans inf_le_left))
      (show 4 ≤ Nat.card Q₀ by omega) huniq
  have hu₂Q : u₂ ∉ Q := by
    intro h
    have h1 : u₂ * t = t * u₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp h).2
    have h2 : t * u₂ * t⁻¹ = u₂ := by rw [← h1]; group
    rw [h2] at htU
    exact hu₁1 (by
      calc u₁ = u₁ * u₂ * u₂⁻¹ := by group
        _ = 1 := by rw [← htU]; group)
  have hlt : Q < T := lt_of_le_of_ne inf_le_left fun h => hu₂Q (h ▸ hUT hu₂U)
  obtain ⟨n, hnT, hnQ, hnN⟩ := exists_mem_normalizer_of_lt hT hlt
  have hntQ : n * t * n⁻¹ ∈ Q := (mem_normalizer_iff.mp hnN t).mp htQ
  have hnto : orderOf (n * t * n⁻¹) = 2 := by
    rw [show n * t * n⁻¹ = MulAut.conj n t from rfl, MulEquiv.orderOf_eq, ht]
  have hzt : u₁ * t = t * u₁ := (hu₁c t htT).symm
  rcases eq_or_eq_or_eq_of_cover htt hQt hzt hcover huniq hntQ hnto with h | h | h
  · exfalso
    apply htQ₀
    have h1 : t = u₁ := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * (u₁ * n) := by rw [h, mul_assoc]
        _ = u₁ := by rw [← hu₁c n hnT, inv_mul_cancel_left]
    rw [h1]
    exact hzQ₀
  · exfalso
    have h1 : n * t = t * n := by
      calc n * t = n * t * n⁻¹ * n := by group
        _ = t * n := by rw [h]
    exact hnQ (mem_inf.mpr ⟨hnT, mem_centralizer_singleton_iff.mpr h1⟩)
  · exact ⟨u₁, Q₀, ⟨orderOf_eq_prime hu₁2 hu₁1, hUT hu₁U, hu₁c, hzZ, inf_le_left, hzQ₀, htQ₀,
      hcover, huniq, hroot, ⟨n, hnT, hnN, h⟩⟩⟩

namespace TwoData

variable {T : Subgroup G} {t z : G} {Q₀ : Subgroup G}

omit [Finite G] in
theorem inv_cases (d : TwoData T t z Q₀) (htt : t * t = 1) {x : G}
    (hx : x ∈ T ⊓ centralizer ({t} : Set G)) (hxo : orderOf x = 2) :
    x = z ∨ x = t ∨ x = t * z :=
  eq_or_eq_or_eq_of_cover htt inf_le_right
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (d.hQ₀ d.hzQ₀)).2) d.hcover d.huniq hx hxo

omit [Finite G] in
theorem sq_mem (d : TwoData T t z Q₀) (htt : t * t = 1) {y : G}
    (hy : y ∈ T ⊓ centralizer ({t} : Set G)) : y ^ 2 ∈ Q₀ := by
  rcases d.hcover y hy with h | h
  · exact pow_mem h 2
  · have hyt : y * t = t * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    have h1 : (y * t) ^ 2 = y ^ 2 := by
      calc (y * t) ^ 2 = y * (t * y) * t := by rw [sq]; group
        _ = y * (y * t) * t := by rw [← hyt]
        _ = y ^ 2 * (t * t) := by rw [sq]; group
        _ = y ^ 2 := by rw [htt, mul_one]
    rw [← h1]
    exact pow_mem h 2

omit [Finite G] in
theorem normalizer_le_centralizer (d : TwoData T t z Q₀) (htt : t * t = 1) :
    normalizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
      centralizer ({z} : Set G) := by
  intro g hg
  obtain ⟨x₀, hx₀, hx₀z⟩ := d.hroot
  have hx₀Q := d.hQ₀ hx₀
  have h1 : g * x₀ * g⁻¹ ∈ T ⊓ centralizer ({t} : Set G) := (mem_normalizer_iff.mp hg x₀).mp hx₀Q
  have h2 : (g * x₀ * g⁻¹) ^ 2 = g * z * g⁻¹ := by rw [← hx₀z, conj_pow]
  have h3 : g * z * g⁻¹ ∈ Q₀ := h2 ▸ d.sq_mem htt h1
  have h4 : orderOf (g * z * g⁻¹) = 2 := by
    rw [show g * z * g⁻¹ = MulAut.conj g z from rfl, MulEquiv.orderOf_eq, d.hz]
  have h5 := d.huniq _ h3 h4
  rw [mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h5]

omit [Finite G] in
theorem t_ne_z (d : TwoData T t z Q₀) : t ≠ z := fun h => d.htQ₀ (h ▸ d.hzQ₀)

end TwoData

end CFSG.ComponentClassification.Foote47
