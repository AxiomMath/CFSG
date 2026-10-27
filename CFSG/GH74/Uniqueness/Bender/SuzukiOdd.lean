module

public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.SuzukiDerangement
public import CFSG.GH74.Uniqueness.Bender.Dickson
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Abstract

theorem inv_of_involution_of_trivial_fixed {G : Type*} [Group G] {C : Subgroup G}
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) {y : G} (hy : y * y = 1)
    (hyN : y ∈ normalizer (C : Set G)) (hfix : ∀ c ∈ C, y * c = c * y → c = 1) :
    ∀ c ∈ C, y * c * y⁻¹ = c⁻¹ := by
  intro c hc
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hc' : y * c * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hyN c).mp hc
  have hd : (y * c * y⁻¹) * c ∈ C := C.mul_mem hc' hc
  have hyd : y * ((y * c * y⁻¹) * c) = ((y * c * y⁻¹) * c) * y := by
    have h1 : y * ((y * c * y⁻¹) * c) * y⁻¹ = (y * c * y⁻¹) * c := by
      calc y * ((y * c * y⁻¹) * c) * y⁻¹ = (y * y) * c * y⁻¹ * c * y⁻¹ := by group
        _ = c * y⁻¹ * c * y⁻¹ := by rw [hy, one_mul]
        _ = c * (y * c * y⁻¹) := by rw [hyinv]; group
        _ = (y * c * y⁻¹) * c := hC c hc _ hc'
    exact mul_inv_eq_iff_eq_mul.mp h1
  have h2 := hfix _ hd hyd
  exact (mul_eq_one_iff_eq_inv.mp h2)

theorem eq_one_of_isPGroup_two_of_odd {G : Type*} [Group G] [Finite G] {S C : Subgroup G}
    (hS : IsPGroup 2 S) (hC : Odd (Nat.card C)) {c : G} (hcS : c ∈ S) (hcC : c ∈ C) : c = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨c, hcS⟩
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf c ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨c, hcC⟩ : C)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card C) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hC)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact orderOf_eq_one_iff.mp this

end Abstract

section Prelim

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem BenderType.e_eq_one_of_two {n e : ℕ} (h : BenderType K n 2 e) : e = 1 := by
  rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, he, -⟩ | ⟨hi, -, -⟩
  · omega
  · exact he
  · omega

theorem BenderType.centralizer_involution_isPGroup
    {n i : ℕ} (h : BenderType K n i 1) {y : K}
    (hy : y * y = 1) (hy1 : y ≠ 1) : IsPGroup 2 (centralizer ({y} : Set K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hz : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hyQ : y ∈ (Q : Subgroup K) := hQ (mem_zpowers y)
  have hyroot : y ∈ rootCenter (Q : Subgroup K) := hc.mem_rootCenter_of_mul_self hyQ hy
  rw [hc.centralizer_eq_of_e_one hyroot hy1]
  exact Q.isPGroup'

end Prelim

section Cartan

variable {K : Type*} [Group K] [Finite K]

theorem BenderCore.exists_conj_cartan_of_prime_dvd {n : ℕ} {Q : Sylow 2 K}
    {t : K} (hc : BenderCore (2 ^ n) 2 1 (Q : Subgroup K) t) {x : K}
    (hodd : Odd (orderOf x)) {p : ℕ} (hp : p.Prime) (hpx : p ∣ orderOf x) (hpq : p ∣ 2 ^ n - 1) :
    ∃ g : K, g * x * g⁻¹ ∈ cartan (Q : Subgroup K) t := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hpodd : Odd p := Odd.of_dvd_nat hodd hpx
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (by decide : ¬ Odd 2) hpodd
  set x₁ := x ^ (orderOf x / p) with hx₁
  have hord₁ : orderOf x₁ = p := orderOf_pow_orderOf_div hpos hpx
  have hx₁1 : x₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord₁
    exact hp.one_lt.ne hord₁
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hidx : ¬ p ∣ (2 ^ n) ^ 2 + 1 := by
    intro hd
    have h1 : (2 ^ n) ^ 2 + 1 = (2 ^ n - 1) * (2 ^ n + 1) + 2 := by
      zify [hq1]
      ring
    have h2 : p ∣ (2 ^ n - 1) * (2 ^ n + 1) := Dvd.dvd.mul_right hpq _
    rw [h1] at hd
    have h3 : p ∣ 2 := (Nat.dvd_add_right h2).mp hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  set M := borel (Q : Subgroup K) with hM
  have hS : IsPGroup p (zpowers x₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord₁, pow_one])
  have hmod := hS.card_modEq_card_fixedPoints (α := K ⧸ M)
  have hcardKM : Nat.card (K ⧸ M) = (2 ^ n) ^ 2 + 1 := by
    rw [← Subgroup.index_eq_card]
    exact hc.index_eq
  have hfix : (MulAction.fixedPoints (zpowers x₁) (K ⧸ M)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints (zpowers x₁) (K ⧸ M)) = 0 := by
      rw [hne]
      simp
    rw [h0, hcardKM] at hmod
    exact hidx ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨gM, hgM⟩ := hfix
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gM
  have hxM : g⁻¹ * x₁ * g ∈ M := by
    have h5 : ((x₁ * g : K) : K ⧸ M) = (g : K ⧸ M) :=
      MulAction.mem_fixedPoints.mp hgM ⟨x₁, mem_zpowers x₁⟩
    have h6 := QuotientGroup.eq.mp h5
    have h7 : g⁻¹ * x₁ * g = ((x₁ * g)⁻¹ * g)⁻¹ := by group
    rw [h7]
    exact M.inv_mem h6
  set y := g⁻¹ * x₁ * g with hy
  have hyord : orderOf y = p := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x₁
    rw [← hord₁, ← this]
    simp [hy]
  have hAM : zpowers y ≤ M := (Subgroup.zpowers_le).mpr hxM
  have hAodd : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, hyord]
    exact hpodd
  obtain ⟨q', hq', hq'conj⟩ := hc.exists_conj_cartan_of_odd Q.isPGroup' hAM hAodd
  have hyD : q' * y * q'⁻¹ ∈ cartan (Q : Subgroup K) t := hq'conj y (mem_zpowers y)
  set u := q' * g⁻¹ with hu
  have huD : u * x₁ * u⁻¹ ∈ cartan (Q : Subgroup K) t := by
    have : u * x₁ * u⁻¹ = q' * y * q'⁻¹ := by simp [hu, hy]; group
    rw [this]
    exact hyD
  have hux1 : u * x₁ * u⁻¹ ≠ 1 := by
    intro h1
    apply hx₁1
    have : x₁ = u⁻¹ * (u * x₁ * u⁻¹) * u := by group
    rw [this, h1]
    group
  have hcen := hc.centralizer_cartan_eq Q.isPGroup' huD hux1
  refine ⟨u, ?_⟩
  rw [← hcen]
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hcomm : x * x₁ = x₁ * x := ((Commute.refl x).pow_right _).eq
  calc u * x * u⁻¹ * (u * x₁ * u⁻¹) = u * (x * x₁) * u⁻¹ := by group
    _ = u * (x₁ * x) * u⁻¹ := by rw [hcomm]
    _ = u * x₁ * u⁻¹ * (u * x * u⁻¹) := by group

theorem BenderType.suzuki_odd_dichotomy
    {n e : ℕ} (h : BenderType K n 2 e) {Q : Sylow 2 K}
    {t : K} (hc : BenderCore (2 ^ n) 2 1 (Q : Subgroup K) t) {x : K}
    (hodd : Odd (orderOf x)) :
    (∃ g : K, g * x * g⁻¹ ∈ cartan (Q : Subgroup K) t) ∨ orderOf x ∣ (2 ^ n) ^ 2 + 1 := by
  by_cases hex : ∃ p : ℕ, p.Prime ∧ p ∣ orderOf x ∧ p ∣ 2 ^ n - 1
  · obtain ⟨p, hp, hpx, hpq⟩ := hex
    exact Or.inl (hc.exists_conj_cartan_of_prime_dvd hodd hp hpx hpq)
  · right
    push Not at hex
    have hcop1 : Nat.Coprime (orderOf x) (2 ^ n - 1) :=
      Nat.coprime_of_dvd (fun p hp hpx hpq => hex p hp hpx hpq)
    have hcop2 : Nat.Coprime (orderOf x) ((2 ^ n) ^ 2) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
    have hdvd : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
    have he := h.e_eq_one_of_two
    subst he
    rw [h.card_eq, mul_one] at hdvd
    exact (Nat.Coprime.mul_right hcop2 hcop1).dvd_of_dvd_mul_right hdvd

end Cartan

section Torus

variable {K : Type*} [Group K] [Finite K]

theorem mul_comm_of_isCyclic {G : Type*} [Group G] {H : Subgroup G} (hH : IsCyclic H) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hH.exists_generator
  obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hg ⟨b, hb⟩
  have h1 : a = (g : G) ^ i := by
    have := congrArg Subtype.val hi
    simpa using this.symm
  have h2 : b = (g : G) ^ j := by
    have := congrArg Subtype.val hj
    simpa using this.symm
  rw [h1, h2]
  exact ((Commute.refl (g : G)).zpow_zpow i j).eq

theorem mem_of_odd_of_card_normalizer {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (h : Nat.card (normalizer (T : Set G)) = 2 * Nat.card T ∨
      Nat.card (normalizer (T : Set G)) = 4 * Nat.card T) {a : G}
    (ha : a ∈ normalizer (T : Set G)) (hodd : Odd (orderOf a)) : a ∈ T := by
  classical
  set N := normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have : (T.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change (g : G) * (n : G) * (g : G)⁻¹ ∈ T
    exact (Subgroup.mem_normalizer_iff.mp g.2 (n : G)).mp hn
  have hcard : Nat.card (N ⧸ T.subgroupOf N) * Nat.card T = Nat.card N := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv] at h1
    exact h1.symm
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have hq4 : Nat.card (N ⧸ T.subgroupOf N) ∣ 4 := by
    rcases h with h | h
    · rw [h] at hcard
      have := Nat.eq_of_mul_eq_mul_right hT0 hcard
      rw [this]
      norm_num
    · rw [h] at hcard
      have := Nat.eq_of_mul_eq_mul_right hT0 hcard
      rw [this]
  set a' : N := ⟨a, ha⟩ with ha'
  have hord1 : orderOf (QuotientGroup.mk a' : N ⧸ T.subgroupOf N) ∣ orderOf a := by
    have := orderOf_map_dvd (QuotientGroup.mk' (T.subgroupOf N)) a'
    rwa [Subgroup.orderOf_mk] at this
  have hord2 : orderOf (QuotientGroup.mk a' : N ⧸ T.subgroupOf N) ∣ 4 :=
    (_root_.orderOf_dvd_natCard _).trans hq4
  have hoddq : Odd (orderOf (QuotientGroup.mk a' : N ⧸ T.subgroupOf N)) :=
    Odd.of_dvd_nat hodd hord1
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk a' : N ⧸ T.subgroupOf N)) (2 ^ 2) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hoddq)
  have h1 : orderOf (QuotientGroup.mk a' : N ⧸ T.subgroupOf N) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop (by simpa using hord2)
  have h2 : (QuotientGroup.mk a' : N ⧸ T.subgroupOf N) = 1 := orderOf_eq_one_iff.mp h1
  exact (QuotientGroup.eq_one_iff a').mp h2

theorem BenderType.suzuki_odd_centralizer
    {n e : ℕ} (h : BenderType K n 2 e) {x : K} (hx1 : x ≠ 1)
    (hodd : Odd (orderOf x)) :
    IsCyclic (centralizer ({x} : Set K)) ∧ Odd (Nat.card (centralizer ({x} : Set K))) ∧
      (Nat.card (centralizer ({x} : Set K)) = 2 ^ n - 1 ∨
        ∃ a, n = 2 * a + 1 ∧
          (Nat.card (centralizer ({x} : Set K)) = 2 ^ n - 2 ^ (a + 1) + 1 ∨
            Nat.card (centralizer ({x} : Set K)) = 2 ^ n + 2 ^ (a + 1) + 1)) ∧
      (Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) =
          2 * Nat.card (centralizer ({x} : Set K)) ∨
        Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) =
          4 * Nat.card (centralizer ({x} : Set K))) := by
  have he := h.e_eq_one_of_two
  subst he
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  rcases h.suzuki_odd_dichotomy hc hodd with ⟨g, hg⟩ | hdiv
  ·
    set Q : Sylow 2 K := default with hQ
    set D := cartan (Q : Subgroup K) t with hD
    have hx'1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h1]
      group
    have hCD : centralizer ({g * x * g⁻¹} : Set K) = D :=
      hc.centralizer_cartan_eq Q.isPGroup' hg hx'1
    have hmap : (centralizer ({x} : Set K)).map (MulAut.conj g).toMonoidHom = D := by
      rw [map_centralizer_singleton (MulAut.conj g) x]
      simpa [MulAut.conj_apply] using hCD
    have hcardC : Nat.card (centralizer ({x} : Set K)) = Nat.card D := by
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    refine ⟨?_, ?_, Or.inl ?_, Or.inl ?_⟩
    · exact ((Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hmap)).isCyclic.mpr hc.isCyclic
    · rw [hcardC]
      exact hc.odd_card_cartan
    · rw [hcardC, hc.card_cartan, mul_one]
    · have hNmap : (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)).map
          (MulAut.conj g).toMonoidHom = normalizer (D : Set K) := by
        rw [← hmap]
        exact Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective
      have h5 : Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) =
          Nat.card (normalizer (D : Set K)) := by
        rw [← hNmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      rw [h5, hcardC]
      exact hc.card_normalizer_cartan Q.isPGroup' hg hx'1
  · obtain ⟨hcyc, hodd', ⟨a, hn, hcard⟩, hN⟩ := h.suzuki_derangement_type hx1 hdiv
    exact ⟨hcyc, hodd', Or.inr ⟨a, hn, hcard⟩, Or.inr hN⟩

theorem BenderType.suzuki_odd_centralizer_eq
    {n e : ℕ} (h : BenderType K n 2 e) {x : K}
    (hx1 : x ≠ 1) (hodd : Odd (orderOf x)) {c : K} (hc : c ∈ centralizer ({x} : Set K))
    (hc1 : c ≠ 1) : centralizer ({c} : Set K) = centralizer ({x} : Set K) := by
  obtain ⟨hcycx, hoddC, -, -⟩ := h.suzuki_odd_centralizer hx1 hodd
  have hcodd : Odd (orderOf c) := by
    have h1 : orderOf c ∣ Nat.card (centralizer ({x} : Set K)) :=
      (Subgroup.orderOf_coe (⟨c, hc⟩ : centralizer ({x} : Set K))) ▸ orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hoddC h1
  obtain ⟨hcycc, -, -, -⟩ := h.suzuki_odd_centralizer hc1 hcodd
  have hxc : x ∈ centralizer ({c} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hcx : c ∈ centralizer ({x} : Set K) := hc
  have hxx : x ∈ centralizer ({x} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcc : c ∈ centralizer ({c} : Set K) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  apply le_antisymm
  · intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_comm_of_isCyclic hcycc hd hxc)
  · intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_comm_of_isCyclic hcycx hd hcx)

theorem BenderType.suzuki_odd_involution
    {n e : ℕ} (h : BenderType K n 2 e) {x : K} (hx1 : x ≠ 1)
    (hodd : Odd (orderOf x)) :
    (∃ y ∈ normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K), y * y = 1 ∧ y ≠ 1) ∧
    (∀ y ∈ normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K), y * y = 1 → y ≠ 1 →
      ∀ c ∈ centralizer ({x} : Set K), y * c * y⁻¹ = c⁻¹) := by
  obtain ⟨hcyc, hoddC, -, hN⟩ := h.suzuki_odd_centralizer hx1 hodd
  have he := h.e_eq_one_of_two
  refine ⟨?_, fun y hyN hy hy1 => ?_⟩
  · have hev : 2 ∣ Nat.card (normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K)) := by
      rcases hN with hN | hN
      · rw [hN]; exact Dvd.intro _ rfl
      · rw [hN]; exact ⟨2 * Nat.card (centralizer ({x} : Set K)), by ring⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hev
    refine ⟨(y : K), y.2, ?_, ?_⟩
    · have h2 : orderOf (y : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
      have := pow_orderOf_eq_one (y : K)
      rw [h2, sq] at this
      exact this
    · intro h1
      have h2 : orderOf (y : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
      rw [h1, orderOf_one] at h2
      omega
  · apply inv_of_involution_of_trivial_fixed (fun a ha b hb => mul_comm_of_isCyclic hcyc ha hb) hy hyN
    intro c hc hyc
    have h2 : IsPGroup 2 (centralizer ({y} : Set K)) :=
      (h.e_eq_one_of_two ▸ h : BenderType K n 2 1).centralizer_involution_isPGroup hy hy1
    exact eq_one_of_isPGroup_two_of_odd h2 hoddC
      (Subgroup.mem_centralizer_singleton_iff.mpr hyc.symm) hc

end Torus

section Subgroups

variable {K : Type*} [Group K] [Finite K]

open scoped commutatorElement in
theorem exists_abelian_normal_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (hG : (⊤ : Subgroup G) ≠ ⊥) :
    ∃ B : Subgroup G, B.Normal ∧ B ≠ ⊥ ∧ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  have hk : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hk
    exact hG hk
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  rw [hm] at hk
  refine ⟨derivedSeries G m, inferInstance, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · intro a ha b hb
    have hcomm : ⁅a, b⁆ ∈ derivedSeries G (m + 1) := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ha hb
    rw [hk, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
    exact hcomm

theorem isPGroup_two_of_sq_eq_one {G : Type*} [Group G] {A : Subgroup G}
    (hA : ∀ x ∈ A, x * x = 1) : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa [sq] using hA g g.2)⟩

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {y : G}
    (hy : y ∈ normalizer (A : Set G)) : y ∈ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) := by
  have key : ∀ y ∈ normalizer (A : Set G), ∀ c ∈ centralizer (A : Set G), y * c * y⁻¹ ∈ centralizer (A : Set G) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : y⁻¹ * a * y ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (A : Set G)).inv_mem hy) a).mp ha
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hc _ h1
    calc a * (y * c * y⁻¹) = y * ((y⁻¹ * a * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * a * y)) * y⁻¹ := by rw [h2]
      _ = y * c * y⁻¹ * a := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key y hy c
  · intro hc
    have := key y⁻¹ ((normalizer (A : Set G)).inv_mem hy) _ hc
    simpa [mul_assoc] using this

theorem BenderType.suzuki_odd_subgroup_le
    {n e : ℕ} (h : BenderType K n 2 e) {A : Subgroup K}
    (hA : Odd (Nat.card A)) (hA1 : A ≠ ⊥) :
    ∃ x₀ ∈ A, x₀ ≠ 1 ∧ A ≤ centralizer ({x₀} : Set K) := by
  classical
  have : Group.IsSolvable A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hA
  have hAtop : (⊤ : Subgroup A) ≠ ⊥ := by
    intro htop
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : (⟨a, ha⟩ : A) ∈ (⊤ : Subgroup A) := trivial
    rw [htop, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨B, hBn, hB1, hBcomm⟩ := exists_abelian_normal_of_solvable hAtop
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  set x₀ : K := ((b : A) : K) with hx₀
  have hx₀A : x₀ ∈ A := (b : A).2
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    apply hb1
    apply Subtype.ext
    apply Subtype.ext
    simpa [hx₀] using h1
  have hodd₀ : Odd (orderOf x₀) := by
    have h1 : orderOf x₀ ∣ Nat.card A := by
      have := orderOf_dvd_natCard (b : A)
      rwa [← Subgroup.orderOf_coe] at this
    exact Odd.of_dvd_nat hA h1
  obtain ⟨hTcyc, hToddC, -, hN⟩ := h.suzuki_odd_centralizer hx₀1 hodd₀
  have hconjT : ∀ a ∈ A, a⁻¹ * x₀ * a ∈ centralizer ({x₀} : Set K) := by
    intro a ha
    have h1 : (⟨a, ha⟩ : A)⁻¹ * (b : A) * (⟨a, ha⟩ : A) ∈ B := by
      have := hBn.conj_mem (b : A) (b.2) (⟨a, ha⟩ : A)⁻¹
      simpa using this
    have h2 := hBcomm _ h1 (b : A) b.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val h2
    simpa [hx₀] using this
  have hnormT : ∀ a ∈ A, ∀ c ∈ centralizer ({x₀} : Set K), a * c * a⁻¹ ∈ centralizer ({x₀} : Set K) := by
    intro a ha c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 := mul_comm_of_isCyclic hTcyc hc (hconjT a ha)
    calc a * c * a⁻¹ * x₀ = a * (c * (a⁻¹ * x₀ * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * x₀ * a) * c) * a⁻¹ := by rw [h3]
      _ = x₀ * (a * c * a⁻¹) := by group
  refine ⟨x₀, hx₀A, hx₀1, fun a ha => ?_⟩
  have haN : a ∈ normalizer ((centralizer ({x₀} : Set K) : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hnormT a ha c
    · intro hc
      have := hnormT a⁻¹ (A.inv_mem ha) _ hc
      simpa [mul_assoc] using this
  have hodda : Odd (orderOf a) := by
    have h1 : orderOf a ∣ Nat.card A := by
      have := orderOf_dvd_natCard (⟨a, ha⟩ : A)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hA h1
  exact mem_of_odd_of_card_normalizer hN haN hodda

theorem BenderType.suzuki_odd_subgroup
    {n e : ℕ} (h : BenderType K n 2 e) {A : Subgroup K}
    (hA : Odd (Nat.card A)) (hA1 : A ≠ ⊥) :
    ∃ T : Subgroup K, A ≤ T ∧ IsCyclic T ∧ Odd (Nat.card T) ∧
      (∀ x ∈ A, x ≠ 1 → centralizer ({x} : Set K) = T) ∧
      (Nat.card T = 2 ^ n - 1 ∨
        ∃ a, n = 2 * a + 1 ∧
          (Nat.card T = 2 ^ n - 2 ^ (a + 1) + 1 ∨ Nat.card T = 2 ^ n + 2 ^ (a + 1) + 1)) ∧
      (Nat.card (normalizer (T : Set K)) = 2 * Nat.card T ∨
        Nat.card (normalizer (T : Set K)) = 4 * Nat.card T) ∧
      (∃ y ∈ normalizer (T : Set K), y * y = 1 ∧ y ≠ 1) ∧
      (∀ y ∈ normalizer (T : Set K), y * y = 1 → y ≠ 1 → ∀ c ∈ T, y * c * y⁻¹ = c⁻¹) ∧
      (∀ y : K, y * y = 1 → y ≠ 1 → y ∈ normalizer (A : Set K) →
        ∀ a ∈ A, y * a * y⁻¹ = a⁻¹) := by
  obtain ⟨x₀, hx₀A, hx₀1, hAT⟩ := h.suzuki_odd_subgroup_le hA hA1
  have hodd₀ : Odd (orderOf x₀) := by
    have h1 : orderOf x₀ ∣ Nat.card A := by
      have := orderOf_dvd_natCard (⟨x₀, hx₀A⟩ : A)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hA h1
  obtain ⟨hTcyc, hToddC, hcards, hN⟩ := h.suzuki_odd_centralizer hx₀1 hodd₀
  obtain ⟨hex, hinv⟩ := h.suzuki_odd_involution hx₀1 hodd₀
  have hAx : ∀ x ∈ A, x ≠ 1 → centralizer ({x} : Set K) = centralizer ({x₀} : Set K) :=
    fun x hx hx1 => h.suzuki_odd_centralizer_eq hx₀1 hodd₀ (hAT hx) hx1
  refine ⟨centralizer ({x₀} : Set K), hAT, hTcyc, hToddC, hAx, hcards, hN, hex, hinv, ?_⟩
  intro y hy hy1 hyA a ha
  have hCA : centralizer (A : Set K) = centralizer ({x₀} : Set K) := by
    apply le_antisymm
    · intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hc x₀ hx₀A).symm)
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (mul_comm_of_isCyclic hTcyc (hAT hb) hc)
  have hyN : y ∈ normalizer ((centralizer ({x₀} : Set K) : Subgroup K) : Set K) := by
    rw [← hCA]
    exact mem_normalizer_centralizer_of_mem_normalizer hyA
  exact hinv y hyN hy hy1 a (hAT ha)

theorem BenderType.suzuki_solvable_subgroup
    {n e : ℕ} (h : BenderType K n 2 e) {J : Subgroup K}
    [Group.IsSolvable J] (hJ1 : J ≠ ⊥) :
    (∃ Q : Sylow 2 K, J ≤ normalizer ((Q : Subgroup K) : Set K)) ∨
      ∃ x : K, x ≠ 1 ∧ Odd (orderOf x) ∧
        J ≤ normalizer ((centralizer ({x} : Set K) : Subgroup K) : Set K) := by
  classical
  have hJtop : (⊤ : Subgroup J) ≠ ⊥ := by
    intro htop
    apply hJ1
    rw [eq_bot_iff]
    intro a ha
    have h1 : (⟨a, ha⟩ : J) ∈ (⊤ : Subgroup J) := trivial
    rw [htop, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  obtain ⟨B₀, hBn, hB1, hBcomm⟩ := exists_abelian_normal_of_solvable hJtop
  set B : Subgroup K := B₀.map J.subtype with hB
  have hBK : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hBcomm a ha b hb)
  have hBJ : ∀ j ∈ J, ∀ b ∈ B, j * b * j⁻¹ ∈ B := by
    rintro j hj _ ⟨b, hb, rfl⟩
    have := hBn.conj_mem b hb ⟨j, hj⟩
    exact ⟨_, this, rfl⟩
  have hBne : B ≠ ⊥ := by
    intro hB'
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    have : (b : K) ∈ B := ⟨b, hb, rfl⟩
    rw [hB', Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  let V : Subgroup K :=
    { carrier := {b | b ∈ B ∧ b * b = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨B.mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hBK b hb a ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨B.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨B.inv_mem ha, ?_⟩
        have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [this]
        exact ha2 }
  have hVJ : ∀ j ∈ J, ∀ v ∈ V, j * v * j⁻¹ ∈ V := by
    rintro j hj v ⟨hvB, hv2⟩
    refine ⟨hBJ j hj v hvB, ?_⟩
    calc j * v * j⁻¹ * (j * v * j⁻¹) = j * (v * v) * j⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  by_cases hV : V = ⊥
  ·
    right
    have hBodd : Odd (Nat.card B) := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
      have hb2 : orderOf (b : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hb
      have hbsq : (b : K) * (b : K) = 1 := by
        have := pow_orderOf_eq_one (b : K)
        rwa [hb2, sq] at this
      have hbV : (b : K) ∈ V := ⟨b.2, hbsq⟩
      rw [hV, Subgroup.mem_bot] at hbV
      rw [hbV, orderOf_one] at hb2
      omega
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    set x : K := (b : K) with hx
    have hx1 : x ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hxodd : Odd (orderOf x) := by
      have h1 : orderOf x ∣ Nat.card B := by
        have := orderOf_dvd_natCard b
        rwa [← Subgroup.orderOf_coe] at this
      exact Odd.of_dvd_nat hBodd h1
    refine ⟨x, hx1, hxodd, fun j hj => ?_⟩
    obtain ⟨hTcyc, -, -, -⟩ := h.suzuki_odd_centralizer hx1 hxodd
    have hconjT : ∀ j ∈ J, j⁻¹ * x * j ∈ centralizer ({x} : Set K) := by
      intro j hj
      have h1 : j⁻¹ * x * j ∈ B := by
        have := hBJ j⁻¹ (J.inv_mem hj) x b.2
        simpa using this
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hBK _ h1 x b.2)
    have hnormT : ∀ j ∈ J, ∀ c ∈ centralizer ({x} : Set K),
        j * c * j⁻¹ ∈ centralizer ({x} : Set K) := by
      intro j hj c hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 := mul_comm_of_isCyclic hTcyc hc (hconjT j hj)
      calc j * c * j⁻¹ * x = j * (c * (j⁻¹ * x * j)) * j⁻¹ := by group
        _ = j * ((j⁻¹ * x * j) * c) * j⁻¹ := by rw [h3]
        _ = x * (j * c * j⁻¹) := by group
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hnormT j hj c
    · intro hc
      have := hnormT j⁻¹ (J.inv_mem hj) _ hc
      simpa [mul_assoc] using this
  ·
    left
    have hV2 : IsPGroup 2 V := isPGroup_two_of_sq_eq_one (fun x hx => hx.2)
    obtain ⟨Q, hVQ⟩ := hV2.exists_le_sylow
    obtain ⟨t, hc⟩ := h.exists_benderCore Q
    refine ⟨Q, ?_⟩
    have hVN : normalizer (V : Set K) ≤ borel (Q : Subgroup K) :=
      IsStronglyEmbedded.normalizer_le hc.strong (hVQ.trans (le_borel _)) hV2 hV
    intro j hj
    apply hVN
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact hVJ j hj v hv
    · intro hv
      have := hVJ j⁻¹ (J.inv_mem hj) _ hv
      simpa [mul_assoc] using this

theorem BenderType.suzuki_odd_normal_card_le_two
    {n e : ℕ} (h : BenderType K n 2 e)
    {J A U : Subgroup K} (hAJ : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (hAodd : Odd (Nat.card A))
    (hA1 : A ≠ ⊥) (hUJ : U ≤ J) (hU : ∀ u ∈ U, u * u = 1) : Nat.card U ≤ 2 := by
  classical
  obtain ⟨T, hAT, hTcyc, hTodd, hAx, -, -, -, -, hinvA⟩ := h.suzuki_odd_subgroup hAodd hA1
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha₀1 : (a₀ : K) ≠ 1 := fun h1 => ha₀ (Subtype.ext h1)
  have hnormA : ∀ u ∈ U, u ∈ normalizer (A : Set K) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hAJ u (hUJ hu) c
    · intro hc
      have := hAJ u⁻¹ (J.inv_mem (hUJ hu)) _ hc
      simpa [mul_assoc] using this
  have huniq : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → u = v := by
    intro u hu v hv hu1 hv1
    have hu' := hinvA u (hU u hu) hu1 (hnormA u hu)
    have hv' := hinvA v (hU v hv) hv1 (hnormA v hv)
    have hcomm : (u * v) * (a₀ : K) = (a₀ : K) * (u * v) := by
      have h1 := hv' (a₀ : K) a₀.2
      have h2 := hu' ((a₀ : K)⁻¹) (A.inv_mem a₀.2)
      calc u * v * (a₀ : K) = u * (v * (a₀ : K) * v⁻¹) * v := by group
        _ = u * ((a₀ : K)⁻¹) * v := by rw [h1]
        _ = u * ((a₀ : K)⁻¹) * u⁻¹ * (u * v) := by group
        _ = ((a₀ : K)⁻¹)⁻¹ * (u * v) := by rw [h2]
        _ = (a₀ : K) * (u * v) := by rw [inv_inv]
    have hmem : u * v ∈ centralizer ({(a₀ : K)} : Set K) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    rw [hAx _ a₀.2 ha₀1] at hmem
    have hUsq : (u * v) * (u * v) = 1 := hU _ (U.mul_mem hu hv)
    have hp2 : IsPGroup 2 (zpowers (u * v)) := by
      apply isPGroup_two_of_sq_eq_one
      rintro _ ⟨k, rfl⟩
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · have : (u * v) ^ (2 * m) = 1 := by
          rw [zpow_mul, show ((u * v) ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact hUsq, one_zpow]
        show (u * v) ^ (2 * m) * (u * v) ^ (2 * m) = 1
        rw [this]
        simp
      · have : (u * v) ^ (2 * m + 1) = u * v := by
          rw [zpow_add_one, zpow_mul, show ((u * v) ^ (2 : ℤ)) = 1 by rw [zpow_two]; exact hUsq,
            one_zpow, one_mul]
        show (u * v) ^ (2 * m + 1) * (u * v) ^ (2 * m + 1) = 1
        rw [this]
        exact hUsq
    have h1 : u * v = 1 :=
      eq_one_of_isPGroup_two_of_odd hp2 hTodd (Subgroup.mem_zpowers _) hmem
    exact (mul_eq_one_iff_eq_inv.mp h1).trans (inv_eq_of_mul_eq_one_right (hU v hv))
  by_cases hU1 : U = ⊥
  · rw [hU1, Subgroup.card_bot]
    norm_num
  · obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
    have hsub : (U : Set K) ⊆ {1, (u : K)} := by
      intro v hv
      by_cases hv1 : v = 1
      · left; exact hv1
      · right; exact huniq v hv u u.2 hv1 (fun h1 => hu1 (Subtype.ext h1))
    calc Nat.card U = (U : Set K).ncard := by rw [← Nat.card_coe_set_eq]; rfl
      _ ≤ ({1, (u : K)} : Set K).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        have := Set.ncard_insert_le (1 : K) ({(u : K)} : Set K)
        rw [Set.ncard_singleton] at this
        exact this

end Subgroups

end CFSG.GH74.Uniqueness.Bender
