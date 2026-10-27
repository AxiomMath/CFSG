module

public import CFSG.GH74.Uniqueness.Section15Derived
public import CFSG.GH74.Uniqueness.Section17Final
public import CFSG.GH74.Uniqueness.Section15Aux
public import CFSG.GH74.Uniqueness.Section15Aux2

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conj_mem_sup {A B : Subgroup X} {d : X} (hA : ∀ x ∈ A, d * x * d⁻¹ ∈ A)
    (hB : ∀ x ∈ B, d * x * d⁻¹ ∈ B) {x : X} (hx : x ∈ A ⊔ B) : d * x * d⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj d).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left (hA a ha)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_right (hB b hb)
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

omit [Finite X] in
theorem isPGroup_two_of_card_dvd {H : Subgroup X} {k : ℕ} (h : Nat.card H ∣ 2 ^ k) :
    IsPGroup 2 H := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  exact IsPGroup.of_card hi

theorem exists_pow_orderOf_prime {a : X} (ha : a ≠ 1) :
    ∃ e : ℕ, (orderOf (a ^ e)).Prime ∧ orderOf (a ^ e) ∣ orderOf a ∧ a ^ e ≠ 1 := by
  have h1 : orderOf a ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨r, hr, hra⟩ := Nat.exists_prime_and_dvd h1
  have hord := orderOf_pow_orderOf_div (orderOf_pos a).ne' hra
  refine ⟨orderOf a / r, ?_, ?_, ?_⟩
  · rw [hord]
    exact hr
  · rw [hord]
    exact hra
  · intro h
    rw [h, orderOf_one] at hord
    exact hr.one_lt.ne hord

omit [Finite X] in
theorem isPGroup_zpowers_of_orderOf {p : ℕ} {x : X} (hx : orderOf x = p) :
    IsPGroup p (zpowers x) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hx, pow_one]

omit [Finite X] in
theorem mem_normalizer_zpowers_of_commute {v z : X} (h : v * z = z * v) :
    v ∈ normalizer (zpowers z : Set X) := by
  have hc : ∀ w ∈ zpowers z, v * w * v⁻¹ = w := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    rw [(Commute.zpow_right (h : Commute v z) i).eq, mul_inv_cancel_right]
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    rw [hc w hw]
    exact hw
  · intro hw
    have h1 := hc _ hw
    have h2 : w = v * w * v⁻¹ := by
      calc w = v⁻¹ * (v * (v * w * v⁻¹) * v⁻¹) * v := by rw [h1]; group
        _ = v * w * v⁻¹ := by group
    rw [h2]
    exact hw

namespace Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X}

omit [Finite X] in
theorem mem_K_sup_zpowers (F : Facts15 M n L D K J Mo V) {y : X} (hyJ : y ∈ J) {w : X}
    (hw : w ∈ K ⊔ zpowers y) : ∃ k ∈ K, ∃ z ∈ zpowers y, w = k * z := by
  refine Bender.exists_mul_of_mem_sup_of_commute (fun k hk z hz => ?_) hw
  have hzJ : z ∈ J := (zpowers_le.mpr hyJ) hz
  exact (F.J_comm hzJ (F.K_le_L hk)).symm

theorem cent_le_Mo (F : Facts15 M n L D K J Mo V) (h : ∀ s ∈ V, s * s = 1 → s ∈ Mo)
    {y : X} (hyJ : y ∈ J) {k : X} (hk : k ∈ K) {z : X} (hz : z ∈ zpowers y) (hkz : k * z ≠ 1)
    {v : X} (hv : v ∈ V) (hvw : v * (k * z) = (k * z) * v) : v ∈ Mo := by
  have hzJ : z ∈ J := (zpowers_le.mpr hyJ) hz
  by_cases hk1 : k = 1
  · subst hk1
    rw [one_mul] at hkz hvw
    have hYJ : zpowers z ≤ J := zpowers_le.mpr hzJ
    have hYne : zpowers z ≠ ⊥ := by
      intro hb
      apply hkz
      have : z ∈ zpowers z := mem_zpowers z
      rw [hb] at this
      exact mem_bot.mp this
    have hvN : v ∈ normalizer (zpowers z : Set X) := mem_normalizer_zpowers_of_commute hvw
    obtain ⟨m, hm, d, hd, rfl⟩ := F.NM_eq v (F.V_le hv) (F.NY_le _ hYJ hYne hvN)
    have hdV : d ∈ V := by
      have e : d = m⁻¹ * (m * d) := by group
      rw [e]
      exact mul_mem (inv_mem (F.Mo_le_V hm)) hv
    have hP : IsPGroup 2 ↥(V ⊓ D) := F.V_pgroup.to_le inf_le_left
    have hbot := eq_bot_of_forall_sq hP fun x hx hx2 =>
      F.eq_one_of_mem_Mo_D (h x (mem_inf.mp hx).1 hx2) (mem_inf.mp hx).2
    have hd1 : d = 1 := by
      have : d ∈ V ⊓ D := mem_inf.mpr ⟨hdV, hd⟩
      rw [hbot] at this
      exact mem_bot.mp this
    rw [hd1, mul_one]
    exact hm
  ·
    have hP : IsPGroup 2 ↥(V ⊓ centralizer ({k * z} : Set X)) := F.V_pgroup.to_le inf_le_left
    have hbot := eq_bot_of_forall_sq hP fun s hs hs2 => by
      obtain ⟨hsV, hsC⟩ := mem_inf.mp hs
      have hsMo := h s hsV hs2
      have hsw : s * (k * z) = (k * z) * s := mem_centralizer_singleton_iff.mp hsC
      have hzs : z * s = s * z := F.J_comm_Mo hzJ hsMo
      have hks : k * s = s * k := by
        have h1 : s * k * z = k * s * z := by
          calc s * k * z = s * (k * z) := by group
            _ = k * z * s := hsw
            _ = k * (z * s) := by group
            _ = k * s * z := by rw [hzs]; group
        exact (mul_right_cancel h1).symm
      exact F.K_fpf k hk hk1 s hsMo hks
    have hv1 : v ∈ V ⊓ centralizer ({k * z} : Set X) :=
      mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr hvw⟩
    rw [hbot] at hv1
    rw [mem_bot.mp hv1]
    exact one_mem _

theorem fpf_quot (F : Facts15 M n L D K J Mo V) (h : ∀ s ∈ V, s * s = 1 → s ∈ Mo)
    {y : X} (hyJ : y ∈ J) (hyodd : Odd (orderOf y)) {a : X} (ha : a ∈ K ⊔ zpowers y)
    (ha1 : a ≠ 1) {x : X} (hx : x ∈ V) (hxa : x⁻¹ * (a * x * a⁻¹) ∈ Mo) : x ∈ Mo := by
  obtain ⟨e, hpr, hdvd, hae⟩ := exists_pow_orderOf_prime ha1
  set r := orderOf (a ^ e) with hr
  have hA : a ^ e ∈ K ⊔ zpowers y := pow_mem ha e
  have hr2 : r ≠ 2 := by
    intro hr2
    obtain ⟨k, hk, z, hz, hkz⟩ := F.mem_K_sup_zpowers hyJ ha
    have hzJ : z ∈ J := (zpowers_le.mpr hyJ) hz
    have hkzc : k * z = z * k := (F.J_comm hzJ (F.K_le_L hk)).symm
    have hok : Odd (orderOf k) := by
      have := orderOf_dvd_natCard (⟨k, hk⟩ : ↥K)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat F.odd_card_K this
    have hoz : Odd (orderOf z) := by
      exact Odd.of_dvd_nat hyodd (orderOf_dvd_of_mem_zpowers hz)
    have hoa : Odd (orderOf a) := by
      rw [hkz]
      have h1 : (k * z) ^ (orderOf k * orderOf z) = 1 := by
        rw [(Commute.mul_pow hkzc), pow_mul, pow_orderOf_eq_one, one_pow, mul_comm, pow_mul,
          pow_orderOf_eq_one, one_pow, one_mul]
      exact Odd.of_dvd_nat (hok.mul hoz) (orderOf_dvd_of_pow_eq_one h1)
    rw [hr2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hoa) (even_iff_two_dvd.mpr hdvd)
  have hxa' : x⁻¹ * (a ^ e * x * (a ^ e)⁻¹) ∈ Mo := by
    have hinv : ∀ j : ℕ, x⁻¹ * (a ^ j * x * (a ^ j)⁻¹) ∈ Mo := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have haM : a ∈ M := by
          have hle : K ⊔ zpowers y ≤ M := sup_le F.K_le_M (zpowers_le.mpr (F.J_le_M hyJ))
          exact hle ha
        have h1 : a * (x⁻¹ * (a ^ j * x * (a ^ j)⁻¹)) * a⁻¹ ∈ Mo := F.Mo_normal a haM _ ih
        have e1 : x⁻¹ * (a ^ (j + 1) * x * (a ^ (j + 1))⁻¹) =
            (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * (a ^ j * x * (a ^ j)⁻¹)) * a⁻¹) := by
          rw [pow_succ']
          group
        rw [e1]
        exact mul_mem hxa h1
    exact hinv e
  have haeM : ∀ m ∈ Mo, a ^ e * m * (a ^ e)⁻¹ ∈ Mo := by
    have hle : K ⊔ zpowers y ≤ M := sup_le F.K_le_M (zpowers_le.mpr (F.J_le_M hyJ))
    exact F.Mo_normal _ (hle hA)
  obtain ⟨c, hc, hcomm⟩ := exists_commute_mem_coset hpr hr2
    (isPGroup_zpowers_of_orderOf hr.symm) F.Mo_isPGroup haeM hxa'
  obtain ⟨k, hk, z, hz, hkz⟩ := F.mem_K_sup_zpowers hyJ hA
  have hcV : c ∈ V := by
    have e1 : c = x * (x⁻¹ * c) := by group
    rw [e1]
    exact mul_mem hx (F.Mo_le_V hc)
  have hcMo : c ∈ Mo := by
    rw [hkz] at hcomm hae
    exact F.cent_le_Mo h hyJ hk hz hae hcV hcomm.symm
  have e1 : x = c * (x⁻¹ * c)⁻¹ := by group
  rw [e1]
  exact mul_mem hcMo (inv_mem hc)

omit [Finite X] in
theorem card_K_sup (F : Facts15 M n L D K J Mo V) {W : Subgroup X} (hWJ : W ≤ J) :
    Nat.card ↥(K ⊔ W) = Nat.card K * Nat.card W := by
  refine card_sup_of_normal (fun w hw k hk => ?_) ?_
  · rw [F.J_comm (hWJ hw) (F.K_le_L hk), mul_inv_cancel_right]
    exact hk
  · rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (F.eq_one_of_mem_K_J (mem_inf.mp hx).1 (hWJ (mem_inf.mp hx).2))

theorem odd_card_of_forall_odd {H : Subgroup X} (h : ∀ x ∈ H, Odd (orderOf x)) :
    Odd (Nat.card H) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (even_iff_two_dvd.mp hne)
  have h1 := h x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (Nat.not_odd_iff_even.mpr even_two) h1

theorem lemma153 (F : Facts15 M n L D K J Mo V) (h : ∀ s ∈ V, s * s = 1 → s ∈ Mo) : V = Mo := by
  by_contra hne
  have hMoV := F.Mo_le_V
  have hVD : V ⊓ D = ⊥ := eq_bot_of_forall_sq (F.V_pgroup.to_le inf_le_left) fun x hx hx2 =>
    F.eq_one_of_mem_Mo_D (h x (mem_inf.mp hx).1 hx2) (mem_inf.mp hx).2
  obtain ⟨u, huJ, hu2⟩ := F.exists_inv_J
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu2
    norm_num at hu2
  by_cases hJ2 : IsPGroup 2 J
  · obtain ⟨k, hk⟩ := hJ2.exists_card_eq
    have hC0 : IsPGroup 2 (centralizer (Mo : Set X)) := by
      apply isPGroup_two_of_card_dvd (k := 3 * n + k)
      rw [pow_add, ← hk]
      exact F.card_C0_dvd
    have hC0V := F.V_max _ F.cent_Mo_le (fun g hg x hx => F.C0_conj hg hx) hC0
    exact hu1 (F.eq_one_of_mem_L_J (F.Mo_le_L (h u (hC0V (F.J_le_C0 huJ)) huu)) huJ)
  have hVp2 : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card V := by
    intro p hp hp2 hdvd
    obtain ⟨a, ha⟩ := F.V_pgroup.exists_card_eq
    rw [ha] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hVn : ∀ g ∈ M, g ∈ normalizer (V : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => F.V_normal g hg x hx
    · intro hx
      have := F.V_normal g⁻¹ (inv_mem hg) _ hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
  by_cases hpref : ∃ y ∈ J, (orderOf y).Prime ∧ orderOf y ≠ 2 ∧ orderOf y ∣ 2 ^ n - 1
  ·
    obtain ⟨y, hyJ, hyp, hy2, hydvd⟩ := hpref
    set p := orderOf y with hp
    have : Fact p.Prime := ⟨hyp⟩
    obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := K) p (F.card_K ▸ hydvd)
    have hx'K : (x' : X) ∈ K := x'.2
    have hx'o : orderOf (x' : X) = p := by rw [Subgroup.orderOf_coe, hx']
    set E : Subgroup X := zpowers (x' : X) ⊔ zpowers y with hE
    have hxK : zpowers (x' : X) ≤ K := zpowers_le.mpr hx'K
    have hyJ' : zpowers y ≤ J := zpowers_le.mpr hyJ
    have hcommE : ∀ a ∈ zpowers (x' : X), ∀ b ∈ zpowers y, a * b = b * a := fun a ha b hb =>
      (F.J_comm (hyJ' hb) (F.K_le_L (hxK ha))).symm
    have hEpow : ∀ e : E, e ^ p = 1 := by
      intro e
      obtain ⟨a, ha, b, hb, hab⟩ := Bender.exists_mul_of_mem_sup_of_commute hcommE e.2
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, hab, (Commute.mul_pow (hcommE a ha b hb)), OneMemClass.coe_one]
      have h1 : a ^ p = 1 := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx'o,
          pow_orderOf_eq_one, one_zpow]
      have h2 : b ^ p = 1 := by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hb
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp,
          pow_orderOf_eq_one, one_zpow]
      rw [h1, h2, one_mul]
    have hEcard : Nat.card E = p ^ 2 := by
      have h1 : Nat.card E = Nat.card (zpowers (x' : X)) * Nat.card (zpowers y) := by
        refine card_sup_of_normal (fun b hb a ha => ?_) ?_
        · rw [← hcommE a ha b hb, mul_inv_cancel_right]
          exact ha
        · rw [eq_bot_iff]
          intro z hz
          exact mem_bot.mpr (F.eq_one_of_mem_K_J (hxK (mem_inf.mp hz).1) (hyJ' (mem_inf.mp hz).2))
      rw [h1, Nat.card_zpowers, Nat.card_zpowers, hx'o, pow_two]
    have hEN : E ≤ normalizer (V : Set X) := by
      have hEM : E ≤ M := sup_le (hxK.trans F.K_le_M) (hyJ'.trans F.J_le_M)
      exact fun e he => hVn e (hEM he)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      p hyp E V hEpow hEcard (hVp2 p hyp hy2) hEN
    apply hne
    refine le_antisymm ?_ hMoV
    rw [hgen]
    refine iSup₂_le fun e he => ?_
    intro v hv
    obtain ⟨hvV, hvC⟩ := mem_inf.mp hv
    obtain ⟨a, ha, b, hb, hab⟩ := Bender.exists_mul_of_mem_sup_of_commute hcommE e.2
    have he1 : a * b ≠ 1 := by
      rw [← hab]
      exact fun h1 => he (Subtype.ext h1)
    have hvw : v * (a * b) = (a * b) * v := by
      rw [← hab]
      exact mem_centralizer_singleton_iff.mp hvC
    exact F.cent_le_Mo h hyJ (hxK ha) hb he1 hvV hvw
  · push Not at hpref
    obtain ⟨y, hyJ, hyp, hy2⟩ : ∃ y ∈ J, (orderOf y).Prime ∧ orderOf y ≠ 2 := by
      by_contra hno
      push Not at hno
      apply hJ2
      refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
        fun {p} hp hpdvd => ?_)
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpdvd
      by_contra hp2
      have h1 := hno y y.2 (by rw [Subgroup.orderOf_coe, hy]; exact hp)
      rw [Subgroup.orderOf_coe, hy] at h1
      exact hp2 h1
    have hyodd : Odd (orderOf y) := hyp.odd_of_ne_two hy2
    obtain ⟨J', hJ'J, hJ'odd, hJcard⟩ := F.J_dihedral hJ2 fun y hy hp hp2 => hpref y hy hp hp2
    set A : Subgroup X := K ⊔ zpowers y with hA
    have hyJ' : zpowers y ≤ J := zpowers_le.mpr hyJ
    have hAM : A ≤ M := sup_le F.K_le_M (hyJ'.trans F.J_le_M)
    have hAcard : Nat.card A = (2 ^ n - 1) * orderOf y := by
      rw [F.card_K_sup hyJ', F.card_K, Nat.card_zpowers]
    have hdvd := card_dvd_index_sub_one (A := A) (P := V) (N := Mo) hMoV
      (fun a ha x hx => F.V_normal a (hAM ha) x hx) (fun a ha x hx => F.Mo_normal a (hAM ha) x hx)
      (fun a ha ha1 x hx hxa => F.fpf_quot h hyJ hyodd ha ha1 hx hxa)
    rw [hAcard] at hdvd
    obtain ⟨a, ha⟩ := F.V_pgroup.exists_card_eq
    have hcardsub : Nat.card ↥(Mo.subgroupOf V) = Nat.card Mo :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMoV).toEquiv
    have hidx : (Mo.subgroupOf V).index * 2 ^ n = 2 ^ a := by
      have h1 := Subgroup.card_mul_index (Mo.subgroupOf V)
      rw [hcardsub, F.card_Mo, ha] at h1
      rw [mul_comm]
      exact h1
    have hna : n ≤ a := by
      have hpos : 0 < (Mo.subgroupOf V).index := by
        rcases Nat.eq_zero_or_pos (Mo.subgroupOf V).index with h0 | h0
        · rw [h0, zero_mul] at hidx
          exact absurd hidx.symm (by positivity)
        · exact h0
      have h1 : 2 ^ n ≤ 2 ^ a := by
        rw [← hidx]
        exact Nat.le_mul_of_pos_left _ hpos
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have hidx' : (Mo.subgroupOf V).index = 2 ^ (a - n) := by
      have h1 : 2 ^ a = 2 ^ (a - n) * 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hna]
      rw [h1] at hidx
      exact Nat.eq_of_mul_eq_mul_right (by positivity) hidx
    rw [hidx'] at hdvd
    set m := a - n with hm
    have hq1 : 0 < 2 ^ n - 1 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by linarith [F.two_le])
      omega
    have hnm : n ∣ m := dvd_of_two_pow_sub_one_dvd (by linarith [F.two_le])
      (dvd_trans (Dvd.intro _ rfl) hdvd)
    have hm0 : m ≠ 0 := by
      intro hm0
      apply hne
      refine (eq_of_le_of_card_ge hMoV ?_).symm
      rw [ha, F.card_Mo]
      have : a = n := by omega
      rw [this]
    have hmn : m ≠ n := by
      intro hmn
      rw [hmn] at hdvd
      have h1 := Nat.le_of_dvd hq1 hdvd
      have h2 : 2 ≤ orderOf y := hyp.two_le
      nlinarith
    obtain ⟨c, hc⟩ := hnm
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc
        exact absurd hc hm0
      · simp at hc
        exact absurd hc hmn
      · omega
    have hV3 : 2 ^ (3 * n) ≤ Nat.card V := by
      rw [ha]
      apply Nat.pow_le_pow_right (by norm_num)
      have : a = n + m := by omega
      rw [this, hc]
      nlinarith
    have hVDcard : Nat.card ↥(V ⊔ D) = Nat.card V * Nat.card D :=
      card_sup_of_normal (fun d hd x hx => F.V_normal d (F.D_le hd) x hx) hVD
    have hVDM : V ⊔ D ≤ M := sup_le F.V_le F.D_le
    have hle : Nat.card ↥(V ⊔ D) ≤ Nat.card M := Subgroup.card_le_of_le hVDM
    rw [hVDcard, F.card_M] at hle
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have hVeq : Nat.card V = 2 ^ (3 * n) := le_antisymm (Nat.le_of_mul_le_mul_right hle hDpos) hV3
    have hsupM : V ⊔ D = M := by
      refine eq_of_le_of_card_ge hVDM ?_
      rw [hVDcard, F.card_M, hVeq]
    have hsup : ∀ g ∈ M, ∃ x ∈ V, ∃ d ∈ D, g = x * d := by
      intro g hg
      rw [← hsupM] at hg
      exact exists_mul_of_sup_eq (fun d hd x hx => F.V_normal d (F.D_le hd) x hx) hg
    have hJ'D : ∀ d ∈ D, ∀ x ∈ J', d * x * d⁻¹ ∈ J' := by
      intro d hd x hx
      have hxJ := hJ'J hx
      refine (hJ'odd _ (F.D_conj_J hd hxJ)).mpr ?_
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact (hJ'odd x hxJ).mp hx
    have hAD : K ⊔ J ≤ D := sup_le F.K_le_D F.J_le_D
    have hNA : K ⊔ J' ≤ K ⊔ J := sup_le le_sup_left (hJ'J.trans le_sup_right)
    have hcomm := comm_mem_of_cyclic_quotient hAD hNA
      (fun d hd x hx => conj_mem_sup (fun k hk => F.D_conj_K hd hk) (fun j hj => F.D_conj_J hd hj) hx)
      (fun d hd x hx => conj_mem_sup (fun k hk => F.D_conj_K hd hk) (fun j hj => hJ'D d hd j hj) hx)
      (by rw [F.card_K_sup le_rfl, F.card_K_sup hJ'J, hJcard]; ring) F.out_cyclic
    have hNodd : Odd (Nat.card ↥(K ⊔ J')) := by
      rw [F.card_K_sup hJ'J]
      exact F.odd_card_K.mul (odd_card_of_forall_odd fun x hx => (hJ'odd x (hJ'J hx)).mp hx)
    have huN : u ∉ K ⊔ J' := fun hu => hu1 (eq_one_of_mem_odd hNodd hu huu)
    have hu' := not_mem_closure_odd_of_comm (hNA.trans hAD) hcomm (F.J_le_D huJ) huu huN
    have hu'' := not_mem_closure_odd_of_complement F.D_le F.V_le F.V_normal hsup hVD
      (F.J_le_D huJ) hu'
    rw [F.oddGen] at hu''
    exact hu'' (F.J_le_M huJ)

end Facts15

end CFSG.GH74.Uniqueness
