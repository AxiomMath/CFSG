module

public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Psl2Subgroups

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Section15Bender

theorem isPGroup_two_of_forall_prime {G : Type*} [Group G] [Finite G]
    (h : ∀ y : G, (orderOf y).Prime → orderOf y = 2) : IsPGroup 2 G := by
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_⟩
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' d hdvd
  have h2 := h y (by rw [hy]; exact hd)
  omega

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_pow_eq_one_of_isPGroup_zpowers {G : Type*} [Group G] {x : G}
    (hx : IsPGroup 2 (zpowers x)) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem mem_iff_odd_orderOf_of_card_eq {G : Type*} [Group G] (N : Subgroup G)
    (hcard : Nat.card G = 2 * Nat.card N) (hodd : Odd (Nat.card N)) (g : G) :
    g ∈ N ↔ Odd (orderOf g) := by
  have hpos : 0 < Nat.card N := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hidx : N.index = 2 := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [N.card_mul_index, hcard, mul_comm]
  have : N.Normal := Subgroup.normal_of_index_eq_two hidx
  constructor
  · intro hg
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hg)
  · rintro ⟨k, hk⟩
    have h1 : g ^ (2 * (k + 1)) = g := by
      rw [show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    have h2 : g ^ 2 ∈ N := by
      have := Subgroup.pow_index_mem N g
      rwa [hidx] at this
    rw [← h1, pow_mul]
    exact N.pow_mem h2 _

omit [Finite X] in
theorem exists_odd_index_two_of_subgroup {J : Subgroup X} (N : Subgroup ↥J)
    (hcard : Nat.card ↥J = 2 * Nat.card N) (hodd : Odd (Nat.card N)) :
    ∃ J' : Subgroup X, J' ≤ J ∧ (∀ j ∈ J, j ∈ J' ↔ Odd (orderOf j)) ∧
      Nat.card J = 2 * Nat.card J' := by
  refine ⟨N.map J.subtype, Subgroup.map_subtype_le N, fun j hj => ?_, ?_⟩
  · have h1 := mem_iff_odd_orderOf_of_card_eq N hcard hodd ⟨j, hj⟩
    rw [Subgroup.orderOf_mk] at h1
    rw [← h1]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hjN
      exact ⟨⟨j, hj⟩, hjN, rfl⟩
  · rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hcard

theorem orderOf_dvd_of_mem_borel_of_odd
    {K : Type*} [Group K] [Finite K] {n : ℕ}
    (hK : Bender.BenderType K n 1 1) (Q : Sylow 2 K) {y : K}
    (hy : y ∈ Bender.borel (Q : Subgroup K)) (hodd : Odd (orderOf y)) :
    orderOf y ∣ 2 ^ n - 1 := by
  obtain ⟨t, hcore⟩ := hK.exists_benderCore Q
  obtain ⟨q', -, hconj⟩ := hcore.exists_conj_cartan_of_odd Q.isPGroup' (A := zpowers y)
    (Subgroup.zpowers_le.mpr hy) (by rw [Nat.card_zpowers]; exact hodd)
  have hd := hconj y (Subgroup.mem_zpowers y)
  have h1 : orderOf (q' * y * q'⁻¹) = orderOf y := MulEquiv.orderOf_eq (MulAut.conj q') y
  have h2 := Subgroup.orderOf_dvd_natCard _ hd
  rw [h1, hcore.card_cartan, mul_one] at h2
  exact h2

end Section15Bender

open Section15Bender

omit [Finite X] in
theorem bender_J_prime {K : Type} [Group K] [Finite K] {n : ℕ} (hK : Bender.BenderType K n 1 1)
    (J : Subgroup X) (f : ↥J →* K) (hf : Function.Injective f) :
    ∀ y ∈ J, (orderOf y).Prime → orderOf y ≠ 2 → orderOf y ∣ 2 ^ n - 1 ∨ orderOf y ∣ 2 ^ n + 1 := by
  intro y hy hp hp2
  have hodd : Odd (orderOf y) := hp.odd_of_ne_two hp2
  have hxord : orderOf (f ⟨y, hy⟩) = orderOf y := by
    rw [orderOf_injective f hf, Subgroup.orderOf_mk]
  have hx1 : f ⟨y, hy⟩ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact hp.one_lt.ne hxord
  obtain ⟨-, hcard, -⟩ := hK.linear_odd_element hx1 (by rw [hxord]; exact hodd)
  have hxC : f ⟨y, hy⟩ ∈ centralizer ({f ⟨y, hy⟩} : Set K) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
  have hdvd := Subgroup.orderOf_dvd_natCard _ hxC
  rw [hxord] at hdvd
  rcases hcard with h | h
  · left
    rwa [h] at hdvd
  · right
    rwa [h] at hdvd

omit [Finite X] in
theorem bender_J_dihedral
    {K : Type} [Group K] [Finite K] {n : ℕ}
    (hK : Bender.BenderType K n 1 1) (J : Subgroup X) (f : ↥J →* K) (hf : Function.Injective f)
    (hev : ∃ u ∈ J, orderOf u = 2) (h2 : ¬ IsPGroup 2 J)
    (hcop : ∀ y ∈ J, (orderOf y).Prime → orderOf y ≠ 2 → ¬ orderOf y ∣ 2 ^ n - 1) :
    ∃ J' : Subgroup X, J' ≤ J ∧ (∀ j ∈ J, j ∈ J' ↔ Odd (orderOf j)) ∧
      Nat.card J = 2 * Nat.card J' := by
  have : Finite ↥J := Finite.of_injective f hf
  let e : ↥J ≃* ↥f.range := MonoidHom.ofInjective hf
  have hcardJ : Nat.card ↥J = Nat.card ↥f.range := Nat.card_congr e.toEquiv
  rcases hK.linear_subgroup_cases f.range with h1 | ⟨-, -, hodd⟩ | ⟨z, -, hzodd, hzcard, ⟨φ⟩⟩ |
      ⟨-, Q, hQ⟩ | ⟨m, hm2, hmn, ⟨φ⟩⟩ | h6
  ·
    exact absurd (h1.of_injective e.toMonoidHom e.injective) h2
  ·
    exfalso
    obtain ⟨u, hu, hu2⟩ := hev
    have hdvd : 2 ∣ Nat.card ↥f.range := by
      rw [← hcardJ, ← hu2]
      exact Subgroup.orderOf_dvd_natCard J hu
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  ·
    let ψ : ↥J ≃* DihedralGroup z := e.trans φ
    let N : Subgroup ↥J := (zpowers (DihedralGroup.r (1 : ZMod z))).map ψ.symm.toMonoidHom
    have hNcard : Nat.card N = z := by
      rw [Subgroup.card_map_of_injective ψ.symm.injective, Nat.card_zpowers,
        DihedralGroup.orderOf_r_one]
    exact exists_odd_index_two_of_subgroup N (by rw [hcardJ, hzcard, hNcard])
      (by rw [hNcard]; exact hzodd)
  ·
    exfalso
    apply h2
    apply isPGroup_two_of_forall_prime
    intro y hy
    by_contra hy2
    have hodd : Odd (orderOf (f y)) := by
      rw [orderOf_injective f hf]
      exact hy.odd_of_ne_two hy2
    have hyM : f y ∈ Bender.borel (Q : Subgroup K) := hQ ⟨y, rfl⟩
    have hdvd := orderOf_dvd_of_mem_borel_of_odd hK Q hyM hodd
    rw [orderOf_injective f hf] at hdvd
    exact hcop (y : X) y.2 (by rw [Subgroup.orderOf_coe]; exact hy)
      (by rw [Subgroup.orderOf_coe]; exact hy2) (by rw [Subgroup.orderOf_coe]; exact hdvd)
  ·
    exfalso
    have hcardPSL : Nat.card ↥J = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [hcardJ, Nat.card_congr φ.toEquiv, Bender.card_psl2_even m (by omega)]
    have hm4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ m - 1) (by omega)
    have : Fact p.Prime := ⟨hp⟩
    have hpJ : p ∣ Nat.card ↥J := by
      rw [hcardPSL]
      exact Dvd.dvd.mul_left (hpd.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ m) 2)) _
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpJ
    have hodd : Odd (2 ^ m - 1) := Bender.odd_two_pow_sub_one m (by omega)
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
    refine hcop (y : X) y.2 ?_ ?_ ?_
    · rw [Subgroup.orderOf_coe, hy]
      exact hp
    · rw [Subgroup.orderOf_coe, hy]
      exact hp2
    · rw [Subgroup.orderOf_coe, hy]
      exact hpd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmn)
  ·
    have h3 : 3 ∣ Nat.card ↥J := by
      rw [hcardJ, h6]
      norm_num
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hNcard : Nat.card (zpowers y) = 3 := by rw [Nat.card_zpowers, hy]
    exact exists_odd_index_two_of_subgroup (zpowers y) (by rw [hcardJ, h6, hNcard])
      (by rw [hNcard]; exact ⟨1, by norm_num⟩)

omit [Finite X] in
theorem bender_J_frob
    {K : Type} [Group K] [Finite K] {n : ℕ} (hK : Bender.BenderType K n 1 1)
    (J : Subgroup X) (f : ↥J →* K) (hf : Function.Injective f)
    (hW : ∃ W : Subgroup X, W ≤ J ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧
      ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W) :
    ∃ U Y : Subgroup X, U ≤ J ∧ Y ≤ J ∧ IsPGroup 2 U ∧
      (∀ j ∈ J, IsPGroup 2 (zpowers j) → j ∈ U) ∧ (∀ x ∈ U, x * x = 1) ∧
      Odd (Nat.card Y) ∧ Nat.card Y ∣ 2 ^ n - 1 ∧ (∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) ∧
      (∀ j ∈ J, ∃ x ∈ U, ∃ y ∈ Y, j = x * y) ∧
      (∀ y ∈ Y, y ≠ 1 → ∀ x ∈ U, y * x = x * y → x = 1) := by
  classical
  have : Finite ↥J := Finite.of_injective f hf
  obtain ⟨W, hWJ, hW1, hW2, hWn⟩ := hW
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 K, f.range ≤ Bender.borel (Q : Subgroup K) := by
    let e : ↥J ≃* ↥f.range := MonoidHom.ofInjective hf
    let W₁ : Subgroup ↥J := W.subgroupOf J
    have hW₁n : W₁.Normal := ⟨fun w hw g => by
      change (g : X) * (w : X) * (g : X)⁻¹ ∈ W
      exact hWn g g.2 w hw⟩
    have hW₁2 : IsPGroup 2 W₁ := hW2.of_injective (Subgroup.subgroupOfEquivOfLe hWJ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWJ).injective
    have : (W₁.map e.toMonoidHom).Normal := hW₁n.map e.toMonoidHom e.surjective
    refine hK.exists_le_borel_of_normal f.range (W₁.map e.toMonoidHom) (hW₁2.map e.toMonoidHom) ?_
    intro hbot
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    have h1 : e ⟨w, hWJ hw⟩ ∈ W₁.map e.toMonoidHom := ⟨⟨w, hWJ hw⟩, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨w, hWJ hw⟩ : ↥J) = 1 := e.injective (by rw [h1, map_one])
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h2)
  obtain ⟨t, hcore⟩ := hK.exists_benderCore Q
  have hQ2 : IsPGroup 2 (Q : Subgroup K) := Q.isPGroup'
  have hfM : ∀ g : ↥J, f g ∈ Bender.borel (Q : Subgroup K) := fun g => hQ ⟨g, rfl⟩
  have hmemQ : ∀ x ∈ Bender.borel (Q : Subgroup K), IsPGroup 2 (zpowers x) →
      x ∈ (Q : Subgroup K) := by
    intro x hx hxp
    have hx' : x ∈ normalizer (Q : Set K) := hx
    have h1 : x ∈ zpowers x ⊓ normalizer (Q : Set K) := ⟨Subgroup.mem_zpowers x, hx'⟩
    rw [hxp.inf_normalizer_sylow Q] at h1
    exact h1.2
  have hsqQ : ∀ x ∈ (Q : Subgroup K), x * x = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hx⟩
    exact hK.sq_eq_one_of_two_pow_linear (k := k) (by simpa using congrArg Subtype.val hk)
  let U₁ : Subgroup ↥J := (Q : Subgroup K).comap f
  have hmemU₁ : ∀ u : ↥J, u ∈ U₁ ↔ f u ∈ (Q : Subgroup K) := fun u => Iff.rfl
  have hU₁n : U₁.Normal := ⟨fun u hu g => by
    rw [hmemU₁, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hfM g) (f u)).mp ((hmemU₁ u).mp hu)⟩
  have hU₁2 : IsPGroup 2 U₁ := hQ2.comap_of_injective f hf
  obtain ⟨S, -⟩ : ∃ S : Sylow 2 ↥J, True := ⟨default, trivial⟩
  have hSU : (S : Subgroup ↥J) ≤ U₁ := by
    intro s hs
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine hmemQ (f s) (hfM s) (isPGroup_zpowers_of_pow_eq_one (k := k) ?_)
    rw [← map_pow, hk', map_one]
  have hU₁odd : Odd U₁.index := by
    have h1 : U₁.index ∣ (S : Subgroup ↥J).index := Subgroup.index_dvd_of_le hSU
    have h2 : ¬ 2 ∣ (S : Subgroup ↥J).index := S.not_dvd_index
    refine Nat.not_even_iff_odd.mp fun he => h2 ((even_iff_two_dvd.mp he).trans h1)
  have hcop : (Nat.card U₁).Coprime U₁.index := by
    obtain ⟨a, ha⟩ := hU₁2.exists_card_eq
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hU₁odd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = U₁.index := hH.symm.index_eq_card.symm
  obtain ⟨q', hq', hconj⟩ : ∃ q' ∈ (Q : Subgroup K), ∀ a ∈ H.map f,
      q' * a * q'⁻¹ ∈ Bender.cartan (Q : Subgroup K) t := by
    refine hcore.exists_conj_cartan_of_odd hQ2 ?_ ?_
    · rintro _ ⟨h, -, rfl⟩
      exact hfM h
    · rw [Subgroup.card_map_of_injective hf, hHcard]
      exact hU₁odd
  let g : ↥H →* K := (MulAut.conj q').toMonoidHom.comp (f.comp H.subtype)
  have hg_inj : Function.Injective g :=
    (MulAut.conj q').injective.comp (hf.comp H.subtype_injective)
  have hgC : ∀ h : ↥H, g h ∈ Bender.cartan (Q : Subgroup K) t := fun h => hconj _ ⟨h, h.2, rfl⟩
  let ι : ↥H →* ↥(Bender.cartan (Q : Subgroup K) t) := g.codRestrict _ hgC
  have hι : Function.Injective ι := fun a b hab => hg_inj (congrArg Subtype.val hab)
  have hHdvd : Nat.card H ∣ 2 ^ n - 1 := by
    have h1 := Subgroup.card_dvd_of_injective ι hι
    rwa [hcore.card_cartan, mul_one] at h1
  have hHcomm : ∀ a b : ↥H, a * b = b * a := fun a b => by
    apply hg_inj
    rw [map_mul, map_mul]
    exact hcore.cartan_comm (hgC a) (hgC b)
  refine ⟨U₁.map J.subtype, H.map J.subtype, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    hU₁2.map J.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hjp
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup_zpowers hjp
    have hk' : (⟨j, hj⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have h1 : f ⟨j, hj⟩ ∈ (Q : Subgroup K) := by
      refine hmemQ _ (hfM _) (isPGroup_zpowers_of_pow_eq_one (k := k) ?_)
      rw [← map_pow, hk', map_one]
    exact ⟨⟨j, hj⟩, h1, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    have h1 : f u * f u = 1 := hsqQ (f u) hu
    have h2 : u * u = 1 := hf (by rw [map_mul, h1, map_one])
    simpa using congrArg Subtype.val h2
  · rw [Subgroup.card_map_of_injective J.subtype_injective, hHcard]
    exact hU₁odd
  · rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hHdvd
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa using congrArg (fun x : ↥H => ((x : ↥J) : X)) (hHcomm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro j hj
    obtain ⟨⟨u, h⟩, huh⟩ := hH.2 ⟨j, hj⟩
    refine ⟨(u : ↥J), ⟨u, u.2, rfl⟩, (h : ↥J), ⟨h, h.2, rfl⟩, ?_⟩
    have h1 := congrArg Subtype.val huh
    exact h1.symm
  · rintro _ ⟨h, hh, rfl⟩ hy1 _ ⟨u, hu, rfl⟩ hcomm
    have hh1 : h ≠ 1 := fun e => hy1 (by rw [e]; rfl)
    have hhu : h * u = u * h := Subtype.ext hcomm
    have hfhu : f h * f u = f u * f h := by rw [← map_mul, ← map_mul, hhu]
    have hdC : q' * f h * q'⁻¹ ∈ Bender.cartan (Q : Subgroup K) t := hconj _ ⟨h, hh, rfl⟩
    have hu' : f u ∈ (Q : Subgroup K) := hu
    have hx'Q : q' * f u * q'⁻¹ ∈ (Q : Subgroup K) :=
      (Q : Subgroup K).mul_mem ((Q : Subgroup K).mul_mem hq' hu') ((Q : Subgroup K).inv_mem hq')
    have hdx : (q' * f u * q'⁻¹) * (q' * f h * q'⁻¹) = (q' * f h * q'⁻¹) * (q' * f u * q'⁻¹) := by
      calc (q' * f u * q'⁻¹) * (q' * f h * q'⁻¹) = q' * (f u * f h) * q'⁻¹ := by group
        _ = q' * (f h * f u) * q'⁻¹ := by rw [hfhu]
        _ = (q' * f h * q'⁻¹) * (q' * f u * q'⁻¹) := by group
    by_contra hu1
    have hu1' : u ≠ 1 := fun e => hu1 (by rw [e]; rfl)
    have hfu1 : q' * f u * q'⁻¹ ≠ 1 := by
      intro e
      apply hu1'
      apply hf
      rw [map_one]
      calc f u = q'⁻¹ * (q' * f u * q'⁻¹) * q' := by group
        _ = 1 := by rw [e]; group
    have hrc : q' * f u * q'⁻¹ ∈ Bender.rootCenter (Q : Subgroup K) :=
      hcore.mem_rootCenter_of_mul_self hx'Q (hsqQ _ hx'Q)
    have hdD : q' * f h * q'⁻¹ ∈ Bender.cartan (Q : Subgroup K) t ⊓
        centralizer ({q' * f u * q'⁻¹} : Set K) := by
      refine ⟨hdC, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hdx
    rw [hcore.cartan_inf_centralizer_eq hrc hfu1, hcore.fixCartan_eq_bot, Subgroup.mem_bot] at hdD
    apply hh1
    apply hf
    rw [map_one]
    calc f h = q'⁻¹ * (q' * f h * q'⁻¹) * q' := by group
      _ = 1 := by rw [hdD]; group

end CFSG.GH74.Uniqueness
