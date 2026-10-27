module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification

section Orders

@[expose] def KOrder (n : ℕ) : Prop :=
  n = 168 ∨ n = 360 ∨ ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ p * (p * p - 1) = 2 * n

theorem IsKType.kOrder {G : Type} [Group G] {K : Subgroup G} (hK : IsKType K) :
    KOrder (Nat.card ↥K) :=
  isKType_card hK

theorem eq_of_two_pow_mul_odd_eq {a c u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ c * v) : a = c := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hac | hac
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hac
    have h2 : u = 2 ^ (d + 1) * v := by
      refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ a) ?_
      calc 2 ^ a * u = 2 ^ (a + d + 1) * v := h
        _ = 2 ^ a * (2 ^ (d + 1) * v) := by ring
    have hev : Even (2 ^ (d + 1)) := Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero d⟩
    exact (Nat.not_even_iff_odd.mpr hu) (by rw [h2]; exact hev.mul_right v)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hac
    have h2 : v = 2 ^ (d + 1) * u := by
      refine Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ c) ?_
      calc 2 ^ c * v = 2 ^ (c + d + 1) * u := h.symm
        _ = 2 ^ c * (2 ^ (d + 1) * u) := by ring
    have hev : Even (2 ^ (d + 1)) := Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero d⟩
    exact (Nat.not_even_iff_odd.mpr hv) (by rw [h2]; exact hev.mul_right u)

theorem KOrder.false_of_two_adic {n b m : ℕ} (hn : KOrder n) (hb : 2 ≤ b) (hm : Odd m)
    (h : n = 2 ^ (3 * b) * m) : False := by
  have h64 : 64 ∣ n := by
    rw [h]
    refine Dvd.dvd.mul_right ?_ m
    have : 2 ^ 6 ∣ 2 ^ (3 * b) := pow_dvd_pow 2 (by omega)
    simpa using this
  have hb0 : 0 < 2 ^ b := by positivity
  have hb4 : 4 ≤ 2 ^ b := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hblt : 2 ^ b < 2 ^ (3 * b) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hn with rfl | rfl | ⟨p, hp, hp7, hpn⟩
  · omega
  · omega
  · have hpp : p.Prime := hp.1
    rcases Unc25K1.fermat_or_mersenne_pow hp hp7 with ⟨hp8, s, hs⟩ | ⟨hp8, s, hs⟩
    ·
      have hs3 : 3 ≤ s := by
        by_contra hlt
        have : 2 ^ s ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hX : 2 ^ (s' + 1) = 2 * 2 ^ s' := by rw [pow_succ]; ring
      have hp' : p = 2 * 2 ^ s' + 1 := by omega
      have hpp1 : p * p - 1 = 4 * 2 ^ s' * (2 ^ s' + 1) := by
        have : p * p = 4 * 2 ^ s' * (2 ^ s' + 1) + 1 := by rw [hp']; ring
        omega
      have h1 : p * (p * p - 1) =
          2 * (2 * 2 ^ s' * ((2 * 2 ^ s' + 1) * (2 ^ s' + 1))) := by
        rw [hpp1, hp']; ring
      have hn' : n = 2 ^ (s' + 1) * ((2 * 2 ^ s' + 1) * (2 ^ s' + 1)) := by
        have h2n : 2 * n = 2 * (2 * 2 ^ s' * ((2 * 2 ^ s' + 1) * (2 ^ s' + 1))) :=
          hpn.symm.trans h1
        rw [hX]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2n
      have hodd : Odd ((2 * 2 ^ s' + 1) * (2 ^ s' + 1)) := by
        refine Odd.mul (odd_two_mul_add_one _) ?_
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩ : Even (2 ^ s')).add_one
      have hsb : 3 * b = s' + 1 := eq_of_two_pow_mul_odd_eq hm hodd (h.symm.trans hn')
      have hs' : p = 2 ^ (3 * b) + 1 := by rw [hs, hsb]
      have hdvd : 2 ^ b + 1 ∣ p := by
        rw [hs', pow_mul' 2 3 b]
        simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ b) 1 (by decide : Odd 3)
      rcases hpp.eq_one_or_self_of_dvd _ hdvd with h1 | h1 <;> omega
    ·
      have hs4 : 4 ≤ s := by
        by_contra hlt
        have : 2 ^ s ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have hX : 2 ^ (s' + 1) = 2 * 2 ^ s' := by rw [pow_succ]; ring
      have hYpos : 1 ≤ 2 ^ s' := Nat.one_le_two_pow
      obtain ⟨W, hW⟩ : ∃ W, 2 ^ s' = W + 1 := ⟨2 ^ s' - 1, by omega⟩
      have hp' : p = 2 * W + 1 := by omega
      have hpp1 : p * p - 1 = 4 * W * (W + 1) := by
        have : p * p = 4 * W * (W + 1) + 1 := by rw [hp']; ring
        omega
      have h1 : p * (p * p - 1) = 2 * (2 * (W + 1) * (p * W)) := by
        rw [hpp1]; ring
      have hn' : n = 2 ^ (s' + 1) * (p * W) := by
        have h2n : 2 * n = 2 * (2 * (W + 1) * (p * W)) := hpn.symm.trans h1
        rw [hX, hW]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2n
      have hWodd : Odd W := by
        have hev : Even (2 ^ s') := Nat.even_pow.mpr ⟨even_two, by omega⟩
        rw [hW] at hev
        rcases Nat.even_add_one.mp hev with h
        exact Nat.not_even_iff_odd.mp h
      have hpodd : Odd p := by rw [hp']; exact odd_two_mul_add_one W
      have hsb : 3 * b = s' + 1 := eq_of_two_pow_mul_odd_eq hm (hpodd.mul hWodd) (h.symm.trans hn')
      have hs' : p + 1 = 2 ^ (3 * b) := by rw [hs, hsb]
      have hdvd : 2 ^ b - 1 ∣ p := by
        have h3 := Nat.sub_dvd_pow_sub_pow (2 ^ b) 1 3
        rw [one_pow, ← pow_mul'] at h3
        have : p = 2 ^ (3 * b) - 1 := by omega
        rwa [this]
      rcases hpp.eq_one_or_self_of_dvd _ hdvd with h1 | h1 <;> omega

end Orders

section Components

@[expose] def HasKComponent (Q : Type*) [Group Q] : Prop :=
  ∃ B : Subgroup Q, CFSG.IsComponent B ∧ KOrder (Nat.card ↥B)

theorem HasKComponent.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : HasKComponent Q) : HasKComponent Q' := by
  obtain ⟨B, hB, hK⟩ := h
  refine ⟨B.map e.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv e hB, ?_⟩
  rwa [← Nat.card_congr (B.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]

theorem isComponent_eq_top_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    {B : Subgroup Q} (hB : CFSG.IsComponent B) : B = ⊤ := by
  have hsub : ∀ U : Subgroup Q, U.IsSubnormal → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    induction hU with
    | top => exact Or.inr rfl
    | step A L hAL _ hAn ih =>
      rcases ih with rfl | rfl
      · exact Or.inl (le_bot_iff.mp hAL)
      · have hn : A.Normal := ⟨fun n hn g => by
          have := hAn.conj_mem ⟨n, trivial⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨g, trivial⟩
          exact Subgroup.mem_subgroupOf.mp this⟩
        have := hn
        exact IsSimpleGroup.eq_bot_or_eq_top_of_normal A
  rcases hsub B hB.2 with h | h
  · exfalso
    have := CFSG.LocalCores.isQuasisimple_nontrivial hB.1
    obtain ⟨⟨x, hx⟩, hx1⟩ := (nontrivial_iff_exists_ne (1 : ↥B)).mp this
    exact hx1 (Subtype.ext (by simpa [h] using hx))
  · exact h

theorem not_hasKComponent_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q] {b m : ℕ}
    (hb : 2 ≤ b) (hm : Odd m) (hcard : Nat.card Q = 2 ^ (3 * b) * m) : ¬ HasKComponent Q := by
  rintro ⟨B, hB, hK⟩
  have h := isComponent_eq_top_of_isSimpleGroup hB
  subst h
  rw [Subgroup.card_top, hcard] at hK
  exact hK.false_of_two_adic hb hm rfl

theorem le_commutator_of_isQuasisimple {Q : Type*} [Group Q] {B : Subgroup Q}
    (h : CFSG.IsQuasisimple ↥B) : B ≤ commutator Q := by
  have h1 : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp h.1
  calc B = ⁅B, B⁆ := h1.symm
    _ ≤ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator Q := (commutator_def Q).symm

theorem not_hasKComponent_of_commutator_simple {Q : Type*} [Group Q]
    [IsSimpleGroup ↥(commutator Q)] (h : ¬ KOrder (Nat.card ↥(commutator Q))) :
    ¬ HasKComponent Q := by
  rintro ⟨B, hB, hK⟩
  have hBle : B ≤ commutator Q := le_commutator_of_isQuasisimple hB.1
  have htop := isComponent_eq_top_of_isSimpleGroup (CFSG.LocalCores.component_overgroup hB hBle)
  have hBeq : B = commutator Q := le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
  rw [hBeq] at hK
  exact h hK

end Components

section Fixed

abbrev fixSubgroup {H : Type*} [Group H] (a : MulAut H) : Subgroup H :=
  MonoidHom.eqLocus a.toMonoidHom (MonoidHom.id H)

theorem mem_fixSubgroup {H : Type*} [Group H] {a : MulAut H} {x : H} :
    x ∈ fixSubgroup a ↔ a x = x :=
  Iff.rfl

theorem fixSubgroup_eq_map {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') (a : MulAut H)
    (a' : MulAut H') (h : ∀ y, a' (e y) = e (a y)) :
    fixSubgroup a' = (fixSubgroup a).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show a (e.symm y) = e.symm y
    apply e.injective
    rw [← h, e.apply_symm_apply]
    exact hy
  · rintro ⟨z, hz, rfl⟩
    show a' (e z) = e z
    rw [h]
    exact congrArg e hz

theorem hasKComponent_fixSubgroup_of_intertwine {H H' : Type*} [Group H] [Group H']
    (e : H ≃* H') (a : MulAut H) (a' : MulAut H') (h : ∀ y, a' (e y) = e (a y))
    (hK : HasKComponent ↥(fixSubgroup a)) : HasKComponent ↥(fixSubgroup a') :=
  hK.of_mulEquiv (((fixSubgroup a).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (fixSubgroup_eq_map e a a' h).symm))

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.conjAut_eq_self_iff (hs : IdentSetting X K t) (y : ↥X) :
    hs.conjAut y = y ↔ (y : G) ∈ Subgroup.centralizer ({t} : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : t⁻¹ * (y : G) * t = y := by
      have := congrArg Subtype.val h
      rwa [hs.coe_conjAut] at this
    calc (y : G) * t = t * (t⁻¹ * (y : G) * t) := by group
      _ = t * y := by rw [h1]
  · intro h
    exact hs.conjAut_of_mem_cent h

theorem IdentSetting.hasKComponent_fix [Finite G] (hs : IdentSetting X K t) :
    HasKComponent ↥(fixSubgroup (hs.conjAut : MulAut ↥X)) := by
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  have heq : C.subgroupOf X = fixSubgroup (hs.conjAut : MulAut ↥X) := by
    ext y
    rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
    exact ⟨fun h => (hs.conjAut_eq_self_iff y).mpr h.2,
      fun h => ⟨y.2, (hs.conjAut_eq_self_iff y).mp h⟩⟩
  let ε : ↥C ≃* ↥(fixSubgroup (hs.conjAut : MulAut ↥X)) :=
    (Subgroup.subgroupOfEquivOfLe hCX).symm.trans (MulEquiv.subgroupCongr heq)
  refine ⟨(K.subgroupOf C).map ε.toMonoidHom,
    CFSG.LocalCores.isComponent_map_mulEquiv ε hs.comp.2, ?_⟩
  have hcard : Nat.card ↥((K.subgroupOf C).map ε.toMonoidHom) = Nat.card ↥K := by
    rw [← Nat.card_congr ((K.subgroupOf C).equivMapOfInjective ε.toMonoidHom ε.injective).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.comp.1).toEquiv
  rw [hcard]
  exact hs.ktype.kOrder

theorem mulAut_congr_apply_self {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') (a : MulAut H)
    (y : H) : (MulAut.congr e a) (e y) = e (a y) := by
  show e (a (e.symm (e y))) = e (a y)
  rw [MulEquiv.symm_apply_apply]

theorem IdentSetting.hasKComponent_fix_congr [Finite G] (hs : IdentSetting X K t) {Γ : Type*}
    [Group Γ] (e : ↥X ≃* Γ) :
    HasKComponent ↥(fixSubgroup (MulAut.congr e (hs.conjAut : MulAut ↥X))) :=
  hasKComponent_fixSubgroup_of_intertwine e _ _
    (mulAut_congr_apply_self e _) hs.hasKComponent_fix

theorem IdentSetting.conjAut_mem_inner_of_congr_mem (hs : IdentSetting X K t) {Γ : Type*}
    [Group Γ] (e : ↥X ≃* Γ)
    (hmem : MulAut.congr e (hs.conjAut : MulAut ↥X) ∈ OuterAutomorphisms.inner Γ) :
    (hs.conjAut : MulAut ↥X) ∈ OuterAutomorphisms.inner ↥X := by
  rw [← OuterAutomorphisms.inner_map_congr e] at hmem
  obtain ⟨β, hβ, hβe⟩ := hmem
  have : β = hs.conjAut := (MulAut.congr e).injective hβe
  rwa [this] at hβ

theorem IdentSetting.conjAut_mul_self (hs : IdentSetting X K t) :
    (hs.conjAut : MulAut ↥X) * hs.conjAut = 1 :=
  MulEquiv.ext fun y => hs.conjAut_conjAut y

end Fixed

section Inner

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem hasKComponent_of_fixSubgroup_one {Γ : Type*} [Group Γ]
    (h : HasKComponent ↥(fixSubgroup (1 : MulAut Γ))) : HasKComponent Γ :=
  h.of_mulEquiv ((MulEquiv.subgroupCongr ((Subgroup.eq_top_iff' _).mpr fun _ => rfl)).trans
    Subgroup.topEquiv)

theorem fixSubgroup_conj {Γ : Type*} [Group Γ] (x : Γ) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set Γ) := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * x = (x * y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h]
      _ = y := by group

theorem not_hasKComponent_fix_of_inner {Γ : Type*} [Group Γ] (hZ : Subgroup.center Γ = ⊥)
    (hfree : ∀ y : Γ, orderOf y = 2 →
      ∀ B : Subgroup ↥(Subgroup.centralizer ({y} : Set Γ)), ¬ CFSG.IsComponent B)
    {a : MulAut Γ} (haa : a * a = 1) (ha1 : a ≠ 1) (hin : a ∈ inner Γ) :
    ¬ HasKComponent ↥(fixSubgroup a) := by
  obtain ⟨x, rfl⟩ := hin
  have hxx : x * x = 1 := by
    apply conj_injective_of_center_bot hZ
    rw [map_mul, haa, map_one]
  have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two, hxx]) hx1
  intro h
  obtain ⟨B, hB, -⟩ := h.of_mulEquiv (MulEquiv.subgroupCongr (fixSubgroup_conj x))
  exact hfree x hord B hB

end Inner

section Centralizer

theorem centralizer_zpowers_eq {H : Type*} [Group H] (y : H) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup H) : Set H) =
      Subgroup.centralizer ({y} : Set H) := by
  refine le_antisymm (Subgroup.centralizer_le (by simp)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro h hh
  rw [SetLike.mem_coe] at hh
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (show Commute y z from hz y (Set.mem_singleton y)) n).eq

end Centralizer

end CFSG.QuasithinUnique.Id2519
