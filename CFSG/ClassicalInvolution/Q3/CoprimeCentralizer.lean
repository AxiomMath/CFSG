module

public import CFSG.ClassicalInvolution.Q3.Subnormal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

universe u

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

section Abstract

variable {p : ℕ}

theorem eq_one_of_pow_eq_one_of_isPGroup {T : Type*} [Group T] (hT : IsPGroup p T) {m : ℕ}
    (hm : Nat.Coprime m p) {e : T} (he : e ^ m = 1) : e = 1 := by
  obtain ⟨k, hk⟩ := hT e
  have h1 : orderOf e ∣ m := orderOf_dvd_of_pow_eq_one he
  have h2 : orderOf e ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3 : Nat.Coprime m (p ^ k) := hm.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)

theorem iterate_apply_of_apply_eq {T : Type*} [Group T] (g : T →* T) {e x : T} (he : g e = e)
    (hx : g x = e * x) (k : ℕ) : g^[k] x = e ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, he, hx, pow_succ, mul_assoc]

theorem apply_eq_self_aux [Fact p.Prime] {m : ℕ} (hm : Nat.Coprime m p) :
    ∀ n : ℕ, ∀ (T : Type u) [Group T] [Finite T], Nat.card T = n → IsPGroup p T →
    ∀ g : T →* T, (∀ x : T, g^[m] x = x) → ∀ z : T, g z = z →
    (∀ x : T, x * z = z * x → g x = x) → ∀ x : T, g x = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T _ _ hn hT g hgm z hz h
    by_cases htriv : Subsingleton T
    · intro x
      exact Subsingleton.elim _ _
    rw [not_subsingleton_iff_nontrivial] at htriv
    have hZnt : Nontrivial (Subgroup.center T) := hT.center_nontrivial
    have hZp : IsPGroup p (Subgroup.center T) := hT.to_subgroup _
    have hpZ : p ∣ Nat.card (Subgroup.center T) :=
      (hZp.card_eq_or_dvd).resolve_left (by
        intro h1
        have := Finite.one_lt_card_iff_nontrivial.mpr hZnt
        omega)
    obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' p hpZ
    set c : T := (c' : T) with hcdef
    have hcZ : c ∈ Subgroup.center T := c'.2
    have hcord : orderOf c = p := by rw [hcdef, Subgroup.orderOf_coe]; exact hc'
    have hgc : g c = c := h c (Subgroup.mem_center_iff.mp hcZ z).symm
    set N : Subgroup T := Subgroup.zpowers c with hN
    have hNc : N ≤ Subgroup.center T := (Subgroup.zpowers_le).mpr hcZ
    have hNn : N.Normal := Subgroup.normal_of_le_center hNc
    have hNcard : Nat.card N = p := by rw [hN, Nat.card_zpowers, hcord]
    have hgN : N ≤ N.comap g := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [Subgroup.mem_comap, map_zpow, hgc]
      exact Subgroup.zpow_mem_zpowers c k
    set g' : T ⧸ N →* T ⧸ N := QuotientGroup.map N N g hgN with hg'
    have hg'mk : ∀ x : T, g' (QuotientGroup.mk x) = QuotientGroup.mk (g x) := fun x => rfl
    have hlt : Nat.card (T ⧸ N) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hNcard] at h1
      have h2 : 1 < p := (Fact.out : p.Prime).one_lt
      have h3 : 0 < Nat.card (T ⧸ N) := Nat.card_pos
      rw [← hn, h1]
      nlinarith
    have hiter : ∀ (k : ℕ) (x : T), g'^[k] (QuotientGroup.mk x) = QuotientGroup.mk (g^[k] x) := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ihk =>
        intro x
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hg'mk, ihk]
    have hgm' : ∀ y : T ⧸ N, g'^[m] y = y := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hiter, hgm]
    have hcent : ∀ w : T, QuotientGroup.mk w * QuotientGroup.mk z =
        (QuotientGroup.mk z : T ⧸ N) * QuotientGroup.mk w → g w = w := by
      intro w hw
      have h1 : (w * z)⁻¹ * (z * w) ∈ N := QuotientGroup.eq.mp (by simpa using hw)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
      have hwz : w⁻¹ * z * w = z * c ^ k := by
        have : (w * z)⁻¹ * (z * w) = z⁻¹ * (w⁻¹ * z * w) := by group
        rw [this] at hk
        calc w⁻¹ * z * w = z * (z⁻¹ * (w⁻¹ * z * w)) := by group
          _ = z * c ^ k := by rw [hk]
      have hgwz : (g w)⁻¹ * z * g w = w⁻¹ * z * w := by
        have := congrArg g hwz
        rw [map_mul, map_mul, map_mul, map_inv, hz, map_zpow, hgc] at this
        rw [this, hwz]
      set e : T := g w * w⁻¹ with he
      have hecomm : e * z = z * e := by
        have : e * z * e⁻¹ = z := by
          calc e * z * e⁻¹ = g w * (w⁻¹ * z * w) * (g w)⁻¹ := by rw [he]; group
            _ = g w * ((g w)⁻¹ * z * g w) * (g w)⁻¹ := by rw [hgwz]
            _ = z := by group
        calc e * z = e * z * e⁻¹ * e := by group
          _ = z * e := by rw [this]
      have hge : g e = e := h e hecomm
      have hgw : g w = e * w := by rw [he]; group
      have hiterw := iterate_apply_of_apply_eq g hge hgw m
      rw [hgm w] at hiterw
      have hem : e ^ m = 1 := by
        have : e ^ m * w = w := hiterw.symm
        simpa using this
      have he1 : e = 1 := eq_one_of_pow_eq_one_of_isPGroup hT hm hem
      rw [hgw, he1, one_mul]
    have hh' : ∀ y : T ⧸ N, y * QuotientGroup.mk z = QuotientGroup.mk z * y → g' y = y := by
      intro y hy
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hg'mk, hcent w hy]
    have hall := ih _ hlt (T ⧸ N) rfl (hT.to_quotient N) g' hgm' (QuotientGroup.mk z)
      (by rw [hg'mk, hz]) hh'
    intro x
    have h1 : (g x)⁻¹ * x ∈ N :=
      QuotientGroup.eq.mp (by rw [← hg'mk]; exact hall (QuotientGroup.mk x))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    set e : T := c ^ (-k) with he
    have hge : g e = e := by rw [he, map_zpow, hgc]
    have hgx : g x = e * x := by
      have : g x = x * (x⁻¹ * g x) := by group
      have h2 : x⁻¹ * g x = c ^ (-k) := by
        have : (g x)⁻¹ * x = c ^ k := hk.symm
        calc x⁻¹ * g x = ((g x)⁻¹ * x)⁻¹ := by group
          _ = c ^ (-k) := by rw [this, zpow_neg]
      have hcc : x * c ^ (-k) = c ^ (-k) * x := by
        have : c ^ (-k) ∈ Subgroup.center T := Subgroup.zpow_mem _ hcZ _
        exact (Subgroup.mem_center_iff.mp this x)
      calc g x = x * (x⁻¹ * g x) := by group
        _ = x * c ^ (-k) := by rw [h2]
        _ = e * x := by rw [he, hcc]
    have hiterx := iterate_apply_of_apply_eq g hge hgx m
    rw [hgm x] at hiterx
    have hem : e ^ m = 1 := by
      have : e ^ m * x = x := hiterx.symm
      simpa using this
    have he1 : e = 1 := eq_one_of_pow_eq_one_of_isPGroup hT hm hem
    rw [hgx, he1, one_mul]

theorem apply_eq_self_of_centralizer_le_fixed [Fact p.Prime] {T : Type u} [Group T] [Finite T]
    (hT : IsPGroup p T) (g : T →* T) {m : ℕ} (hm : Nat.Coprime m p)
    (hgm : ∀ x : T, g^[m] x = x) (z : T) (hz : g z = z)
    (h : ∀ x : T, x * z = z * x → g x = x) : ∀ x : T, g x = x :=
  apply_eq_self_aux hm (Nat.card T) T rfl hT g hgm z hz h

end Abstract

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem commute_of_centralizer_le_fixed {T : Subgroup G} (hT : IsPGroup p T) {g z : G}
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hz : z ∈ T) (hgz : g * z = z * g) {m : ℕ}
    (hm : Nat.Coprime m p) (hgm : g ^ m = 1)
    (h : ∀ x ∈ T, x * z = z * x → g * x = x * g) : ∀ x ∈ T, g * x = x * g := by
  let φ : T →* T :=
    { toFun := fun x => ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgT x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [mul_assoc] }
  have hφ : ∀ x : T, (φ x : G) = g * x * g⁻¹ := fun x => rfl
  have hφk : ∀ (k : ℕ) (x : T), ((φ^[k] x : T) : G) = g ^ k * x * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hφ, ih]
      simp only [pow_succ, mul_inv_rev]
      group
  have hφm : ∀ x : T, φ^[m] x = x := by
    intro x
    ext
    rw [hφk, hgm]
    simp
  have hφz : φ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    ext
    rw [hφ]
    show g * z * g⁻¹ = z
    rw [hgz]
    group
  have hφh : ∀ x : T, x * ⟨z, hz⟩ = ⟨z, hz⟩ * x → φ x = x := by
    intro x hx
    have := h x x.2 (congrArg Subtype.val hx)
    ext
    rw [hφ]
    rw [this]
    group
  have key := apply_eq_self_of_centralizer_le_fixed hT φ hm hφm ⟨z, hz⟩ hφz hφh
  intro x hx
  have := congrArg Subtype.val (key ⟨x, hx⟩)
  rw [hφ] at this
  have h2 : g * x * g⁻¹ = x := this
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h2]

end Ambient

section CorollaryB

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isPGroup_zpowers {p j : ℕ} {g : Y} (h : g ^ p ^ j = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨j, Subtype.ext ?_⟩
  show (g ^ k) ^ p ^ j = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

omit [Finite Y] in
theorem isPGroup_two_sup_zpowers {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U) {z : Y}
    (hz : z * z = 1) : IsPGroup 2 ↥(U ⊔ Subgroup.zpowers z) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hzk : z ^ k = 1 ∨ z ^ k = z := by
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    have : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [this, h0]; simp
    · right; rw [this, h1]; simp
  have hsq : (n * z ^ k) * (n * z ^ k) ∈ U := by
    rcases hzk with h1 | h1
    · rw [h1]
      simpa using U.mul_mem hn hn
    · rw [h1]
      have h3 : n * z * (n * z) = n * (z * n * z⁻¹) * (z * z) := by group
      rw [h3, hz, mul_one]
      exact U.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n hn z)
  obtain ⟨k', hk'⟩ := hU ⟨_, hsq⟩
  refine ⟨k' + 1, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hk'
  simp only [OneMemClass.coe_one, SubgroupClass.coe_pow] at this
  show (n * z ^ k) ^ 2 ^ (k' + 1) = 1
  rw [pow_succ, mul_comm, pow_mul, sq]
  exact this

theorem exists_not_commute_of_isSubnormal_centralizer {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1)
    {J : Subgroup Y} (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) {g : Y}
    (hgJ : g ∈ J) {j : ℕ} (hgj : g ^ 3 ^ j = 1) (hg1 : g ≠ 1) :
    ∃ x ∈ J ⊓ U, g * x ≠ x * g := by
  by_contra hcon
  push Not at hcon
  set H : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hHdef
  have hJH : J ≤ H := isSubnormal_le hJ
  have hgH : g ∈ H := hJH hgJ
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgH
  set A : Subgroup Y := U ⊓ H with hAdef
  have hAH : A ≤ H := inf_le_right
  have hAU : A ≤ U := inf_le_left
  have hAn : (A.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAH]
    intro n h hnA hhH
    exact ⟨Subgroup.Normal.conj_mem inferInstance n hnA.1 h, H.mul_mem (H.mul_mem hhH (hAH hnA))
      (H.inv_mem hhH)⟩
  have hA2 : IsPGroup 2 A := hU.to_le hAU
  have hcop : ¬ 3 ∣ Nat.card A := not_three_dvd_card_of_isPGroup_two hA2
  have hP : IsPGroup 3 (Subgroup.zpowers g) := isPGroup_zpowers hgj
  have hPJ : Subgroup.zpowers g ≤ J := (Subgroup.zpowers_le).mpr hgJ
  have h1 : ⁅A, Subgroup.zpowers g⁆ ≤ J :=
    commutator_le_of_isSubnormal Nat.prime_three hJ hAH hAn hcop hPJ hP
  have hgA : g ∈ Subgroup.normalizer (A : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hfwd : ∀ g' ∈ H, ∀ x ∈ A, g' * x * g'⁻¹ ∈ A := fun g' hg' x hx =>
      ⟨Subgroup.Normal.conj_mem inferInstance x hx.1 g',
        H.mul_mem (H.mul_mem hg' hx.2) (H.inv_mem hg')⟩
    exact ⟨fun hx => hfwd g hgH x hx, fun hx => by
      have := hfwd g⁻¹ (H.inv_mem hgH) _ hx
      simpa [mul_assoc] using this⟩
  have hPnorm : Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set Y) := by
    rw [Subgroup.zpowers_le]; exact hgA
  have h2 : ⁅A, Subgroup.zpowers g⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hPnorm
  have hB : ⁅⁅A, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro b hb x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hbJU : b ∈ J ⊓ U := ⟨h1 hb, hAU (h2 hb)⟩
    have hc : g * b = b * g := hcon b hbJU
    have hck : Commute b (g ^ k) := (Commute.zpow_right (show Commute b g from hc.symm) k)
    exact commutatorElement_eq_one_iff_mul_comm.mpr hck.eq
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Subgroup.zpowers g) A hP hcop hPnorm
  rw [hidem] at hB
  have hgA' : ∀ x ∈ A, g * x = x * g := by
    intro x hx
    have : ⁅x, g⁆ ∈ ⁅A, Subgroup.zpowers g⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers g)
    rw [hB, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  set T : Subgroup Y := U ⊔ Subgroup.zpowers z with hT
  have hT2 : IsPGroup 2 T := isPGroup_two_sup_zpowers hU hz
  have hzT : z ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzg : ∀ k : ℤ, g * z ^ k = z ^ k * g := fun k =>
    (Commute.zpow_right (show Commute g z from hgz) k).eq
  have hgT : g ∈ Subgroup.normalizer (T : Set Y) := by
    have hfwd : ∀ g' : Y, (∀ k : ℤ, g' * z ^ k = z ^ k * g') → ∀ y ∈ T, g' * y * g'⁻¹ ∈ T := by
      intro g' hg' y hy
      obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have : g' * (n * z ^ k) * g'⁻¹ = (g' * n * g'⁻¹) * z ^ k := by
        calc g' * (n * z ^ k) * g'⁻¹ = (g' * n * g'⁻¹) * (g' * z ^ k * g'⁻¹) := by group
          _ = (g' * n * g'⁻¹) * z ^ k := by rw [hg' k]; group
      rw [this]
      exact T.mul_mem (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem inferInstance n hn g'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd g hzg y hy, fun hy => ?_⟩
    have hzg' : ∀ k : ℤ, g⁻¹ * z ^ k = z ^ k * g⁻¹ := by
      intro k
      calc g⁻¹ * z ^ k = g⁻¹ * z ^ k * g * g⁻¹ := by group
        _ = g⁻¹ * (z ^ k * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * z ^ k) * g⁻¹ := by rw [hzg k]
        _ = z ^ k * g⁻¹ := by group
    have := hfwd g⁻¹ hzg' _ hy
    simpa [mul_assoc] using this
  have hall := commute_of_centralizer_le_fixed (p := 2) hT2 hgT hzT hgz
    (m := 3 ^ j) (Nat.Coprime.pow_left j (by norm_num)) hgj (by
      intro x hx hxz
      obtain ⟨n, hn, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hnz : n * z = z * n := by
        have h3 : n * z ^ k * z = z * (n * z ^ k) := hxz
        have h4 : z ^ k * z = z * z ^ k := by rw [← zpow_one_add, add_comm, zpow_add_one]
        have : n * z * z ^ k = z * n * z ^ k := by
          calc n * z * z ^ k = n * (z * z ^ k) := by group
            _ = n * (z ^ k * z) := by rw [h4]
            _ = n * z ^ k * z := by group
            _ = z * (n * z ^ k) := h3
            _ = z * n * z ^ k := by group
        exact mul_right_cancel this
      have hnA : n ∈ A := ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr hnz⟩
      calc g * (n * z ^ k) = (g * n) * z ^ k := by group
        _ = (n * g) * z ^ k := by rw [hgA' n hnA]
        _ = n * (g * z ^ k) := by group
        _ = n * (z ^ k * g) := by rw [hzg k]
        _ = (n * z ^ k) * g := by group)
  have hgU : g ∈ Subgroup.centralizer (U : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hall x (Subgroup.mem_sup_left hx)).symm
  have hgU' : g ∈ U := hC hgU
  have h5 : (⟨g, hgU'⟩ : U) ^ 3 ^ j = 1 := Subtype.ext hgj
  exact hg1 (congrArg Subtype.val
    (eq_one_of_pow_eq_one_of_isPGroup hU (Nat.Coprime.pow_left j (by norm_num)) h5))

end CorollaryB

section SL23

private theorem sl23_conj_gen : ∀ x y : SL(2, ZMod 3), x ^ 4 = 1 → x ^ 2 ≠ 1 → y ^ 4 = 1 →
    ∃ w₁ w₂ : SL(2, ZMod 3), y = w₁ * x * w₁⁻¹ ∨ y = (w₁ * x * w₁⁻¹) * (w₂ * x * w₂⁻¹) := by
  decide +kernel

private theorem sl23_pow_twelve : ∀ s : SL(2, ZMod 3), s ^ 12 = 1 := by decide +kernel

private theorem sl23_sq_one : ∀ s : SL(2, ZMod 3), s * s = 1 → s = 1 ∨ s = -1 := by
  decide +kernel

private theorem sl23_neg_central : ∀ s : SL(2, ZMod 3), s * (-1) = (-1) * s := by
  decide +kernel

private theorem sl23_one_ne_neg : (1 : SL(2, ZMod 3)) ≠ -1 := by decide +kernel

private def elemT3 : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem elemT3_pow : elemT3 ^ 3 = 1 := by decide +kernel

private theorem elemT3_ne : elemT3 ≠ 1 := by decide +kernel

private theorem sl23_pow_four_of_two_power {s : SL(2, ZMod 3)} {k : ℕ} (h : s ^ 2 ^ k = 1) :
    s ^ 4 = 1 := by
  have h1 : orderOf s ∣ 12 := orderOf_dvd_of_pow_eq_one (sl23_pow_twelve s)
  have h2 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : a ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ∣ orderOf s := by rw [ha]; exact pow_dvd_pow 2 hlt
    have := this.trans h1
    omega
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact (pow_dvd_pow 2 h3 : 2 ^ a ∣ 2 ^ 2))

variable {Y : Type*} [Group Y] [Finite Y]

private theorem exists_three_element {J : Subgroup Y} (ψ : ↥J →* SL(2, ZMod 3))
    (hψ : Function.Surjective ψ) : ∃ (g : ↥J) (j : ℕ), g ^ 3 ^ j = 1 ∧ ψ g ≠ 1 := by
  obtain ⟨g₀, hg₀⟩ := hψ elemT3
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g₀).ne' 3
    (by norm_num)
  refine ⟨g₀ ^ b, a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hab]
    exact pow_orderOf_eq_one g₀
  · rw [map_pow, hg₀]
    intro h1
    have : 3 ∣ b := by
      have h2 : orderOf elemT3 = 3 := orderOf_eq_prime elemT3_pow elemT3_ne
      rw [← h2]
      exact orderOf_dvd_of_pow_eq_one h1
    exact hb this

theorem exists_mem_inf_of_isSubnormal_centralizer_sl2Three {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1)
    {J : Subgroup Y} (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y)))
    (ψ : ↥J →* SL(2, ZMod 3)) (hψ : Function.Surjective ψ) (hker : Odd (Nat.card ψ.ker)) :
    ∀ y : J, ψ y ^ 4 = 1 → ∃ u : J, (u : Y) ∈ U ∧ ψ u = ψ y := by
  obtain ⟨g', j, hgj', hψg⟩ := exists_three_element ψ hψ
  have hgj : ((g' : ↥J) : Y) ^ 3 ^ j = 1 := congrArg Subtype.val hgj'
  have hg1 : ((g' : ↥J) : Y) ≠ 1 := by
    intro h
    apply hψg
    have : g' = 1 := Subtype.ext h
    rw [this, map_one]
  obtain ⟨x₀, hx₀, hnc⟩ := exists_not_commute_of_isSubnormal_centralizer hU hC hz hJ g'.2 hgj hg1
  have hx₀J : x₀ ∈ J := hx₀.1
  have hx₀U : x₀ ∈ U := hx₀.2
  set ex : SL(2, ZMod 3) := ψ ⟨x₀, hx₀J⟩ with hex
  have hex4 : ex ^ 4 = 1 := by
    obtain ⟨k, hk⟩ := hU ⟨x₀, hx₀U⟩
    have h1 : x₀ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine sl23_pow_four_of_two_power (k := k) ?_
    have : (⟨x₀, hx₀J⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext h1
    rw [hex, ← map_pow, this, map_one]
  have hex2 : ex ^ 2 ≠ 1 := by
    intro h2
    have hcentral : ∀ s : SL(2, ZMod 3), s * ex = ex * s := by
      rcases sl23_sq_one ex (by rwa [← sq]) with h3 | h3
      · intro s; rw [h3]; simp
      · intro s; rw [h3]; exact sl23_neg_central s
    apply hnc
    have hcomm : ⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcentral (ψ g')).symm
    have hcU : ((⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) : Y) ∈ U := by
      have : ((⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) : Y) = x₀ * ((g' : Y) * x₀⁻¹ * (g' : Y)⁻¹) := by
        simp only [commutatorElement_def]
        simp
        group
      rw [this]
      exact U.mul_mem hx₀U (Subgroup.Normal.conj_mem inferInstance _ (U.inv_mem hx₀U) _)
    have hodd : Odd (orderOf (⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J)) :=
      Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard _ hcomm)
    obtain ⟨k, hk⟩ := hU ⟨_, hcU⟩
    have hk' : (⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : (⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) = 1 := by
      have h2' : orderOf (⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have h3' : orderOf (⁅(⟨x₀, hx₀J⟩ : ↥J), g'⁆ : ↥J) = 1 := by
        have := (Nat.coprime_two_right.mpr hodd).pow_right k
        exact Nat.Coprime.eq_one_of_dvd this h2'
      exact orderOf_eq_one_iff.mp h3'
    have h2'' : (⟨x₀, hx₀J⟩ : ↥J) * g' = g' * ⟨x₀, hx₀J⟩ :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    exact (congrArg Subtype.val h2'').symm
  intro y hy4
  obtain ⟨w₁, w₂, hw⟩ := sl23_conj_gen ex (ψ y) hex4 hex2 hy4
  obtain ⟨v₁, hv₁⟩ := hψ w₁
  obtain ⟨v₂, hv₂⟩ := hψ w₂
  have hconj : ∀ v : ↥J, ((v * ⟨x₀, hx₀J⟩ * v⁻¹ : ↥J) : Y) ∈ U := fun v =>
    Subgroup.Normal.conj_mem inferInstance x₀ hx₀U (v : Y)
  have hψconj : ∀ v : ↥J, ψ (v * ⟨x₀, hx₀J⟩ * v⁻¹) = ψ v * ex * (ψ v)⁻¹ := by
    intro v; rw [map_mul, map_mul, map_inv]
  rcases hw with hw | hw
  · refine ⟨v₁ * ⟨x₀, hx₀J⟩ * v₁⁻¹, hconj v₁, ?_⟩
    rw [hψconj, hv₁]
    exact hw.symm
  · refine ⟨(v₁ * ⟨x₀, hx₀J⟩ * v₁⁻¹) * (v₂ * ⟨x₀, hx₀J⟩ * v₂⁻¹), ?_, ?_⟩
    · exact U.mul_mem (hconj v₁) (hconj v₂)
    · rw [map_mul, hψconj, hψconj, hv₁, hv₂]
      exact hw.symm

theorem pow_four_mem_of_isSubnormal_centralizer_sl2Three {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1)
    {J : Subgroup Y} (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y)))
    (e : ↥J ≃* SL(2, ZMod 3)) : ∀ y ∈ J, y ^ 4 = 1 → y ∈ U := by
  intro y hy hy4
  have hker : Odd (Nat.card (e.toMonoidHom.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, Subgroup.card_bot]
    exact odd_one
  obtain ⟨u, huU, hu⟩ := exists_mem_inf_of_isSubnormal_centralizer_sl2Three hU hC hz hJ
    e.toMonoidHom e.surjective hker ⟨y, hy⟩ (by
      rw [← map_pow]
      have : (⟨y, hy⟩ : ↥J) ^ 4 = 1 := Subtype.ext hy4
      rw [this, map_one])
  have h7 : (u : Y) = y := congrArg Subtype.val (e.injective hu)
  rw [← h7]
  exact huU

private theorem eq_one_of_odd_orderOf_of_pow_two {T : Type*} [Group T] {w : T}
    (hw : Odd (orderOf w)) {k : ℕ} (h : w ^ 2 ^ k = 1) : w = 1 := by
  have h2 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    ((Nat.coprime_two_right.mpr hw).pow_right k) h2)

theorem involution_mem_of_isSubnormal_centralizer_sl2Three {U : Subgroup Y} [U.Normal]
    (hU : IsPGroup 2 U) (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1)
    {J : Subgroup Y} (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y))) (hzJ : z ∈ J)
    (ψ : ↥J →* SL(2, ZMod 3)) (hψ : Function.Surjective ψ) (hker : Odd (Nat.card ψ.ker)) :
    z ∈ U := by
  have hz4 : (⟨z, hzJ⟩ : ↥J) ^ 4 = 1 := by
    apply Subtype.ext
    show z ^ 4 = 1
    calc z ^ 4 = (z * z) * (z * z) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hz, mul_one]
  obtain ⟨u, huU, hu⟩ := exists_mem_inf_of_isSubnormal_centralizer_sl2Three hU hC hz hJ ψ hψ hker
    ⟨z, hzJ⟩ (by rw [← map_pow, hz4, map_one])
  set o : ↥J := u⁻¹ * ⟨z, hzJ⟩ with ho
  have hoker : o ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, ho, map_mul, map_inv, hu]
    simp
  have hodd : ∀ w ∈ ψ.ker, Odd (orderOf w) := fun w hw =>
    Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard _ hw)
  have hkerU : ∀ w ∈ ψ.ker, ((w : ↥J) : Y) ∈ U → w = 1 := by
    intro w hw hwU
    obtain ⟨k, hk⟩ := hU ⟨_, hwU⟩
    have : w ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact eq_one_of_odd_orderOf_of_pow_two (hodd w hw) this
  have hcomm : u * o = o * u := by
    have h1 : ⁅u, o⁆ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, show ψ o = 1 from hoker]
      simp
    have h2 : ((⁅u, o⁆ : ↥J) : Y) ∈ U := by
      have : ((⁅u, o⁆ : ↥J) : Y) = (u : Y) * ((o : Y) * (u : Y)⁻¹ * (o : Y)⁻¹) := by
        simp only [commutatorElement_def]
        simp
        group
      rw [this]
      exact U.mul_mem huU (Subgroup.Normal.conj_mem inferInstance _ (U.inv_mem huU) _)
    exact commutatorElement_eq_one_iff_mul_comm.mp (hkerU _ h1 h2)
  have hzuo : (⟨z, hzJ⟩ : ↥J) = u * o := by rw [ho]; group
  have hsq : u * u * (o * o) = 1 := by
    have h1 : (⟨z, hzJ⟩ : ↥J) * ⟨z, hzJ⟩ = 1 := Subtype.ext hz
    rw [hzuo] at h1
    calc u * u * (o * o) = u * (u * o) * o := by group
      _ = u * (o * u) * o := by rw [hcomm]
      _ = (u * o) * (u * o) := by group
      _ = 1 := h1
  have hu2 : u * u = 1 := by
    have h1 : u * u = (o * o)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    have hmem : u * u ∈ ψ.ker := by
      rw [h1]; exact ψ.ker.inv_mem (ψ.ker.mul_mem hoker hoker)
    exact hkerU _ hmem (U.mul_mem huU huU)
  have ho2 : o * o = 1 := by rw [hu2, one_mul] at hsq; exact hsq
  have ho1 : o = 1 :=
    eq_one_of_odd_orderOf_of_pow_two (hodd o hoker) (k := 1) (by simpa [sq] using ho2)
  have hzu : (⟨z, hzJ⟩ : ↥J) = u := by rw [hzuo, ho1, mul_one]
  have h7 : z = (u : Y) := congrArg Subtype.val hzu
  rw [h7]
  exact huU

end SL23

end CFSG.ClassicalInvolution.Q3
