module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoLift
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem odd_card_O (H : Subgroup G) : Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := by
  have h1 : Nat.card ↥(pPrimeCoreOf 2 H) = Nat.card ↥(pPrimeCore 2 ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [h1]
  exact odd_card_pPrimeCore

theorem inf_O_eq_bot {H T : Subgroup G} (hT : IsPGroup 2 ↥T) : T ⊓ pPrimeCoreOf 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(T ⊓ pPrimeCoreOf 2 H) := hT.to_inf_left
  have hdvd : Nat.card ↥(T ⊓ pPrimeCoreOf 2 H) ∣ Nat.card ↥(pPrimeCoreOf 2 H) :=
    Subgroup.card_dvd_of_le inf_le_right
  rcases h2.card_eq_or_dvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exact absurd (h.trans hdvd) (Nat.not_even_iff_odd.2 (odd_card_O H) ∘ even_iff_two_dvd.2)

omit [Finite G] in
theorem mk_mem_barIn {H X : Subgroup G} {x : ↥H} (hx : (x : G) ∈ X) :
    QuotientGroup.mk' (pPrimeCore 2 ↥H) x ∈ barIn H X :=
  ⟨x, hx, rfl⟩

omit [Finite G] in
theorem barIn_mono {H X Y : Subgroup G} (h : X ≤ Y) : barIn H X ≤ barIn H Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem eq_of_mk_eq {H T : Subgroup G} (hT : IsPGroup 2 ↥T) {x y : ↥H} (hx : (x : G) ∈ T)
    (hy : (y : G) ∈ T)
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥H) x = QuotientGroup.mk' (pPrimeCore 2 ↥H) y) :
    x = y := by
  have hk : x⁻¹ * y ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥H), MonoidHom.mem_ker, map_mul, map_inv, h]
    exact inv_mul_cancel _
  have hO : ((x⁻¹ * y : ↥H) : G) ∈ pPrimeCoreOf 2 H := ⟨_, hk, rfl⟩
  have hT' : ((x⁻¹ * y : ↥H) : G) ∈ T := by
    have : ((x⁻¹ * y : ↥H) : G) = (x : G)⁻¹ * (y : G) := rfl
    rw [this]
    exact T.mul_mem (T.inv_mem hx) hy
  have hmem : ((x⁻¹ * y : ↥H) : G) ∈ T ⊓ pPrimeCoreOf 2 H := ⟨hT', hO⟩
  rw [inf_O_eq_bot hT, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 (Subtype.ext hmem)

theorem card_barIn {H T : Subgroup G} (hT : IsPGroup 2 ↥T) (hTH : T ≤ H) :
    Nat.card ↥(barIn H T) = Nat.card ↥T := by
  let f : ↥(T.subgroupOf H) →* HBar H :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)).domRestrict (T.subgroupOf H)
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (eq_of_mk_eq hT a.2 b.2 hab)
  have hrange : f.range = barIn H T := MonoidHom.domRestrict_range _ _
  rw [← hrange]
  exact ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv)

theorem comm_of_barIn_le {H T X : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 ↥T)
    (hTX : barIn H T ≤ barIn H X) (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, hi, hia⟩ := hTX (mk_mem_barIn (H := H) (x := ⟨a, hTH ha⟩) ha)
  obtain ⟨j, hj, hjb⟩ := hTX (mk_mem_barIn (H := H) (x := ⟨b, hTH hb⟩) hb)
  have h : QuotientGroup.mk' (pPrimeCore 2 ↥H) (⟨a, hTH ha⟩ * ⟨b, hTH hb⟩ : ↥H) =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) (⟨b, hTH hb⟩ * ⟨a, hTH ha⟩ : ↥H) := by
    rw [map_mul, map_mul, ← hia, ← hjb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hXc _ hi _ hj)
  exact congrArg Subtype.val (eq_of_mk_eq hT2 (T.mul_mem ha hb) (T.mul_mem hb ha) h)

theorem sq_of_barIn_le {H T X : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 ↥T)
    (hTX : barIn H T ≤ barIn H X) (hXs : ∀ a ∈ X, a * a = 1) : ∀ a ∈ T, a * a = 1 := by
  intro a ha
  obtain ⟨i, hi, hia⟩ := hTX (mk_mem_barIn (H := H) (x := ⟨a, hTH ha⟩) ha)
  have hii : i * i = 1 := Subtype.ext (hXs _ hi)
  have h : QuotientGroup.mk' (pPrimeCore 2 ↥H) (⟨a, hTH ha⟩ * ⟨a, hTH ha⟩ : ↥H) =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) (1 : ↥H) := by
    rw [map_mul, ← hia, ← map_mul, hii]
  exact congrArg Subtype.val (eq_of_mk_eq hT2 (T.mul_mem ha ha) T.one_mem h)

omit [Finite G] in
theorem commutator_mem_O_of_mk_comm {H : Subgroup G} {x y : ↥H}
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥H) x * QuotientGroup.mk' (pPrimeCore 2 ↥H) y =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) y * QuotientGroup.mk' (pPrimeCore 2 ↥H) x) :
    ⁅(x : G), (y : G)⁆ ∈ pPrimeCoreOf 2 H := by
  have hk : ⁅x, y⁆ ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥H), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h
  exact ⟨_, hk, rfl⟩

omit [Finite G] in
theorem barIn_comm {H X : Subgroup G} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    ∀ x ∈ barIn H X, ∀ y ∈ barIn H X, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hXc _ ha _ hb)

omit [Finite G] in
theorem isElementaryAbelian_two_of {T : Subgroup G} (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hs : ∀ a ∈ T, a * a = 1) : IsElementaryAbelian 2 ↥T :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a =>
      Subtype.ext (by simpa [pow_two] using hs a a.2) }

omit [Finite G] in
theorem comm_of_isElementaryAbelian {T : Subgroup G} [IsElementaryAbelian 2 ↥T] :
    ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
  intro a ha b hb
  have := (IsMulCommutative.is_comm (M := ↥T)).comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

omit [Finite G] in
theorem sq_of_isElementaryAbelian {T : Subgroup G} [IsElementaryAbelian 2 ↥T] :
    ∀ a ∈ T, a * a = 1 := by
  intro a ha
  have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := T) a ha
  simpa [pow_two] using this

omit [Finite G] in
theorem card_sup_eq_mul_of_commute {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  let f : A × B →* G := (A.subtype).noncommCoprod B.subtype (fun p q => hcomm _ p.2 _ q.2)
  have happ : ∀ (p : A) (q : B), f (p, q) = (p : G) * q := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    rw [MonoidHom.mem_ker, happ] at hpq
    have hmem : (p : G) ∈ A ⊓ B := by
      refine ⟨p.2, ?_⟩
      have : (p : G) = ((q : G))⁻¹ := eq_inv_of_mul_eq_one_left hpq
      rw [this]
      exact B.inv_mem q.2
    rw [hinf, mem_bot] at hmem
    have hp : p = 1 := Subtype.ext hmem
    rw [hmem, one_mul] at hpq
    have hq : q = 1 := Subtype.ext hpq
    rw [hp, hq]
    exact one_mem _
  have hrange : f.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨⟨p, q⟩, rfl⟩
      rw [happ]
      exact mul_mem (mem_sup_left p.2) (mem_sup_right q.2)
    · refine sup_le ?_ ?_
      · intro p hp
        exact ⟨(⟨p, hp⟩, 1), by rw [happ]; simp⟩
      · intro q hq
        exact ⟨(1, ⟨q, hq⟩), by rw [happ]; simp⟩
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_E8 (hrank : NoE32 G) {H U I₁ E : Subgroup G} (hI : GoodI1 H U I₁)
    (hEH : E ≤ H) (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEsq : ∀ a ∈ E, a * a = 1)
    (hEcard : Nat.card ↥E = 8)
    (hEI : barIn H E ≤ centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H))) :
    False := by
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  obtain ⟨Q₁, hQ₁I, hQ₁el, hQ₁card⟩ := hI.four
  have hQ₁H : Q₁ ≤ H := hQ₁I.trans hI.le_H
  have := hQ₁el
  have hQ₁2 : IsPGroup 2 ↥Q₁ := IsElementaryAbelian.isPGroup 2 ↥Q₁
  have hQ₁comm : ∀ a ∈ Q₁, ∀ b ∈ Q₁, a * b = b * a := comm_of_isElementaryAbelian
  have hQ₁sq : ∀ a ∈ Q₁, a * a = 1 := sq_of_isElementaryAbelian
  have hB2 : IsPGroup 2 ↥(barIn H Q₁) := (hQ₁2.comap_subtype (K := H)).map _
  have hBI : barIn H Q₁ ≤ barIn H I₁ := barIn_mono hQ₁I
  have hQC : barIn H Q₁ ≤ centralizer ((barIn H E : Subgroup (HBar H)) : Set (HBar H)) :=
    fun b hb => Subgroup.mem_centralizer_iff.2 fun x hx =>
      (Subgroup.mem_centralizer_iff.1 (hEI hx) b (hBI hb)).symm
  have hbot : barIn H (⊥ : Subgroup G) ≤ barIn H Q₁ := by
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : y = 1 := Subtype.ext hy
    rw [hy1, map_one]
    exact (barIn H Q₁).one_mem
  obtain ⟨Q', hQ'H, hQ'C, hQ'2, -, hQ'B⟩ := exists_lift_centralizer_gen (A := ⊥) hEH hE2 bot_le
    (IsPGroup.of_card (n := 0) (by simp)) bot_le hB2 hQC hbot
  have hQ'B' : barIn H Q' ≤ barIn H Q₁ := hQ'B.le
  have hQ'comm : ∀ a ∈ Q', ∀ b ∈ Q', a * b = b * a := comm_of_barIn_le hQ'H hQ'2 hQ'B' hQ₁comm
  have hQ'sq : ∀ a ∈ Q', a * a = 1 := sq_of_barIn_le hQ'H hQ'2 hQ'B' hQ₁sq
  have hQ'card : Nat.card ↥Q' = 4 := by
    rw [← card_barIn hQ'2 hQ'H, hQ'B, card_barIn hQ₁2 hQ₁H]
    exact hQ₁card
  have hinf : E ⊓ Q' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxE, hxQ⟩
    have hxH : x ∈ H := hEH hxE
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hxH⟩ ∈ barIn H Q' := mk_mem_barIn hxQ
    rw [hQ'B] at hmem
    obtain ⟨i, hiQ, hix⟩ := hmem
    have hcentral : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hxH⟩ ∈
        centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) := hEI (mk_mem_barIn hxE)
    have hcomm : ∀ j ∈ I₁, ⁅(i : G), j⁆ ∈ pPrimeCoreOf 2 H := by
      intro j hj
      have hjH : j ∈ H := hI.le_H hj
      have h1 := Subgroup.mem_centralizer_iff.1 hcentral
        (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨j, hjH⟩) (mk_mem_barIn (H := H) (x := ⟨j, hjH⟩) hj)
      rw [← hix] at h1
      exact commutator_mem_O_of_mk_comm (x := i) (y := ⟨j, hjH⟩) h1.symm
    have hi1 : (i : G) = 1 := by
      have hdvd : orderOf (i : G) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hQ₁sq _ hiQ)
      have hodd := hI.noCent (i : G) (hQ₁I hiQ) hcomm
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have hi1' : i = 1 := Subtype.ext hi1
    have hmk : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hxH⟩ =
        QuotientGroup.mk' (pPrimeCore 2 ↥H) (1 : ↥H) := by
      rw [← hix, hi1']
    exact congrArg Subtype.val (eq_of_mk_eq hQ'2 (x := ⟨x, hxH⟩) (y := 1) hxQ Q'.one_mem hmk)
  have hEel : IsElementaryAbelian 2 ↥E := isElementaryAbelian_two_of hEcomm hEsq
  have hQel : IsElementaryAbelian 2 ↥Q' := isElementaryAbelian_two_of hQ'comm hQ'sq
  have hFel : IsElementaryAbelian 2 ↥(E ⊔ Q') := IsElementaryAbelian.sup_of_le_centralizer hQ'C
  have hF := hrank (E ⊔ Q') comm_of_isElementaryAbelian sq_of_isElementaryAbelian
  have hcard : Nat.card ↥(E ⊔ Q') = 32 := by
    rw [card_sup_eq_mul_of_commute ?_ hinf, hEcard, hQ'card]
    intro e he q hq
    exact Subgroup.mem_centralizer_iff.1 (hQ'C hq) e he
  omega

theorem centralizer_W_le (hrank : NoE32 G) {H U I₁ : Subgroup G} (hU2 : IsPGroup 2 ↥U)
    (hU4 : IVK.IsFourSubgroup U) (hUH : U ≤ H)
    (hstr : ∀ Q : Subgroup G, Q ≤ centralizer (U : Set G) → IsPGroup 2 ↥Q → U ≤ Q → Q ≠ U →
      ∃ d ∈ Q, orderOf d = 2 ∧ d ∉ U)
    (hI : GoodI1 H U I₁) {W : Subgroup (HBar H)} (hW2 : IsPGroup 2 ↥W)
    (hWI : W ≤ centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)))
    (hUW : barIn H U ≤ W) :
    W ⊓ centralizer ((barIn H U : Subgroup (HBar H)) : Set (HBar H)) ≤ barIn H U := by
  obtain ⟨hUel, hUcard⟩ := hU4
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := comm_of_isElementaryAbelian
  have hQb2 : IsPGroup 2 ↥(W ⊓ centralizer ((barIn H U : Subgroup (HBar H)) : Set (HBar H))) :=
    hW2.to_le inf_le_left
  have hUQb : barIn H U ≤ W ⊓ centralizer ((barIn H U : Subgroup (HBar H)) : Set (HBar H)) :=
    le_inf hUW fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      barIn_comm hUcomm y hy x hx
  obtain ⟨Q, hQH, hQC, hQ2, hUQ, hQbar⟩ :=
    exists_lift_centralizer hUH hU2 hUcomm hQb2 inf_le_right hUQb
  by_contra hnot
  have hQU : Q ≠ U := by
    intro h
    exact hnot (by rw [← hQbar, h])
  obtain ⟨d, hdQ, hd2, hdU⟩ := hstr Q hQC hQ2 hUQ hQU
  have hdsq : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rwa [hd2, pow_two] at this
  have hdC : d ∈ centralizer (U : Set G) := hQC hdQ
  have hzC : zpowers d ≤ centralizer (U : Set G) := Subgroup.zpowers_le.2 hdC
  have hEQ : U ⊔ zpowers d ≤ Q := sup_le hUQ (Subgroup.zpowers_le.2 hdQ)
  have hEH : U ⊔ zpowers d ≤ H := hEQ.trans hQH
  have hEI : barIn H (U ⊔ zpowers d) ≤
      centralizer ((barIn H I₁ : Subgroup (HBar H)) : Set (HBar H)) :=
    (barIn_mono hEQ).trans (hQbar.le.trans (inf_le_left.trans hWI))
  have hdel : IsElementaryAbelian 2 ↥(zpowers d) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [pow_two]; exact hdsq)
  have hEel : IsElementaryAbelian 2 ↥(U ⊔ zpowers d) :=
    IsElementaryAbelian.sup_of_le_centralizer hzC
  have hEcard : Nat.card ↥(U ⊔ zpowers d) = 8 := by
    have hcomm : ∀ g ∈ U, ∀ g' ∈ zpowers d, g * g' = g' * g := fun g hg g' hg' =>
      Subgroup.mem_centralizer_iff.1 (hzC hg') g hg
    have hinf : U ⊓ zpowers d = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨hxU, hxd⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxd
      rw [← zpow_mod_orderOf, hd2] at hxU ⊢
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [Nat.cast_ofNat, h, zpow_zero]
      · rw [Nat.cast_ofNat, h, zpow_one] at hxU
        exact absurd hxU hdU
    rw [card_sup_eq_mul_of_commute hcomm hinf, hUcard, Nat.card_zpowers, hd2]
  exact false_of_E8 hrank hI hEH comm_of_isElementaryAbelian sq_of_isElementaryAbelian hEcard hEI

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
