module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup AltStdSec

section Abstract

variable {H : Type*} [Group H] [Finite H]

theorem exists_conj_of_mk_conj_oddCore {t s : H} (ht : t * t = 1) (hs : s * s = 1)
    {k : H ⧸ CFSG.oddCore H}
    (hk : k * (t : H ⧸ CFSG.oddCore H) * k⁻¹ = (s : H ⧸ CFSG.oddCore H)) :
    ∃ w : H, w * t * w⁻¹ = s := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
  have hu : (k * t * k⁻¹) * (k * t * k⁻¹) = 1 := by
    calc (k * t * k⁻¹) * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hmem : s * (k * t * k⁻¹) ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk, ← QuotientGroup.mk_mul, hs]
    rfl
  obtain ⟨r, -, hr⟩ := exists_conj_of_involutions_of_mul_mem
    (fun y hy => orderOf_odd_of_mem_oddCore hy) hu hs hmem
  exact ⟨r * k, by rw [← hr]; group⟩

theorem exists_mul_comm_of_mk_mem_center {t : H} (ht : t * t = 1)
    (hc : (t : H ⧸ CFSG.oddCore H) ∈ Subgroup.center (H ⧸ CFSG.oddCore H)) (c : H) :
    ∃ r ∈ CFSG.oddCore H, r * c * t = t * (r * c) := by
  have hu : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hmem : t * (c * t * c⁻¹) ∈ CFSG.oddCore H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 := Subgroup.mem_center_iff.1 hc (c : H ⧸ CFSG.oddCore H)
    have h2 : (t : H ⧸ CFSG.oddCore H) * t = 1 := by rw [← QuotientGroup.mk_mul, ht]; rfl
    calc (t : H ⧸ CFSG.oddCore H) * ((c : H ⧸ CFSG.oddCore H) * t * (c : H ⧸ CFSG.oddCore H)⁻¹)
        = (t : H ⧸ CFSG.oddCore H) * ((c : H ⧸ CFSG.oddCore H) * t) *
            (c : H ⧸ CFSG.oddCore H)⁻¹ := by group
      _ = (t : H ⧸ CFSG.oddCore H) * (t * (c : H ⧸ CFSG.oddCore H)) *
            (c : H ⧸ CFSG.oddCore H)⁻¹ := by rw [h1]
      _ = ((t : H ⧸ CFSG.oddCore H) * t) * ((c : H ⧸ CFSG.oddCore H) *
            (c : H ⧸ CFSG.oddCore H)⁻¹) := by group
      _ = 1 := by rw [h2, mul_inv_cancel, one_mul]
  obtain ⟨r, hr, hrt⟩ := exists_conj_of_involutions_of_mul_mem
    (fun y hy => orderOf_odd_of_mem_oddCore hy) hu ht hmem
  refine ⟨r, hr, ?_⟩
  calc r * c * t = (r * (c * t * c⁻¹) * r⁻¹) * (r * c) := by group
    _ = t * (r * c) := by rw [hrt]

theorem exists_mul_of_mk_mem_oddCore (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ Subgroup.center H)
    (hZ2 : IsPGroup 2 Z) {k : H} (hk : (k : H ⧸ Z) ∈ CFSG.oddCore (H ⧸ Z)) :
    ∃ ζ ∈ Z, ∃ o ∈ CFSG.oddCore H, k = ζ * o := by
  set O := CFSG.oddCore (H ⧸ Z) with hOdef
  set N : Subgroup H := O.comap (QuotientGroup.mk' Z) with hNdef
  have hON : O.Normal := inferInstance
  have hNn : N.Normal := hON.comap _
  have hZN : Z ≤ N := by
    intro z hz
    change (QuotientGroup.mk' Z z) ∈ O
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact O.one_mem
  have hOodd : Odd (Nat.card O) := CFSG.Semidihedral.Local.odd_card_oddCore (H ⧸ Z)
  set Z' : Subgroup N := Z.subgroupOf N with hZ'def
  let ρ : N →* O := (QuotientGroup.mk' Z).subgroupComap O
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk' Z).subgroupComap_surjective O (QuotientGroup.mk'_surjective Z)
  have hρker : ρ.ker = Z' := by
    ext n
    rw [MonoidHom.mem_ker, hZ'def, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ((QuotientGroup.mk' Z) (n : H) : H ⧸ Z) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hidx : Z'.index = Nat.card O := by
    rw [Subgroup.index_eq_card, ← hρker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
  have hZ'2 : IsPGroup 2 Z' := by
    have e : Z' ≃* Z := Subgroup.subgroupOfEquivOfLe hZN
    exact hZ2.of_equiv e.symm
  have hcop : Nat.Coprime (Nat.card Z') Z'.index := by
    obtain ⟨j, hj⟩ := hZ'2.exists_card_eq
    rw [hj, hidx]
    exact Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hOodd)
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hQodd : Odd (Nat.card Q) := by
    rw [← hQ.symm.index_eq_card, hidx]
    exact hOodd
  have hcen : ∀ a : N, a ∈ Z' → ∀ b : N, a * b = b * a := by
    intro a ha b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ ha) (b : H)).symm
  have hoddQ : ∀ n : N, Odd (orderOf n) → n ∈ Q := by
    intro n hn
    have hmem : n ∈ ((Z' ⊔ Q : Subgroup N) : Set N) := by
      rw [hQ.sup_eq_top]
      exact Subgroup.mem_top n
    rw [Subgroup.normal_mul] at hmem
    obtain ⟨z, hz, q, hq, rfl⟩ := hmem
    dsimp only at hn ⊢
    have hzq : Commute z q := hcen z hz q
    have hpow : z ^ orderOf (z * q) * q ^ orderOf (z * q) = 1 := by
      rw [← hzq.mul_pow, pow_orderOf_eq_one]
    have hzm : z ^ orderOf (z * q) ∈ Z' ⊓ Q := by
      refine ⟨Z'.pow_mem hz _, ?_⟩
      have : z ^ orderOf (z * q) = (q ^ orderOf (z * q))⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact Q.inv_mem (Q.pow_mem hq _)
    rw [hQ.disjoint.eq_bot, Subgroup.mem_bot] at hzm
    have hz2 : ∃ j : ℕ, orderOf z = 2 ^ j := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hZ'2) ⟨z, hz⟩
      exact ⟨j, (Subgroup.orderOf_coe (⟨z, hz⟩ : Z')).trans hj⟩
    have hz1 : z = 1 := by
      have h := QuasiDihedralFusion.mem_zpowers_pow_of_odd hz2 hn
      rw [hzm, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
      exact h
    rw [hz1, one_mul]
    exact hq
  set Q' : Subgroup H := Q.map N.subtype with hQ'def
  have hQ'odd : Odd (Nat.card Q') := by
    rw [hQ'def, Subgroup.card_map_of_injective N.subtype_injective]
    exact hQodd
  have hQ'n : Q'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hx
    have hgN : g * (q : H) * g⁻¹ ∈ N := hNn.conj_mem _ q.property g
    let n : N := ⟨g * (q : H) * g⁻¹, hgN⟩
    have hnodd : Odd (orderOf n) := by
      have h1 : orderOf n = orderOf (g * (q : H) * g⁻¹) := Subgroup.orderOf_mk _ _
      have h2 : orderOf (g * (q : H) * g⁻¹) = orderOf (q : H) := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      have h3 : orderOf (q : H) = orderOf (⟨q, hq⟩ : Q) :=
        (Subgroup.orderOf_coe q).trans (Subgroup.orderOf_coe (⟨q, hq⟩ : Q))
      rw [h1, h2, h3]
      exact Odd.of_dvd_nat hQodd (orderOf_dvd_natCard _)
    exact ⟨n, hoddQ n hnodd, rfl⟩
  have hQ'le : Q' ≤ CFSG.oddCore H := CFSG.Semidihedral.Local.le_oddCore hQ'n hQ'odd
  have hkN : k ∈ N := hk
  have hmem : (⟨k, hkN⟩ : N) ∈ ((Z' ⊔ Q : Subgroup N) : Set N) := by
    rw [hQ.sup_eq_top]
    exact Subgroup.mem_top _
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨ζ, hζ, q, hq, hζq⟩ := hmem
  refine ⟨(ζ : H), hζ, (q : H), hQ'le ⟨q, hq, rfl⟩, ?_⟩
  have h1 := congrArg Subtype.val hζq
  rw [Subgroup.coe_mul] at h1
  exact h1.symm

end Abstract

section TwoSec

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_selfC {x : G} (hx2 : x * x = 1) : IsPGroup 2 (zpowers (selfC x)) := by
  have hs : selfC x * selfC x = 1 := Subtype.ext hx2
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 g.2
  rw [Subgroup.coe_pow, ← hj, OneMemClass.coe_one, pow_one, pow_two,
    ← (Commute.refl (selfC x)).mul_zpow, hs, one_zpow]

theorem exists_oddCoreOf_of_mk_mem_oddCore {x : G} (hx2 : x * x = 1)
    {r : ↥(centralizer ({x} : Set G))}
    (hr : (QuotientGroup.mk r : TwoSec x) ∈ CFSG.oddCore (TwoSec x)) :
    ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)), (r : G) = o ∨ (r : G) = x * o := by
  obtain ⟨ζ, hζ, o, ho, hro⟩ := exists_mul_of_mk_mem_oddCore (zpowers (selfC x))
    (zpowers_le.2 (selfC_mem_center x)) (isPGroup_zpowers_selfC hx2) hr
  refine ⟨(o : G), ⟨o, ho, rfl⟩, ?_⟩
  have h1 : (r : G) = (ζ : G) * o := by rw [hro, Subgroup.coe_mul]
  rcases (mem_zpowers_selfC_iff hx2).1 hζ with h2 | h2
  · left
    rw [h1, h2, one_mul]
  · right
    rw [h1, h2]

theorem exists_oddCoreOf_mul_mem_centralizer {x z : G} (hx2 : x * x = 1) (hz2 : z * z = 1)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G))
    (hcen : (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) :
        TwoSec x ⧸ CFSG.oddCore (TwoSec x)) ∈ Subgroup.center (TwoSec x ⧸ CFSG.oddCore (TwoSec x)))
    {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    ∃ o ∈ oddCoreOf (centralizer ({x} : Set G)), o * c ∈ centralizer ({z} : Set G) := by
  have ht : (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) * QuotientGroup.mk ⟨z, hzx⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]
    rfl
  obtain ⟨rb, hrb, hrc⟩ := exists_mul_comm_of_mk_mem_center ht hcen
    (QuotientGroup.mk ⟨c, hc⟩ : TwoSec x)
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective rb
  have hrcz : (r : G) * c * z = z * ((r : G) * c) := by
    have hmem : (r : G) * c ∈ centralizer ({x} : Set G) := mul_mem r.2 hc
    have h1 : (QuotientGroup.mk ⟨(r : G) * c, hmem⟩ : TwoSec x) =
        (QuotientGroup.mk r : TwoSec x) * QuotientGroup.mk ⟨c, hc⟩ := by
      rw [← QuotientGroup.mk_mul]
      rfl
    have h2 := comm_of_mk_comm hx2 hfus hzx hmem (by rw [h1]; exact hrc)
    exact h2
  obtain ⟨o, ho, hro | hro⟩ := exists_oddCoreOf_of_mk_mem_oddCore hx2 hrb
  · refine ⟨o, ho, ?_⟩
    rw [mem_centralizer_singleton_iff, ← hro]
    exact hrcz
  · refine ⟨o, ho, ?_⟩
    have hxz : x * z = z * x := (mem_centralizer_singleton_iff.1 hzx).symm
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hoc : o * c = x * ((r : G) * c) := by
      rw [hro, ← mul_assoc, ← mul_assoc, hx2, one_mul]
    rw [mem_centralizer_singleton_iff, hoc]
    calc x * ((r : G) * c) * z = x * ((r : G) * c * z) := by group
      _ = x * (z * ((r : G) * c)) := by rw [hrcz]
      _ = (x * z) * ((r : G) * c) := by group
      _ = (z * x) * ((r : G) * c) := by rw [hxz]
      _ = z * (x * ((r : G) * c)) := by group

end TwoSec

end CFSG.OddStandard.AltStdCycTwo.Two
