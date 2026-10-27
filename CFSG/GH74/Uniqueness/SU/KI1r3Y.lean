module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG
open scoped Pointwise

namespace LemmaYAux

section Abstract

variable {V : Type*} [Group V] [Finite V]

theorem fpf_prod {ψ : V →* V} (hψ : MonoidHom.FixedPointFree ψ)
    (h3 : ∀ v, ψ (ψ (ψ v)) = v) (g : V) : g * ψ g * ψ (ψ g) = 1 := by
  have hit : (⇑ψ)^[3] = _root_.id := funext fun v => h3 v
  have := hψ.prod_pow_eq_one hit g
  simpa [List.range_succ, mul_assoc] using this

theorem fpf_commute {ψ : V →* V} (hψ : MonoidHom.FixedPointFree ψ)
    (h3 : ∀ v, ψ (ψ (ψ v)) = v) (x : V) : x * ψ x = ψ x * x := by
  have h1 := fpf_prod hψ h3 x
  have h2 := fpf_prod hψ h3 (x * ψ x)
  simp only [map_mul, h3] at h2
  have hz : ψ (ψ x) = (x * ψ x)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [hz] at h2
  have key : x * ψ x * x⁻¹ * (ψ x)⁻¹ = 1 := by
    calc x * ψ x * x⁻¹ * (ψ x)⁻¹
        = x * ψ x * (ψ x * (x * ψ x)⁻¹) * ((x * ψ x)⁻¹ * x) := by group
      _ = 1 := h2
  calc x * ψ x = x * ψ x * x⁻¹ * (ψ x)⁻¹ * (ψ x * x) := by group
    _ = ψ x * x := by rw [key, one_mul]

end Abstract

section Conj

variable {G : Type*} [Group G]

structure FpfConj (R : Subgroup G) (y : G) : Prop where
  mem : ∀ r ∈ R, y * r * y⁻¹ ∈ R
  cube : ∀ r ∈ R, y ^ 3 * r * (y ^ 3)⁻¹ = r
  free : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1

variable {R : Subgroup G} {y : G}

theorem FpfConj.cube3 (h : FpfConj R y) {r : G} (hr : r ∈ R) :
    y * y * y * r = r * (y * y * y) := by
  have := h.cube r hr
  rwa [pow_three', mul_inv_eq_iff_eq_mul] at this

theorem FpfConj.cube' (h : FpfConj R y) {r : G} (hr : r ∈ R) :
    y * (y * (y * r * y⁻¹) * y⁻¹) * y⁻¹ = r := by
  have hc := h.cube3 hr
  calc y * (y * (y * r * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y * r) * (y * y * y)⁻¹ := by group
    _ = r := by rw [hc, mul_inv_cancel_right]

theorem FpfConj.inv_eq (h : FpfConj R y) {r : G} (hr : r ∈ R) :
    y⁻¹ * r * y = y * (y * r * y⁻¹) * y⁻¹ := by
  have hc := h.cube3 hr
  calc y⁻¹ * r * y = y⁻¹ * (r * (y * y * y)) * (y * y * y)⁻¹ * y := by group
    _ = y⁻¹ * (y * y * y * r) * (y * y * y)⁻¹ * y := by rw [hc]
    _ = y * (y * r * y⁻¹) * y⁻¹ := by group

theorem FpfConj.inv_mem (h : FpfConj R y) {r : G} (hr : r ∈ R) : y⁻¹ * r * y ∈ R := by
  rw [h.inv_eq hr]
  exact h.mem _ (h.mem _ hr)

def FpfConj.hom (h : FpfConj R y) : ↥R →* ↥R where
  toFun r := ⟨y * r * y⁻¹, h.mem r r.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show y * ((a : G) * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹)
    group)

variable [Finite G]

theorem FpfConj.prod_eq_one (h : FpfConj R y) {r : G} (hr : r ∈ R) :
    r * (y * r * y⁻¹) * (y * (y * r * y⁻¹) * y⁻¹) = 1 := by
  have hfix : MonoidHom.FixedPointFree h.hom := fun g hg =>
    Subtype.ext (h.free g g.2 (congrArg Subtype.val hg))
  have h3 : ∀ v : ↥R, h.hom (h.hom (h.hom v)) = v := fun v => Subtype.ext (h.cube' v.2)
  exact congrArg Subtype.val (fpf_prod hfix h3 ⟨r, hr⟩)

theorem FpfConj.commute (h : FpfConj R y) {r : G} (hr : r ∈ R) :
    r * (y * r * y⁻¹) = (y * r * y⁻¹) * r := by
  have hfix : MonoidHom.FixedPointFree h.hom := fun g hg =>
    Subtype.ext (h.free g g.2 (congrArg Subtype.val hg))
  have h3 : ∀ v : ↥R, h.hom (h.hom (h.hom v)) = v := fun v => Subtype.ext (h.cube' v.2)
  exact congrArg Subtype.val (fpf_commute hfix h3 ⟨r, hr⟩)

end Conj

section Pair

variable {G : Type*} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {x c : G} (hx : x * x = 1) (hc : c ∈ zpowers x) :
    c = 1 ∨ c = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hx, one_zpow, one_mul]

def pairSub (y e : G) : Subgroup G := zpowers e ⊔ zpowers (y * e * y⁻¹)

variable {R : Subgroup G} {y : G}

theorem FpfConj.pair (h : FpfConj R y) [Finite G] {e : G} (heR : e ∈ R) (he2 : e * e = 1)
    (he1 : e ≠ 1) :
    pairSub y e ≤ R ∧ Open.IsElemAbelian 2 (pairSub y e) ∧ Nat.card (pairSub y e) = 4 ∧
      (∀ w ∈ pairSub y e, y * w * y⁻¹ ∈ pairSub y e) ∧ e ∈ pairSub y e := by
  have he'R : y * e * y⁻¹ ∈ R := h.mem e heR
  have he'2 : (y * e * y⁻¹) * (y * e * y⁻¹) = 1 := by
    calc (y * e * y⁻¹) * (y * e * y⁻¹) = y * (e * e) * y⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have he'1 : y * e * y⁻¹ ≠ 1 := by
    intro hh
    apply he1
    calc e = y⁻¹ * (y * e * y⁻¹) * y := by group
      _ = 1 := by rw [hh]; group
  have he'ne : y * e * y⁻¹ ≠ e := fun hh => he1 (h.free e heR hh)
  have he'nz : y * e * y⁻¹ ∉ zpowers e := fun hm =>
    (eq_one_or_eq_of_mem_zpowers he2 hm).elim he'1 he'ne
  have hcomm : e * (y * e * y⁻¹) = (y * e * y⁻¹) * e := h.commute heR
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
    (by rw [pow_two]; exact he2) (by rw [pow_two]; exact he'2) he1 he'nz hcomm
  have hee : y * (y * e * y⁻¹) * y⁻¹ = e * (y * e * y⁻¹) := by
    have h2 : y * (y * e * y⁻¹) * y⁻¹ = (e * (y * e * y⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right (h.prod_eq_one heR)
    rw [h2, mul_inv_rev, inv_eq_of_mul_eq_one_right he2, inv_eq_of_mul_eq_one_right he'2,
      ← hcomm]
  refine ⟨sup_le (zpowers_le.2 heR) (zpowers_le.2 he'R), hel, hcard, ?_,
    mem_sup_left (mem_zpowers e)⟩
  have hle : pairSub y e ≤ (pairSub y e).comap (MulAut.conj y).toMonoidHom := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · show y * e * y⁻¹ ∈ pairSub y e
      exact mem_sup_right (mem_zpowers _)
    · show y * (y * e * y⁻¹) * y⁻¹ ∈ pairSub y e
      rw [hee]
      exact mul_mem (mem_sup_left (mem_zpowers e)) (mem_sup_right (mem_zpowers _))
  intro w hw
  exact hle hw

theorem FpfConj.extend (h : FpfConj R y) [Finite G] {B : Subgroup G} (hBR : B ≤ R)
    (hB : Open.IsElemAbelian 2 B) (hBy : ∀ b ∈ B, y * b * y⁻¹ ∈ B) {e : G} (heR : e ∈ R)
    (he2 : e * e = 1) (heB : e ∉ B) (hcomm : ∀ b ∈ B, b * e = e * b) :
    ∃ B' : Subgroup G, B' ≤ R ∧ Open.IsElemAbelian 2 B' ∧ Nat.card B' = 4 * Nat.card B := by
  have he1 : e ≠ 1 := fun h1 => heB (h1 ▸ B.one_mem)
  obtain ⟨hWR, hWel, hW4, hWy, heW⟩ := h.pair heR he2 he1
  have hBy' : ∀ b ∈ B, y⁻¹ * b * y ∈ B := fun b hb => by
    rw [h.inv_eq (hBR hb)]
    exact hBy _ (hBy b hb)
  have hcomm' : ∀ b ∈ B, b * (y * e * y⁻¹) = (y * e * y⁻¹) * b := by
    intro b hb
    calc b * (y * e * y⁻¹) = y * ((y⁻¹ * b * y) * e) * y⁻¹ := by group
      _ = y * (e * (y⁻¹ * b * y)) * y⁻¹ := by rw [hcomm _ (hBy' b hb)]
      _ = (y * e * y⁻¹) * b := by group
  have hWcent : pairSub y e ≤ centralizer (B : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_iff.2 hcomm))
      (zpowers_le.2 (mem_centralizer_iff.2 hcomm'))
  have hBW : ∀ b ∈ B, ∀ w ∈ pairSub y e, b * w = w * b := fun b hb w hw =>
    mem_centralizer_iff.1 (hWcent hw) b hb
  have hdisj : Disjoint B (pairSub y e) := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    by_contra hx1
    obtain ⟨hxB, hxW⟩ := Subgroup.mem_inf.1 hx
    have hxR : x ∈ R := hBR hxB
    have hx2 : x * x = 1 := by
      have := (SU1.isElemAbelian_iff.1 hWel).2 x hxW
      rwa [pow_two] at this
    obtain ⟨-, -, hX4, -, -⟩ := h.pair hxR hx2 hx1
    have hle1 : pairSub y x ≤ pairSub y e :=
      sup_le (zpowers_le.2 hxW) (zpowers_le.2 (hWy x hxW))
    have hle2 : pairSub y x ≤ B := sup_le (zpowers_le.2 hxB) (zpowers_le.2 (hBy x hxB))
    have heq : pairSub y x = pairSub y e :=
      Subgroup.eq_of_le_of_card_ge hle1 (by rw [hW4, hX4])
    have : e ∈ pairSub y x := by rw [heq]; exact heW
    exact heB (hle2 this)
  refine ⟨B ⊔ pairSub y e, sup_le hBR hWR, SU1.IsElemAbelian.sup hB hWel hBW, ?_⟩
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B (pairSub y e)
    (hWcent.trans (centralizer_le_normalizer _)) hdisj, hW4, mul_comm]

theorem exists_central_involution [Finite G] {R : Subgroup G} (hR : IsPGroup 2 R)
    (hne : R ≠ ⊥) : ∃ a ∈ R, a * a = 1 ∧ a ≠ 1 ∧ ∀ s ∈ R, a * s = s * a := by
  obtain ⟨z, hzR, hz1, hzc⟩ := SU1.exists_central_of_normal Nat.prime_two hR le_rfl
    (fun g hg u hu => R.mul_mem (R.mul_mem hg hu) (R.inv_mem hg)) hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hR) ⟨z, hzR⟩
  have hjz : orderOf z = 2 ^ j := by
    rw [← hj]
    exact Subgroup.orderOf_coe (⟨z, hzR⟩ : ↥R)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hjz
    exact hz1 (orderOf_eq_one_iff.1 hjz)
  have hdvd : 2 ∣ orderOf z := by rw [hjz]; exact dvd_pow_self 2 hj0
  have hord : orderOf (z ^ (orderOf z / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos z).ne' hdvd
  set u := z ^ (orderOf z / 2) with hu
  refine ⟨u, R.pow_mem hzR _, ?_, ?_, fun s hs => ?_⟩
  · rw [← sq]
    exact hord ▸ pow_orderOf_eq_one _
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · exact (Commute.pow_left (show Commute z s from (hzc s hs).symm) _).eq

theorem mem_sup_zpowers_of_sq {R : Subgroup G} {z : G} (hz : z * z = 1)
    (hzR : ∀ r ∈ R, z * r * z⁻¹ ∈ R) {u : G} (hu : u ∈ R ⊔ zpowers z) :
    u ∈ R ∨ ∃ r ∈ R, u = r * z := by
  have hzmem : z ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hzR g, fun hg => ?_⟩
    have h2 : z * (z * g * z⁻¹) * z⁻¹ = g := by
      calc z * (z * g * z⁻¹) * z⁻¹ = (z * z) * g * (z * z)⁻¹ := by group
        _ = g := by rw [hz]; group
    have h3 := hzR _ hg
    rwa [h2] at h3
  have hnorm : zpowers z ≤ normalizer (R : Set G) := zpowers_le.2 hzmem
  have hu' : u ∈ ((R : Set G) * (zpowers z : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R (zpowers z) hnorm]
    exact hu
  obtain ⟨r, hr, c, hc, rfl⟩ := hu'
  rcases eq_one_or_eq_of_mem_zpowers hz hc with rfl | rfl
  · exact Or.inl (by simpa using hr)
  · exact Or.inr ⟨r, hr, rfl⟩

end Pair

end LemmaYAux

open LemmaYAux

theorem lemmaY {G : Type} [Group G] [Finite G] (R : Subgroup G) (hR : IsPGroup 2 R) (y : G)
    (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (hy3 : ∀ r ∈ R, y ^ 3 * r * (y ^ 3)⁻¹ = r)
    (hC : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1) :
    R = ⊥ ∨ 4 ≤ Open.pRank 2 R ∨
      ∃ A : Subgroup G, A ≤ R ∧ Open.IsElemAbelian 2 A ∧ Nat.card A = 4 ∧
        (∀ a ∈ A, ∀ r ∈ R, a * r = r * a) ∧ (∀ r ∈ R, r * r = 1 → r ∈ A) := by
  have h : FpfConj R y := ⟨hyR, hy3, hC⟩
  by_cases hR1 : R = ⊥
  · exact Or.inl hR1
  right
  obtain ⟨a, haR, ha2, ha1, hac⟩ := exists_central_involution hR hR1
  obtain ⟨hAR, hAel, hA4, hAy, -⟩ := h.pair haR ha2 ha1
  have hAcent : pairSub y a ≤ centralizer (R : Set G) := by
    refine sup_le (zpowers_le.2 (mem_centralizer_iff.2 fun s hs => (hac s hs).symm))
      (zpowers_le.2 (mem_centralizer_iff.2 fun s hs => ?_))
    have hs' : y⁻¹ * s * y ∈ R := h.inv_mem hs
    calc s * (y * a * y⁻¹) = y * ((y⁻¹ * s * y) * a) * y⁻¹ := by group
      _ = y * (a * (y⁻¹ * s * y)) * y⁻¹ := by rw [← hac _ hs']
      _ = (y * a * y⁻¹) * s := by group
  have hAc : ∀ a' ∈ pairSub y a, ∀ r ∈ R, a' * r = r * a' := fun a' ha' r hr =>
    (mem_centralizer_iff.1 (hAcent ha') r hr).symm
  by_cases hex : ∃ e ∈ R, e * e = 1 ∧ e ∉ pairSub y a
  · left
    obtain ⟨e, heR, he2, heA⟩ := hex
    obtain ⟨B', hB'R, hB'el, hB'4⟩ :=
      h.extend hAR hAel hAy heR he2 heA (fun b hb => hAc b hb e heR)
    have : Nat.card B' = 2 ^ 4 := by rw [hB'4, hA4]; norm_num
    exact SU1.le_pRank (by norm_num) hB'R hB'el this
  · right
    push Not at hex
    exact ⟨pairSub y a, hAR, hAel, hA4, hAc, hex⟩

theorem no_rank_three {G : Type} [Group G] [Finite G] (R : Subgroup G) (hR : IsPGroup 2 R) (y z : G)
    (hz : z * z = 1) (hzR : ∀ r ∈ R, z * r * z⁻¹ ∈ R) (_hzn : z ∉ R)
    (hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) (hy3 : ∀ r ∈ R, y ^ 3 * r * (y ^ 3)⁻¹ = r)
    (_hzy : z * y * z⁻¹ = y⁻¹) (hC : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1)
    (A : Subgroup G) (hAR : A ≤ R) (hA : Open.IsElemAbelian 2 A) (hA4 : Nat.card A = 4)
    (hAc : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a) (hAz : ∃ a ∈ A, z * a * z⁻¹ ≠ a) :
    Open.pRank 2 (R ⊔ zpowers z) ≠ 3 := by
  intro h3
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := (SU1.isElemAbelian_iff.1 hA).2 a ha
    rwa [pow_two] at this
  rcases lemmaY R hR y hyR hy3 hC with hbot | h4 | ⟨A', hA'R, hA'e, hA'4, -, hA'inv⟩
  · have := Subgroup.card_le_of_le hAR
    rw [hbot, Subgroup.card_bot] at this
    omega
  · have := SU1.pRank_mono (p := 2) (by norm_num) (le_sup_left : R ≤ R ⊔ zpowers z)
    omega
  ·
    have hAA' : A ≤ A' := fun a ha => hA'inv a (hAR ha) (hAsq a ha)
    have hAeq : A = A' := Subgroup.eq_of_le_of_card_ge hAA' (by rw [hA4, hA'4])
    have hinv : ∀ r ∈ R, r * r = 1 → r ∈ A := fun r hr hr2 => by
      rw [hAeq]
      exact hA'inv r hr hr2
    obtain ⟨E, hET, hE, hE8⟩ :=
      SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two (k := 3) h3.ge
    have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
      have := (SU1.isElemAbelian_iff.1 hE).2 x hx
      rwa [pow_two] at this
    have hEcomm := (SU1.isElemAbelian_iff.1 hE).1
    have hER : ∀ x ∈ E, x ∈ R → x ∈ A := fun x hx hxR => hinv x hxR (hEsq x hx)
    obtain ⟨u, huE, huR⟩ : ∃ u ∈ E, u ∉ R := by
      by_contra hcon
      push Not at hcon
      have hEA : E ≤ A := fun x hx => hER x hx (hcon x hx)
      have := Subgroup.card_le_of_le hEA
      rw [hE8, hA4] at this
      norm_num at this
    obtain ⟨r, hrR, hur⟩ : ∃ r ∈ R, u = r * z :=
      (mem_sup_zpowers_of_sq hz hzR (hET huE)).resolve_left huR
    have hE0 : E ≤ (E ⊓ R) ⊔ zpowers u := by
      intro x hx
      by_cases hxR : x ∈ R
      · exact mem_sup_left ⟨hx, hxR⟩
      · obtain ⟨r', hr'R, hxr'⟩ :=
          (mem_sup_zpowers_of_sq hz hzR (hET hx)).resolve_left hxR
        have hxu : x * u⁻¹ ∈ R := by
          rw [hxr', hur]
          have : r' * z * (r * z)⁻¹ = r' * r⁻¹ := by group
          rw [this]
          exact R.mul_mem hr'R (R.inv_mem hrR)
        have hxuE : x * u⁻¹ ∈ E := E.mul_mem hx (E.inv_mem huE)
        have : x = (x * u⁻¹) * u := by group
        rw [this]
        exact mul_mem_sup (show x * u⁻¹ ∈ E ⊓ R from ⟨hxuE, hxu⟩) (mem_zpowers u)
    have hcommEu : ∀ a ∈ E ⊓ R, ∀ b ∈ zpowers u, a * b = b * a := fun a ha b hb =>
      hEcomm a ha.1 b (zpowers_le.2 huE hb)
    have hzp : Nat.card (zpowers u) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hEsq u huE)
    have h8 : 8 ≤ Nat.card ↥(E ⊓ R) * 2 := by
      calc 8 = Nat.card E := by rw [hE8]; norm_num
        _ ≤ Nat.card ((E ⊓ R) ⊔ zpowers u : Subgroup G) := Subgroup.card_le_of_le hE0
        _ ≤ Nat.card ↥(E ⊓ R) * Nat.card (zpowers u) := SU1.card_sup_le_of_commute hcommEu
        _ ≤ Nat.card ↥(E ⊓ R) * 2 := Nat.mul_le_mul_left _ hzp
    have hE0A : E ⊓ R ≤ A := fun x hx => hER x hx.1 hx.2
    have hEA : E ⊓ R = A := Subgroup.eq_of_le_of_card_ge hE0A (by rw [hA4]; omega)
    have hAE : A ≤ E := hEA ▸ inf_le_left
    obtain ⟨a, haA, haz⟩ := hAz
    have hcomm := hEcomm u huE a (hAE haA)
    rw [hur] at hcomm
    have h1 : r * (z * a * z⁻¹) = a * r := by
      calc r * (z * a * z⁻¹) = (r * z * a) * z⁻¹ := by group
        _ = (a * (r * z)) * z⁻¹ := by rw [hcomm]
        _ = a * r := by group
    exact haz (mul_left_cancel (h1.trans (hAc a haA r hrR)))

end CFSG.GH74.Uniqueness.SU.K.R3
