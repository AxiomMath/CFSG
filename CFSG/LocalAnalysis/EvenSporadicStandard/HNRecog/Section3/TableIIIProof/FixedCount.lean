module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open scoped commutatorElement

private lemma t3_card_le_sq_fixed' {V : Type*} [Group V] [Finite V]
    (hmul : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v ^ 2 = 1) (β : V →* V) (hβ : ∀ v, β (β v) = v) :
    Nat.card V ≤ Nat.card {v : V // β v = v} ^ 2 := by
  letI : CommGroup V := { mul_comm := hmul }
  let g : V →* V := β / MonoidHom.id V
  have hinv : ∀ v : V, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hV v)
  have hker : ∀ v : V, v ∈ g.ker ↔ β v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    change (β / MonoidHom.id V) v = 1 ↔ β v = v
    rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_one]
  have hrange : ∀ x : g.range, β (x : V) = x := by
    intro x
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp x.2
    rw [← hw]
    change β ((β / MonoidHom.id V) w) = (β / MonoidHom.id V) w
    rw [MonoidHom.div_apply, MonoidHom.id_apply]
    rw [div_eq_mul_inv, map_mul, map_inv, hβ w, hinv (β w), hinv w, mul_comm]
  have hker_card : Nat.card g.ker = Nat.card {v : V // β v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hrange_card : Nat.card g.range ≤ Nat.card {v : V // β v = v} :=
    Nat.card_le_card_of_injective
      (fun x : g.range => (⟨(x : V), hrange x⟩ : {v : V // β v = v}))
      (fun a b h =>
        Subtype.ext (congrArg (fun y : {v : V // β v = v} => (y : V)) h))
  have hcard : Nat.card V = Nat.card g.range * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  calc Nat.card V = Nat.card g.range * Nat.card g.ker := hcard
    _ ≤ Nat.card {v : V // β v = v} * Nat.card {v : V // β v = v} :=
        Nat.mul_le_mul hrange_card (le_of_eq hker_card)
    _ = Nat.card {v : V // β v = v} ^ 2 := (sq _).symm

theorem tableIII_card_le_sq_fixed {V : Type*} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (β : V →* V) (hβ : ∀ v, β (β v) = v) :
    Nat.card V ≤ Nat.card {v : V // β v = v} ^ 2 :=
  t3_card_le_sq_fixed' (fun a b => mul_comm a b) hV β hβ

theorem tableIII_two_mul_card_le_sq {G : Type*} [Group G] {W : Subgroup G} [Finite W] {z t : G}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hzW : z ∈ W) (hzc : ∀ w ∈ W, w * z = z * w)
    (hsq : ∀ w ∈ W, w ^ 2 ∈ Subgroup.zpowers z)
    (hcomm : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ Subgroup.zpowers z)
    (htW : ∀ w ∈ W, t * w * t⁻¹ ∈ W) (htW' : ∀ w ∈ W, t⁻¹ * w * t ∈ W)
    (htz : t * z = z * t) (ht2 : t ^ 2 ∈ W) :
    2 * Nat.card W ≤ Nat.card {w : G // w ∈ W ∧ ⁅w, t⁆ ∈ Subgroup.zpowers z} ^ 2 := by
  have hZle : Subgroup.zpowers z ≤ W := Subgroup.zpowers_le.mpr hzW
  let Zs : Subgroup ↥W := (Subgroup.zpowers z).subgroupOf W
  have hZs_center : Zs ≤ Subgroup.center ↥W := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hxZ : (x : G) ∈ Subgroup.zpowers z := hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    rw [← hn]
    exact (Commute.zpow_right (show Commute (w : G) z from hzc w w.2) n).eq
  haveI : Zs.Normal := Subgroup.normal_of_le_center hZs_center
  let ct : ↥W →* ↥W :=
    { toFun := fun w => ⟨t * (w : G) * t⁻¹, htW w w.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hct_apply : ∀ x : ↥W, ((ct x : ↥W) : G) = t * (x : G) * t⁻¹ := fun _ => rfl
  have hconj_z : t * z * t⁻¹ = z := by
    rw [htz, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : ∀ n : ℤ, t * z ^ n * t⁻¹ = z ^ n := by
    intro n
    rw [← conj_zpow (a := t) (b := z) (i := n), hconj_z]
  have hct : Zs ≤ Zs.comap ct := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxZ : (x : G) ∈ Subgroup.zpowers z := hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    change ((ct x : ↥W) : G) ∈ Subgroup.zpowers z
    rw [hct_apply x, ← hn]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, (hconj n).symm⟩
  let V := ↥W ⧸ Zs
  let β : V →* V := QuotientGroup.map Zs Zs ct hct
  have hβmk : ∀ x : ↥W, β (QuotientGroup.mk x) = QuotientGroup.mk (ct x) := fun _ => rfl
  have hVcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a ?_
    intro x
    refine QuotientGroup.induction_on b ?_
    intro y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have hdiv : (x * y) / (y * x) = ⁅x, y⁆ := by
      rw [commutatorElement_def, div_eq_mul_inv, mul_inv_rev]
      group
    rw [hdiv]
    exact hcomm x x.2 y y.2
  have hVexp : ∀ v : V, v ^ 2 = 1 := by
    intro v
    refine QuotientGroup.induction_on v ?_
    intro w
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff (N := Zs) (w ^ 2)).mpr (by
      change ((w ^ 2 : ↥W) : G) ∈ Subgroup.zpowers z
      rw [Subgroup.coe_pow]
      exact hsq w w.2)
  have hβ : ∀ v : V, β (β v) = v := by
    intro v
    refine QuotientGroup.induction_on v ?_
    intro w
    rw [hβmk w, hβmk (ct w)]
    refine (QuotientGroup.eq_iff_div_mem (N := Zs) (x := ct (ct w)) (y := w)).mpr ?_
    change ((ct (ct w) / w : ↥W) : G) ∈ Subgroup.zpowers z
    have hcalc : ((ct (ct w) / w : ↥W) : G) = ⁅t ^ 2, (w : G)⁆ := by
      rw [Subgroup.coe_div, hct_apply (ct w), hct_apply w, commutatorElement_def, pow_two,
        div_eq_mul_inv]
      group
    rw [hcalc]
    exact hcomm (t ^ 2) ht2 w w.2
  have hker_iff : ∀ x : ↥W,
      β (QuotientGroup.mk x) = QuotientGroup.mk x ↔
        ⁅(x : G), t⁆ ∈ Subgroup.zpowers z := by
    intro x
    rw [hβmk x, QuotientGroup.eq_iff_div_mem]
    have hg : ((ct x / x : ↥W) : G) = ⁅t, (x : G)⁆ := by
      rw [Subgroup.coe_div, hct_apply x, commutatorElement_def, div_eq_mul_inv]
    constructor
    · intro h
      have hZ : ⁅t, (x : G)⁆ ∈ Subgroup.zpowers z := by
        rw [← hg]
        exact h
      rw [← commutatorElement_inv] at hZ
      exact inv_mem_iff.mp hZ
    · intro h
      change ((ct x / x : ↥W) : G) ∈ Subgroup.zpowers z
      rw [hg, ← commutatorElement_inv]
      exact inv_mem_iff.mpr h
  have hZcard : Nat.card Zs = 2 := by
    change Nat.card ((Subgroup.zpowers z).subgroupOf W) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hWcard : Nat.card W = Nat.card V * Nat.card Zs :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Zs
  have hKcard : Nat.card {w : G // w ∈ W ∧ ⁅w, t⁆ ∈ Subgroup.zpowers z}
      = Nat.card Zs * Nat.card {v : V // β v = v} := by
    have e : {w : G // w ∈ W ∧ ⁅w, t⁆ ∈ Subgroup.zpowers z} ≃
        ↥(QuotientGroup.mk ⁻¹' ({v : V | β v = v})) :=
    { toFun := fun a => ⟨⟨a.1, a.2.1⟩, by
        rw [Set.mem_preimage, Set.mem_setOf_eq]
        exact (hker_iff ⟨a.1, a.2.1⟩).mpr a.2.2⟩
      invFun := fun b => ⟨(b.1 : G), b.1.2, by
        have hb := b.2
        rw [Set.mem_preimage, Set.mem_setOf_eq] at hb
        exact (hker_iff b.1).mp hb⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun b => Subtype.ext (Subtype.ext rfl) }
    have hpre : Nat.card ↥(QuotientGroup.mk ⁻¹' ({v : V | β v = v}))
        = Nat.card Zs * Nat.card {v : V // β v = v} := by
      rw [Nat.card_congr
            (QuotientGroup.preimageMkEquivSubgroupProdSet Zs {v : V | β v = v}),
        Nat.card_prod]
      rfl
    rw [Nat.card_congr e, hpre]
  have h1 : Nat.card V ≤ Nat.card {v : V // β v = v} ^ 2 :=
    t3_card_le_sq_fixed' hVcomm hVexp β hβ
  calc 2 * Nat.card W = 2 * (Nat.card V * Nat.card Zs) := by rw [hWcard]
    _ = 4 * Nat.card V := by rw [hZcard]; ring
    _ ≤ 4 * Nat.card {v : V // β v = v} ^ 2 := Nat.mul_le_mul_left 4 h1
    _ = (2 * Nat.card {v : V // β v = v}) ^ 2 := by ring
    _ = Nat.card {w : G // w ∈ W ∧ ⁅w, t⁆ ∈ Subgroup.zpowers z} ^ 2 := by
        rw [hKcard, hZcard]

end CFSG.EvenSporadicStandard.HNRecog.Section3
