module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open FiniteField

variable {V : Type*} [CommGroup V]

@[expose] def toAddEnd : MulAut V →* AddMonoid.End (Additive V) where
  toFun g := (g : V →* V).toAdditive
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem toAddEnd_injective : Function.Injective (toAddEnd (V := V)) := by
  intro g h hgh
  ext v
  have := DFunLike.congr_fun hgh (Additive.ofMul v)
  exact congrArg Additive.toMul this

@[expose] def fieldRing (J : Subgroup (MulAut V)) : Subring (AddMonoid.End (Additive V)) :=
  Subring.centralizer (toAddEnd '' (J : Set (MulAut V)))

theorem mem_fieldRing_iff {J : Subgroup (MulAut V)} {x : AddMonoid.End (Additive V)} :
    x ∈ fieldRing J ↔ ∀ a ∈ J, toAddEnd a * x = x * toAddEnd a := by
  rw [fieldRing, Subring.mem_centralizer_iff]
  exact ⟨fun h a ha => h _ ⟨a, ha, rfl⟩, fun h _ ⟨a, ha, he⟩ => he ▸ h a ha⟩

variable {J : Subgroup (MulAut V)}

theorem toAddEnd_mem_fieldRing (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) {a : MulAut V}
    (ha : a ∈ J) : toAddEnd a ∈ fieldRing J :=
  mem_fieldRing_iff.mpr fun b hb => by rw [← map_mul, ← map_mul, hJ b hb a ha]

theorem eq_zero_of_apply_eq_zero (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w)
    {x : AddMonoid.End (Additive V)} (hx : x ∈ fieldRing J) {v₀ : Additive V} (hv₀ : v₀ ≠ 0)
    (h : x v₀ = 0) : x = 0 := by
  ext w
  by_cases hw : w = 0
  · rw [hw, map_zero]
    rfl
  obtain ⟨a, ha, haw⟩ := htrans v₀.toMul w.toMul hv₀ hw
  have hw' : toAddEnd a v₀ = w := congrArg Additive.ofMul haw
  have hc := DFunLike.congr_fun (mem_fieldRing_iff.mp hx a ha) v₀
  change toAddEnd a (x v₀) = x (toAddEnd a v₀) at hc
  rw [← hw', ← hc, h, map_zero]
  rfl

theorem apply_injective (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w)
    {v₀ : Additive V} (hv₀ : v₀ ≠ 0) {x y : AddMonoid.End (Additive V)} (hx : x ∈ fieldRing J)
    (hy : y ∈ fieldRing J) (h : x v₀ = y v₀) : x = y := by
  have := eq_zero_of_apply_eq_zero htrans (sub_mem hx hy) hv₀ (by
    change x v₀ - y v₀ = 0
    rw [h, sub_self])
  exact sub_eq_zero.mp this

theorem exists_eq_toAddEnd (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {v₀ : Additive V} (hv₀ : v₀ ≠ 0)
    {x : AddMonoid.End (Additive V)} (hx : x ∈ fieldRing J) (hx0 : x ≠ 0) :
    ∃ a ∈ J, x = toAddEnd a := by
  have hxv : x v₀ ≠ 0 := fun h => hx0 (eq_zero_of_apply_eq_zero htrans hx hv₀ h)
  obtain ⟨a, ha, hav⟩ := htrans v₀.toMul (x v₀).toMul hv₀ hxv
  exact ⟨a, ha, apply_injective htrans hv₀ hx (toAddEnd_mem_fieldRing hJ ha)
    (congrArg Additive.ofMul hav).symm⟩

theorem fieldRing_mul_comm (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {v₀ : Additive V} (hv₀ : v₀ ≠ 0)
    {x y : AddMonoid.End (Additive V)} (hx : x ∈ fieldRing J) (hy : y ∈ fieldRing J) :
    x * y = y * x := by
  by_cases hx0 : x = 0
  · rw [hx0, zero_mul, mul_zero]
  by_cases hy0 : y = 0
  · rw [hy0, zero_mul, mul_zero]
  obtain ⟨a, ha, rfl⟩ := exists_eq_toAddEnd hJ htrans hv₀ hx hx0
  obtain ⟨b, hb, rfl⟩ := exists_eq_toAddEnd hJ htrans hv₀ hy hy0
  rw [← map_mul, ← map_mul, hJ a ha b hb]

theorem isField_fieldRing (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {v₀ : Additive V} (hv₀ : v₀ ≠ 0) :
    IsField (fieldRing J) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have := DFunLike.congr_fun (congrArg Subtype.val h) v₀
    exact hv₀ this.symm⟩
  mul_comm x y := Subtype.ext (fieldRing_mul_comm hJ htrans hv₀ x.2 y.2)
  mul_inv_cancel {x} hx := by
    have hx0 : (x : AddMonoid.End (Additive V)) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨a, ha, he⟩ := exists_eq_toAddEnd hJ htrans hv₀ x.2 hx0
    refine ⟨⟨toAddEnd a⁻¹, toAddEnd_mem_fieldRing hJ (J.inv_mem ha)⟩, Subtype.ext ?_⟩
    change (x : AddMonoid.End (Additive V)) * toAddEnd a⁻¹ = 1
    rw [he, ← map_mul, mul_inv_cancel, map_one]

theorem card_fieldRing [Finite V] (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {v₀ : Additive V} (hv₀ : v₀ ≠ 0) :
    Nat.card (fieldRing J) = Nat.card V := by
  let ev : fieldRing J → Additive V := fun x => (x : AddMonoid.End (Additive V)) v₀
  have hbij : Function.Bijective ev := by
    refine ⟨fun x y h => Subtype.ext (apply_injective htrans hv₀ x.2 y.2 h), fun w => ?_⟩
    by_cases hw : w = 0
    · exact ⟨0, by rw [hw]; rfl⟩
    obtain ⟨a, ha, haw⟩ := htrans v₀.toMul w.toMul hv₀ hw
    exact ⟨⟨toAddEnd a, toAddEnd_mem_fieldRing hJ ha⟩, congrArg Additive.ofMul haw⟩
  rw [Nat.card_eq_of_bijective ev hbij]
  rfl

theorem finite_addEnd [Finite V] : Finite (AddMonoid.End (Additive V)) :=
  Finite.of_injective (fun x : AddMonoid.End (Additive V) => (x : Additive V → Additive V))
    DFunLike.coe_injective

theorem charP_fieldRing [Finite V] {m : ℕ} (hV : Nat.card V = 2 ^ m)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {v₀ : Additive V} (hv₀ : v₀ ≠ 0) :
    letI : Field (fieldRing J) := (isField_fieldRing hJ htrans hv₀).toField
    CharP (fieldRing J) 2 := by
  let : Field (fieldRing J) := (isField_fieldRing hJ htrans hv₀).toField
  have := finite_addEnd (V := V)
  have : Fintype (fieldRing J) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, card_fieldRing hJ htrans hv₀, hV])

theorem eq_one_of_commute_of_pow_two_pow_eq_one [Finite V] {m : ℕ} (hV : Nat.card V = 2 ^ m)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {g : MulAut V}
    (hg : ∀ a ∈ J, g * a = a * g) {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g = 1 := by
  rcases subsingleton_or_nontrivial V with hV1 | hV1
  · ext v
    exact Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  set v₀ : Additive V := Additive.ofMul v
  have hv₀ : v₀ ≠ 0 := hv
  let : Field (fieldRing J) := (isField_fieldRing hJ htrans hv₀).toField
  have : CharP (fieldRing J) 2 := charP_fieldRing hV hJ htrans hv₀
  have hgR : toAddEnd g ∈ fieldRing J := mem_fieldRing_iff.mpr fun a ha => by
    rw [← map_mul, ← map_mul, hg a ha]
  set r : fieldRing J := ⟨toAddEnd g, hgR⟩
  have hr : r ^ 2 ^ k = 1 := Subtype.ext (by
    change toAddEnd g ^ 2 ^ k = 1
    rw [← map_pow, hgk, map_one])
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, hr, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos two_pos k).ne' |>.mp h0)
  apply toAddEnd_injective
  rw [map_one]
  exact congrArg Subtype.val hr1

theorem conj_eq_pow_of_transitive [Finite V] {f : ℕ} (hV : Nat.card V = (2 ^ f) ^ 2)
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {σ : MulAut V}
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσJ : ∀ a ∈ J, σ⁻¹ * a * σ ∈ J) :
    ∀ a ∈ J, σ⁻¹ * a * σ = a ^ 2 ^ f := by
  classical
  have hV' : Nat.card V = 2 ^ (2 * f) := by rw [hV, ← pow_mul, mul_comm]
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  rcases subsingleton_or_nontrivial V with hV1 | hV1
  · exact absurd (MulEquiv.ext fun v => Subsingleton.elim _ _) hσ1
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  set v₀ : Additive V := Additive.ofMul v
  have hv₀ : v₀ ≠ 0 := hv
  set R := fieldRing J
  let : Field R := (isField_fieldRing hJ htrans hv₀).toField
  have := finite_addEnd (V := V)
  have : Fintype R := Fintype.ofFinite _
  have : CharP R 2 := charP_fieldRing hV' hJ htrans hv₀
  let : Algebra (ZMod 2) R := ZMod.algebra R 2
  have hrank : Module.finrank (ZMod 2) R = 2 * f := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := R)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, card_fieldRing hJ htrans hv₀, hV'] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  set s := toAddEnd σ
  set s' := toAddEnd σ⁻¹
  have hss' : s * s' = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hs's : s' * s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hconjJ : ∀ a ∈ J, s' * toAddEnd a * s = toAddEnd (σ⁻¹ * a * σ) := fun a _ => by
    rw [map_mul, map_mul]
  have hmemR : ∀ x ∈ R, s' * x * s ∈ R := by
    intro x hx
    rw [mem_fieldRing_iff] at hx ⊢
    intro b hb
    have hb' : σ⁻¹ * (σ * b * σ⁻¹) * σ = b := by group
    have hbJ : σ * b * σ⁻¹ ∈ J := by
      have := hσJ b hb
      rw [hσinv] at this
      rw [hσinv]
      exact this
    have hb'' : toAddEnd b = s' * toAddEnd (σ * b * σ⁻¹) * s := by
      rw [hconjJ _ hbJ, hb']
    rw [hb'']
    set y := toAddEnd (σ * b * σ⁻¹)
    have hyx : y * x = x * y := hx _ hbJ
    calc s' * y * s * (s' * x * s) = s' * ((y * x) * s) := by
          simp only [mul_assoc]; rw [← mul_assoc s s', hss', one_mul]
      _ = s' * ((x * y) * s) := by rw [hyx]
      _ = s' * x * s * (s' * y * s) := by
          simp only [mul_assoc]; rw [← mul_assoc s s', hss', one_mul]
  let τ : R →+* R :=
    { toFun := fun x => ⟨s' * x * s, hmemR x x.2⟩
      map_one' := Subtype.ext (by
        change s' * 1 * s = 1
        rw [mul_one, hs's])
      map_mul' := fun x y => Subtype.ext (by
        change s' * (x * y : AddMonoid.End (Additive V)) * s =
          (s' * x * s) * (s' * y * s)
        simp only [mul_assoc]
        rw [← mul_assoc s s', hss', one_mul])
      map_zero' := Subtype.ext (by
        change s' * 0 * s = 0
        rw [mul_zero, zero_mul])
      map_add' := fun x y => Subtype.ext (by
        change s' * (x + y : AddMonoid.End (Additive V)) * s = s' * x * s + s' * y * s
        rw [mul_add, add_mul]) }
  have hτ : ∀ x : R, ((τ x : R) : AddMonoid.End (Additive V)) = s' * x * s := fun x => rfl
  let τ' : R →ₐ[ZMod 2] R :=
    { τ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (τ.comp (algebraMap (ZMod 2) R))
          (algebraMap (ZMod 2) R)) r }
  have hτ' : ∀ x : R, τ' x = τ x := fun x => rfl
  have hτ2 : τ' * τ' = 1 := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    change ((τ (τ x) : R) : AddMonoid.End (Additive V)) = x
    rw [hτ, hτ]
    have hs'2 : s' * s' = 1 := by rw [← map_mul, hσinv, hσ2, map_one]
    have hs2 : s * s = 1 := by rw [← map_mul, hσ2, map_one]
    simp only [mul_assoc]
    rw [hs2, mul_one, ← mul_assoc, hs'2, one_mul]
  obtain ⟨n, hn⟩ := (bijective_frobeniusAlgHom_pow (ZMod 2) R).2 τ'
  replace hn : frobeniusAlgHom (ZMod 2) R ^ (n : ℕ) = τ' := hn
  have hpow : ∀ x : R, τ' x = x ^ 2 ^ (n : ℕ) := by
    intro x
    rw [← hn]
    change (frobeniusAlgHom (ZMod 2) R ^ (n : ℕ)) x = _
    rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hord := orderOf_frobeniusAlgHom (ZMod 2) R
  rw [hrank] at hord
  have hdvd : 2 * f ∣ 2 * (n : ℕ) := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, hn, sq, hτ2]
  have hn2 : (n : ℕ) < 2 * f := hrank ▸ n.2
  have hfn : f ∣ (n : ℕ) := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
  obtain ⟨k, hk⟩ := hfn
  have hk1 : k < 2 := by
    by_contra hk2
    push Not at hk2
    have : 2 * f ≤ (n : ℕ) := by rw [hk]; nlinarith
    omega
  intro a ha
  have haR := toAddEnd_mem_fieldRing hJ ha
  have key : toAddEnd (σ⁻¹ * a * σ) = toAddEnd a ^ 2 ^ (n : ℕ) := by
    rw [← hconjJ a ha]
    have := congrArg Subtype.val (hpow ⟨toAddEnd a, haR⟩)
    rw [hτ', hτ] at this
    rw [this]
    rfl
  interval_cases k
  ·
    exfalso
    apply hσ1
    refine eq_one_of_commute_of_pow_two_pow_eq_one hV' hJ htrans (k := 1) (fun b hb => ?_)
      (by rw [pow_one, sq, hσ2])
    have hkey : toAddEnd (σ⁻¹ * b * σ) = toAddEnd b := by
      rw [← hconjJ b hb]
      have := congrArg Subtype.val (hpow ⟨toAddEnd b, toAddEnd_mem_fieldRing hJ hb⟩)
      rw [hτ', hτ, hk, mul_zero, pow_zero, pow_one] at this
      exact this
    have := toAddEnd_injective hkey
    calc σ * b = σ * (σ⁻¹ * b * σ) := by rw [this]
      _ = b * σ := by group
  ·
    rw [hk, mul_one] at key
    rw [← map_pow] at key
    exact toAddEnd_injective key

end CFSG.LocalAnalysis.EvenBN.U4
