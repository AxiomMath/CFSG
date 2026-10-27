module

public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryAutomorphismEnd
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup mem_bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

theorem eq_one_of_pow_two_pow_of_pow_odd {M : Type*} [Monoid M] {g : M} {k m : ℕ}
    (h1 : g ^ (2 ^ k) = 1) (hm : Odd m) (h2 : g ^ m = 1) : g = 1 := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have hd1 := orderOf_dvd_of_pow_eq_one h1
  have hd2 := orderOf_dvd_of_pow_eq_one h2
  have h := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  exact orderOf_eq_one_iff.mp h

theorem isPGroup_two_mulAut_of_isCyclic {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y]
    (hY : IsPGroup 2 Y) : IsPGroup 2 (MulAut Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  rcases k with _ | k
  · apply IsPGroup.of_card (n := 0)
    rw [IsCyclic.card_mulAut, hk, pow_zero, Nat.totient_one]
  · apply IsPGroup.of_card (n := k)
    rw [IsCyclic.card_mulAut, hk, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
    simp

theorem mulAut_eq_one_of_odd {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y] (hY : IsPGroup 2 Y)
    {σ : MulAut Y} {m : ℕ} (hm : Odd m) (hσ : σ ^ m = 1) : σ = 1 := by
  obtain ⟨k, hk⟩ := isPGroup_two_mulAut_of_isCyclic hY σ
  exact eq_one_of_pow_two_pow_of_pow_odd hk hm hσ

theorem mulAut_apply_eq_of_mem_center {D : Type*} [Group D] [Finite D] [IsCyclic (center D)]
    (hZ : IsPGroup 2 (center D)) (σ : MulAut D) {m : ℕ} (hm : Odd m) (hσ : σ ^ m = 1)
    {c : D} (hc : c ∈ center D) : σ c = c := by
  have hmem : ∀ (τ : MulAut D) (c : D), c ∈ center D → τ c ∈ center D := by
    intro τ c hc
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := τ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hc g']
  let τ : MulAut (center D) :=
    { toFun := fun c => ⟨σ (c : D), hmem σ c c.2⟩
      invFun := fun c => ⟨σ.symm (c : D), hmem σ.symm c c.2⟩
      left_inv := fun c => Subtype.ext (σ.symm_apply_apply (c : D))
      right_inv := fun c => Subtype.ext (σ.apply_symm_apply (c : D))
      map_mul' := fun c c' => Subtype.ext (map_mul σ (c : D) (c' : D)) }
  have hτpow : ∀ (n : ℕ) (c : center D), (((τ ^ n) c : center D) : D) = (σ ^ n) c := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ← ih]
      rfl
  have hτ : τ ^ m = 1 := MulEquiv.ext fun c => Subtype.ext (by
    rw [hτpow, hσ]
    rfl)
  have h1 := mulAut_eq_one_of_odd hZ hm hτ
  have h2 := hτpow 1 ⟨c, hc⟩
  rw [pow_one, h1, pow_one] at h2
  exact h2.symm

theorem mulAut_eq_one_of_odd_of_inv_mul_mem {D : Type*} [Group D] {N : Subgroup D}
    (hN : IsPGroup 2 N) {σ : MulAut D} {m : ℕ} (hm : Odd m) (hσ : σ ^ m = 1)
    (hfix : ∀ c ∈ N, σ c = c) (hmod : ∀ d, d⁻¹ * σ d ∈ N) : σ = 1 := by
  ext d
  have hcN : d⁻¹ * σ d ∈ N := hmod d
  have hpow : ∀ n : ℕ, (σ ^ n) d = d * (d⁻¹ * σ d) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hfix _ (pow_mem hcN n), pow_succ',
        mul_assoc d⁻¹, mul_inv_cancel_left]
  have h1 : (d⁻¹ * σ d) ^ m = 1 := by
    have h := hpow m
    rw [hσ, MulAut.one_apply] at h
    have h' : d * (d⁻¹ * σ d) ^ m = d * 1 := by rw [← h, mul_one]
    exact mul_left_cancel h'
  obtain ⟨k, hk⟩ := hN ⟨_, hcN⟩
  have h2 : (d⁻¹ * σ d) ^ (2 ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have h3 := eq_one_of_pow_two_pow_of_pow_odd h2 hm h1
  rw [MulAut.one_apply]
  calc σ d = d * (d⁻¹ * σ d) := by group
    _ = d := by rw [h3, mul_one]

section Commutators

variable {D : Type*} [Group D]

theorem commutatorElement_mul_left_of_mem_center' {x x' y : D} (h : ⁅x', y⁆ ∈ center D) :
    ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have hc := mem_center_iff.mp h x
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * y * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x', y⁆ * x * y * x⁻¹ * y⁻¹ := by rw [hc]
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, y⁆ * ⁅x', y⁆ := (mem_center_iff.mp h _).symm

theorem commutatorElement_mul_right_of_mem_center' {x y y' : D} (h : ⁅x, y'⁆ ∈ center D) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have hc := mem_center_iff.mp h y⁻¹
  calc ⁅x, y * y'⁆ = x * y * x⁻¹ * (⁅x, y'⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = x * y * x⁻¹ * (y⁻¹ * ⁅x, y'⁆) := by rw [hc]
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := by
        simp only [commutatorElement_def]
        group

theorem commutatorElement_eq_one_of_mem_center_left {x y : D} (h : x ∈ center D) : ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h y).symm

theorem commutatorElement_eq_one_of_mem_center_right {x y : D} (h : y ∈ center D) : ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h x)

variable [IsElementaryAbelian 2 (D ⧸ center D)]

theorem commutatorElement_mem_center_of_isElementaryAbelian (x y : D) : ⁅x, y⁆ ∈ center D := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

theorem mul_self_mem_center_of_isElementaryAbelian (x : D) : x * x ∈ center D := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (D ⧸ center D)) (x : D ⧸ center D)
  rwa [pow_two] at h

theorem commutatorElement_mul_self_of_isElementaryAbelian (x y : D) : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
  rw [← commutatorElement_mul_left_of_mem_center'
    (commutatorElement_mem_center_of_isElementaryAbelian x y)]
  exact commutatorElement_eq_one_of_mem_center_left (mul_self_mem_center_of_isElementaryAbelian x)

theorem commutatorElement_eq_one_or_eq [Finite D] [IsCyclic (center D)] {z : D}
    (hzZ : z ∈ center D) (hz : orderOf z = 2) (x y : D) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := by
  by_cases h1 : ⁅x, y⁆ = 1
  · exact Or.inl h1
  right
  have hc := commutatorElement_mem_center_of_isElementaryAbelian x y
  have ho : orderOf (⟨⁅x, y⁆, hc⟩ : center D) = 2 := by
    rw [Subgroup.orderOf_mk]
    apply orderOf_eq_prime
    · rw [pow_two]
      exact commutatorElement_mul_self_of_isElementaryAbelian x y
    · exact h1
  have hz' : orderOf (⟨z, hzZ⟩ : center D) = 2 := by rw [Subgroup.orderOf_mk, hz]
  exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic ho hz')

end Commutators

section Form

variable {D : Type*} [Group D]

open Classical in
@[expose] noncomputable def commSign (x y : D) : ZMod 2 := if ⁅x, y⁆ = 1 then 0 else 1

theorem commSign_eq_zero_iff {x y : D} : commSign x y = 0 ↔ ⁅x, y⁆ = 1 := by
  unfold commSign
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

variable {z : D}

theorem commutatorElement_eq_pow_commSign (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z)
    (x y : D) : ⁅x, y⁆ = z ^ (commSign x y).val := by
  unfold commSign
  split_ifs with h
  · rw [h, ZMod.val_zero, pow_zero]
  · rw [(hzz x y).resolve_left h, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem commSign_mul_left (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz1 : z ≠ 1)
    (hzsq : z * z = 1) (hc : ∀ x y : D, ⁅x, y⁆ ∈ center D) (x x' y : D) :
    commSign (x * x') y = commSign x y + commSign x' y := by
  have hmul := commutatorElement_mul_left_of_mem_center' (hc x' y) (x := x)
  unfold commSign
  rcases hzz x y with h | h <;> rcases hzz x' y with h' | h' <;>
    simp only [hmul, h, h', mul_one, one_mul, hzsq, hz1, ite_true, ite_false] <;> decide

theorem commSign_mul_right (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz1 : z ≠ 1)
    (hzsq : z * z = 1) (hc : ∀ x y : D, ⁅x, y⁆ ∈ center D) (x y y' : D) :
    commSign x (y * y') = commSign x y + commSign x y' := by
  have hmul := commutatorElement_mul_right_of_mem_center' (hc x y') (y := y)
  unfold commSign
  rcases hzz x y with h | h <;> rcases hzz x y' with h' | h' <;>
    simp only [hmul, h, h', mul_one, one_mul, hzsq, hz1, ite_true, ite_false] <;> decide

theorem commSign_mul_center (hc : ∀ x y : D, ⁅x, y⁆ ∈ center D) {x y c c' : D}
    (hcZ : c ∈ center D) (hc'Z : c' ∈ center D) : commSign (x * c) (y * c') = commSign x y := by
  have h1 : ⁅x * c, y * c'⁆ = ⁅x, y⁆ := by
    rw [commutatorElement_mul_left_of_mem_center' (hc c (y * c')),
      commutatorElement_eq_one_of_mem_center_left hcZ, mul_one,
      commutatorElement_mul_right_of_mem_center' (hc x c'),
      commutatorElement_eq_one_of_mem_center_right hc'Z, mul_one]
  unfold commSign
  rw [h1]

theorem commSign_self (x : D) : commSign x x = 0 :=
  commSign_eq_zero_iff.mpr (commutatorElement_self x)

variable [IsElementaryAbelian 2 (D ⧸ center D)]

theorem commSign_out (x y : D) :
    commSign (Quotient.out (x : D ⧸ center D)) (Quotient.out (y : D ⧸ center D)) =
      commSign x y := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (center D) x
  obtain ⟨c', hc'⟩ := QuotientGroup.mk_out_eq_mul (center D) y
  rw [hc, hc']
  exact commSign_mul_center commutatorElement_mem_center_of_isElementaryAbelian c.2 c'.2

@[expose] noncomputable def commSignFun (v w : Additive (D ⧸ center D)) : ZMod 2 :=
  commSign (Quotient.out (Additive.toMul v)) (Quotient.out (Additive.toMul w))

theorem commSignFun_mk (x y : D) :
    commSignFun (Additive.ofMul (x : D ⧸ center D)) (Additive.ofMul (y : D ⧸ center D)) =
      commSign x y :=
  commSign_out x y

theorem commSignFun_add_left (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz1 : z ≠ 1)
    (hzsq : z * z = 1) (v v' w : Additive (D ⧸ center D)) :
    commSignFun (v + v') w = commSignFun v w + commSignFun v' w := by
  have hc := commutatorElement_mem_center_of_isElementaryAbelian (D := D)
  unfold commSignFun
  have h1 : Additive.toMul (v + v') = ((Quotient.out (Additive.toMul v) *
      Quotient.out (Additive.toMul v') : D) : D ⧸ center D) := by
    rw [toMul_add, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [h1]
  obtain ⟨c, hc'⟩ := QuotientGroup.mk_out_eq_mul (center D)
    (Quotient.out (Additive.toMul v) * Quotient.out (Additive.toMul v'))
  have h2 := commSign_mul_center hc c.2 (one_mem _)
    (x := Quotient.out (Additive.toMul v) * Quotient.out (Additive.toMul v'))
    (y := Quotient.out (Additive.toMul w))
  rw [mul_one] at h2
  rw [hc', h2, commSign_mul_left hzz hz1 hzsq hc]

theorem commSignFun_add_right (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz1 : z ≠ 1)
    (hzsq : z * z = 1) (v w w' : Additive (D ⧸ center D)) :
    commSignFun v (w + w') = commSignFun v w + commSignFun v w' := by
  have hc := commutatorElement_mem_center_of_isElementaryAbelian (D := D)
  unfold commSignFun
  have h1 : Additive.toMul (w + w') = ((Quotient.out (Additive.toMul w) *
      Quotient.out (Additive.toMul w') : D) : D ⧸ center D) := by
    rw [toMul_add, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [h1]
  obtain ⟨c, hc'⟩ := QuotientGroup.mk_out_eq_mul (center D)
    (Quotient.out (Additive.toMul w) * Quotient.out (Additive.toMul w'))
  have h2 := commSign_mul_center hc (one_mem _) c.2
    (x := Quotient.out (Additive.toMul v))
    (y := Quotient.out (Additive.toMul w) * Quotient.out (Additive.toMul w'))
  rw [mul_one] at h2
  rw [hc', h2, commSign_mul_right hzz hz1 hzsq hc]

theorem ne_one_of_orderOf_eq_two {G : Type*} [Monoid G] {z : G} (hz : orderOf z = 2) : z ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Monoid G] {z : G} (hz : orderOf z = 2) :
    z * z = 1 := by
  rw [← pow_two, ← hz, pow_orderOf_eq_one]

@[expose] noncomputable def commSignForm (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z)
    (hz : orderOf z = 2) :
    LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D)) :=
  LinearMap.mk₂ (ZMod 2) commSignFun
    (commSignFun_add_left hzz (ne_one_of_orderOf_eq_two hz) (mul_self_eq_one_of_orderOf_eq_two hz))
    (fun c v w => ZMod.map_smul (n := 2) (M₁ := ZMod 2)
      (AddMonoidHom.mk' (fun v => commSignFun v w)
        (fun v v' => commSignFun_add_left hzz (ne_one_of_orderOf_eq_two hz)
          (mul_self_eq_one_of_orderOf_eq_two hz) v v' w) :
        Additive (D ⧸ center D) →+ ZMod 2) c v)
    (commSignFun_add_right hzz (ne_one_of_orderOf_eq_two hz)
      (mul_self_eq_one_of_orderOf_eq_two hz))
    (fun c v w => ZMod.map_smul (n := 2) (M₁ := ZMod 2)
      (AddMonoidHom.mk' (fun w => commSignFun v w)
        (fun w w' => commSignFun_add_right hzz (ne_one_of_orderOf_eq_two hz)
          (mul_self_eq_one_of_orderOf_eq_two hz) v w w') :
        Additive (D ⧸ center D) →+ ZMod 2) c w)

theorem commSignForm_apply (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz : orderOf z = 2)
    (x y : D) :
    commSignForm hzz hz (Additive.ofMul (x : D ⧸ center D)) (Additive.ofMul (y : D ⧸ center D)) =
      commSign x y :=
  commSignFun_mk x y

theorem commSignForm_isAlt (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) (hz : orderOf z = 2) :
    (commSignForm hzz hz).IsAlt := by
  intro v
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (x : D ⧸ center D) := by rw [hx]; rfl
  rw [hv, commSignForm_apply, commSign_self]

theorem commSignForm_nondegenerate [Finite D] (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z)
    (hz : orderOf z = 2) : (commSignForm hzz hz).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv' : v = Additive.ofMul (x : D ⧸ center D) := by rw [hx]; rfl
  rw [hv'] at hv ⊢
  have hxZ : x ∈ center D := by
    rw [mem_center_iff]
    intro y
    have h := hv (Additive.ofMul (y : D ⧸ center D))
    rw [commSignForm_apply, commSign_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  have h1 : (x : D ⧸ center D) = 1 := (QuotientGroup.eq_one_iff x).mpr hxZ
  rw [h1]
  rfl

end Form

section Action

variable {H : Type*} [Group H] (D : Subgroup H) [D.Normal] [IsElementaryAbelian 2 (D ⧸ center D)]

@[expose] noncomputable def centerQuotientConjGL :
    H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D)) :=
  ((CFSG.SignalizerFunctor.Helpers.elementaryAutomorphismEnd 2).comp
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAction (center D)
      MulAut.conjNormal)).toHomUnits

theorem centerQuotientConjGL_apply (h : H) (x : D) :
    ((centerQuotientConjGL D h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (D ⧸ center D))) : Module.End (ZMod 2) (Additive (D ⧸ center D)))
      (Additive.ofMul (x : D ⧸ center D)) =
      Additive.ofMul ((MulAut.conjNormal h x : D) : D ⧸ center D) := rfl

end Action

section Core

theorem eq_one_of_mem_of_odd_orderOf {H : Type*} [Group H] {P : Subgroup H} (hP : IsPGroup 2 P)
    {g : H} (hg : g ∈ P) (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  exact eq_one_of_pow_two_pow_of_pow_odd hk' hodd (pow_orderOf_eq_one g)

variable {H : Type*} [Group H] [Finite H]

theorem symplectic_core (hH : IsCharacteristicP 2 H) {D : Subgroup H} [hDn : D.Normal]
    (hDQ : D ≤ pCore 2 H) [IsCyclic (center D)] [IsElementaryAbelian 2 (D ⧸ center D)]
    (hQD : ∀ q ∈ pCore 2 H, ∀ d d' : D, ⁅q, (d : H)⁆ * d' = d' * ⁅q, (d : H)⁆)
    (hCQ : ∀ q ∈ pCore 2 H, (∀ d : D, q * d = d * q) → q ∈ D)
    {z : D} (hzZ : z ∈ center D) (hz : orderOf z = 2) :
    (∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z) ∧
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D)),
      (∀ x y : D, ⁅x, y⁆ = z ^ (b (Additive.ofMul (x : D ⧸ center D))
        (Additive.ofMul (y : D ⧸ center D))).val) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      (centerQuotientConjGL D).ker = pCore 2 H ∧
      (∀ h, centerQuotientConjGL D h ∈ bilinIsometryGroup b) ∧
      (∃ ι : H ⧸ pCore 2 H →* bilinIsometryGroup b, Function.Injective ι ∧
        ∀ h : H, ((ι (h : H ⧸ pCore 2 H) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D))) =
            centerQuotientConjGL D h) ∧
      ∀ K : Subgroup H, Odd (Nat.card K) →
        Function.Injective ((centerQuotientConjGL D).comp K.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCore 2 H with hQ
  have hQp : IsPGroup 2 Q := pCore_isPGroup
  have hDp : IsPGroup 2 D := hQp.to_le hDQ
  have hZp : IsPGroup 2 (center D) := hDp.to_subgroup _
  have hzz := commutatorElement_eq_one_or_eq hzZ hz
  set b := commSignForm hzz hz with hb
  set ρ := centerQuotientConjGL D with hρ
  have hV : ∀ v : Additive (D ⧸ center D), ∃ x : D, v = Additive.ofMul (x : D ⧸ center D) := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, by rw [hx]; rfl⟩
  have hQker : Q ≤ ρ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := hV v
    rw [Units.val_one, Module.End.one_apply, hρ, centerQuotientConjGL_apply]
    congr 1
    rw [QuotientGroup.eq, mem_center_iff]
    intro d'
    apply Subtype.ext
    have hcomm : Commute ⁅q, (x : H)⁆ (x : H) := hQD q hq x x
    have hcd : Commute ⁅q, (x : H)⁆ (d' : H) := hQD q hq x d'
    have hcx' : q * (x : H) * q⁻¹ = ⁅q, (x : H)⁆ * x := by
      rw [commutatorElement_def]
      group
    have he : ((((MulAut.conjNormal q) x)⁻¹ * x : D) : H) = ⁅q, (x : H)⁆⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, hcx']
      calc (⁅q, (x : H)⁆ * x)⁻¹ * x = (x : H)⁻¹ * (⁅q, (x : H)⁆⁻¹ * x) := by group
        _ = (x : H)⁻¹ * (x * ⁅q, (x : H)⁆⁻¹) := by rw [hcomm.inv_left.eq]
        _ = ⁅q, (x : H)⁆⁻¹ := by group
    have he' : ((((MulAut.conjNormal q) x)⁻¹ * x * d' : D) : H) =
        (((MulAut.conjNormal q) x)⁻¹ * x : D) * (d' : H) := Subgroup.coe_mul _ _ _
    have he'' : ((d' * (((MulAut.conjNormal q) x)⁻¹ * x) : D) : H) =
        (d' : H) * (((MulAut.conjNormal q) x)⁻¹ * x : D) := Subgroup.coe_mul _ _ _
    rw [he', he'', he]
    exact hcd.inv_left.eq.symm
  have hodd1 : ∀ g ∈ ρ.ker, Odd (orderOf g) → g = 1 := by
    intro g hg hodd
    have hgm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    have htriv : ∀ x : D, ((MulAut.conjNormal g x : D) : D ⧸ center D) = (x : D ⧸ center D) := by
      intro x
      have h1 : ((ρ g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D ⧸ center D))) :
          Module.End (ZMod 2) (Additive (D ⧸ center D))) (Additive.ofMul (x : D ⧸ center D)) =
          Additive.ofMul (x : D ⧸ center D) := by
        rw [MonoidHom.mem_ker.mp hg]
        rfl
      rw [hρ, centerQuotientConjGL_apply] at h1
      exact Additive.ofMul.injective h1
    set σD : MulAut D := MulAut.conjNormal g with hσD
    have hσDm : σD ^ orderOf g = 1 := by rw [hσD, ← map_pow, hgm, map_one]
    have hσDZ : ∀ c ∈ center D, σD c = c := fun c hc =>
      mulAut_apply_eq_of_mem_center hZp σD hodd hσDm hc
    have hσDmod : ∀ d : D, d⁻¹ * σD d ∈ center D := by
      intro d
      have h2 := QuotientGroup.eq.mp (htriv d)
      have h3 := inv_mem h2
      rwa [mul_inv_rev, inv_inv] at h3
    have hσD1 : σD = 1 := mulAut_eq_one_of_odd_of_inv_mul_mem hZp hodd hσDm hσDZ hσDmod
    have hgD : ∀ d : D, g * (d : H) = d * g := by
      intro d
      have h4 := congrArg (fun f : MulAut D => ((f d : D) : H)) hσD1
      simp only [hσD, MulAut.conjNormal_apply, MulAut.one_apply] at h4
      calc g * (d : H) = g * d * g⁻¹ * g := by group
        _ = d * g := by rw [h4]
    set σQ : MulAut Q := MulAut.conjNormal g with hσQ
    have hσQm : σQ ^ orderOf g = 1 := by rw [hσQ, ← map_pow, hgm, map_one]
    set N : Subgroup Q := ((center D).map D.subtype).subgroupOf Q with hN
    have hNp : IsPGroup 2 N := hQp.to_subgroup N
    have hσQN : ∀ c ∈ N, σQ c = c := by
      intro c hc
      obtain ⟨d, _, hdc⟩ := mem_subgroupOf.mp hc
      apply Subtype.ext
      rw [hσQ, MulAut.conjNormal_apply, ← hdc]
      change g * (d : H) * g⁻¹ = d
      rw [hgD d]
      group
    have hσQmod : ∀ q : Q, q⁻¹ * σQ q ∈ N := by
      intro q
      rw [mem_subgroupOf]
      have hc : ((q⁻¹ * σQ q : Q) : H) = (q : H)⁻¹ * (g * q * g⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hσQ, MulAut.conjNormal_apply]
      rw [hc]
      have hcQ : (q : H)⁻¹ * (g * q * g⁻¹) ∈ Q :=
        Q.mul_mem (Q.inv_mem q.2) ((pCore_normal (p := 2) (G := H)).conj_mem _ q.2 g)
      have hcD : ∀ d : D, (q : H)⁻¹ * (g * q * g⁻¹) * d = d * ((q : H)⁻¹ * (g * q * g⁻¹)) := by
        intro d
        obtain ⟨qh, hqh⟩ := q
        obtain ⟨dh, hdh⟩ := d
        change qh⁻¹ * (g * qh * g⁻¹) * dh = dh * (qh⁻¹ * (g * qh * g⁻¹))
        have hd1 : qh * dh * qh⁻¹ ∈ D := hDn.conj_mem _ hdh qh
        have e1 : g * (qh * dh * qh⁻¹) = qh * dh * qh⁻¹ * g := hgD ⟨_, hd1⟩
        have e2 : g⁻¹ * dh = dh * g⁻¹ := by
          calc g⁻¹ * dh = g⁻¹ * (dh * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * dh) * g⁻¹ := by rw [hgD ⟨dh, hdh⟩]
            _ = dh * g⁻¹ := by group
        calc qh⁻¹ * (g * qh * g⁻¹) * dh = qh⁻¹ * g * qh * (g⁻¹ * dh) := by group
          _ = qh⁻¹ * g * qh * (dh * g⁻¹) := by rw [e2]
          _ = qh⁻¹ * (g * (qh * dh * qh⁻¹)) * qh * g⁻¹ := by group
          _ = qh⁻¹ * (qh * dh * qh⁻¹ * g) * qh * g⁻¹ := by rw [e1]
          _ = dh * (qh⁻¹ * (g * qh * g⁻¹)) := by group
      have hcD' : (q : H)⁻¹ * (g * q * g⁻¹) ∈ D := hCQ _ hcQ hcD
      refine ⟨⟨_, hcD'⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro d
      exact Subtype.ext (hcD d).symm
    have hσQ1 : σQ = 1 := mulAut_eq_one_of_odd_of_inv_mul_mem hNp hodd hσQm hσQN hσQmod
    have hgC : g ∈ centralizer (Q : Set H) := by
      rw [mem_centralizer_iff]
      intro q hq
      have h5 := congrArg (fun f : MulAut Q => ((f ⟨q, hq⟩ : Q) : H)) hσQ1
      simp only [hσQ, MulAut.conjNormal_apply, MulAut.one_apply] at h5
      calc q * g = g * q * g⁻¹ * g := by rw [h5]
        _ = g * q := by group
    exact eq_one_of_mem_of_odd_orderOf hQp (hH hgC) hodd
  have hkerp : IsPGroup 2 ρ.ker := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg0 : orderOf (g : H) ≠ 0 := (orderOf_pos (g : H)).ne'
    obtain ⟨a, m, hm, hgam⟩ := Nat.exists_eq_two_pow_mul_odd hg0
    have hdvd : 2 ^ a ∣ orderOf (g : H) := ⟨m, hgam⟩
    have h1 : orderOf ((g : H) ^ (2 ^ a)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) hdvd, hgam, Nat.mul_div_cancel_left _ (by positivity)]
    have h2 : (g : H) ^ (2 ^ a) = 1 :=
      hodd1 _ (pow_mem g.2 _) (by rw [h1]; exact hm)
    have h3 : orderOf (g : H) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨j, by rw [Subgroup.orderOf_coe] at hj; exact hj⟩
  have hker : ρ.ker = Q := le_antisymm (le_sSup ⟨ρ.normal_ker, hkerp⟩) hQker
  have hiso : ∀ h, ρ h ∈ bilinIsometryGroup b := by
    intro h v w
    obtain ⟨x, rfl⟩ := hV v
    obtain ⟨y, rfl⟩ := hV w
    rw [hρ, centerQuotientConjGL_apply, centerQuotientConjGL_apply, hb, commSignForm_apply,
      commSignForm_apply]
    unfold commSign
    rw [← map_commutatorElement, MulEquiv.map_eq_one_iff]
  have hρ'ker : (ρ.codRestrict (bilinIsometryGroup b) hiso).ker = Q := by
    rw [MonoidHom.ker_codRestrict, hker]
  refine ⟨hzz, b, fun x y => ?_, commSignForm_isAlt hzz hz, commSignForm_nondegenerate hzz hz,
    hker, hiso, ⟨(QuotientGroup.kerLift (ρ.codRestrict _ hiso)).comp
      (QuotientGroup.quotientMulEquivOfEq hρ'ker.symm).toMonoidHom, ?_, fun h => rfl⟩, ?_⟩
  · rw [hb, commSignForm_apply]
    exact commutatorElement_eq_pow_commSign hzz x y
  · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact (QuotientGroup.kerLift_injective _).comp (MulEquiv.injective _)
  · intro K hK
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkQ : (k : H) ∈ Q := by
      rw [← hker]
      exact hk
    have hodd : Odd (orderOf (k : H)) := by
      rw [Subgroup.orderOf_coe]
      exact hK.of_dvd_nat (orderOf_dvd_natCard k)
    exact Subtype.ext (eq_one_of_mem_of_odd_orderOf hQp hkQ hodd)

end Core

section Complements

theorem exists_unique_involution_center {D : Type*} [Group D] [Finite D] [Nontrivial D]
    [IsCyclic (center D)] (hD : IsPGroup 2 D) :
    ∃ z : D, z ∈ center D ∧ orderOf z = 2 ∧ ∀ z' ∈ center D, orderOf z' = 2 → z' = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (center D) := hD.center_nontrivial
  have h2 : 2 ∣ Nat.card (center D) := by
    obtain ⟨n, hn⟩ := (hD.to_subgroup (center D)).exists_card_eq
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center D) 2 h2
  refine ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz, fun z' hz' hz'2 => ?_⟩
  have := eq_of_orderOf_eq_two_of_isCyclic (X := center D) (u := ⟨z', hz'⟩) (v := z)
    ((Subgroup.orderOf_mk _ _).trans hz'2) hz
  exact congrArg Subtype.val this

variable {D : Type*} [Group D] [Finite D] [IsElementaryAbelian 2 (D ⧸ center D)]

theorem existsUnique_finrank_eq_two_mul {b : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D))}
    (hba : b.IsAlt) (hbn : b.Nondegenerate) :
    ∃! w : ℕ, Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * w := by
  have : Module.Finite (ZMod 2) (Additive (D ⧸ center D)) := Module.Finite.of_finite
  obtain ⟨w, hw⟩ := LinearMap.BilinForm.IsAlt.even_finrank hba hbn
  exact ⟨w, by rw [hw]; ring, fun w' hw' => by omega⟩

theorem finrank_eq_zero_iff_forall_mem_center :
    Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 0 ↔ ∀ x : D, x ∈ center D := by
  have : Module.Finite (ZMod 2) (Additive (D ⧸ center D)) := Module.Finite.of_finite
  rw [_root_.finrank_zero_iff_forall_zero]
  constructor
  · intro h x
    have h1 := h (Additive.ofMul (x : D ⧸ center D))
    exact (QuotientGroup.eq_one_iff x).mp (Additive.ofMul.injective h1)
  · intro h v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (x : D ⧸ center D) := by rw [hx]; rfl
    rw [hv, (QuotientGroup.eq_one_iff x).mpr (h x)]
    rfl

omit [Finite D] [IsElementaryAbelian 2 (D ⧸ center D)] in
theorem commutator_eq_zpowers_of_exists {z : D} (hzz : ∀ x y : D, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z)
    {x y : D} (hxy : ⁅x, y⁆ ≠ 1) : commutator D = zpowers z := by
  apply le_antisymm
  · rw [_root_.commutator_def, commutator_le]
    intro a _ c _
    rcases hzz a c with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers z
  · rw [zpowers_le, ← (hzz x y).resolve_left hxy]
    exact commutator_mem_commutator (mem_top x) (mem_top y)

omit [Finite D] in
theorem bilinForm_eq_of_commutator_rule {z : D} (hz : orderOf z = 2)
    {b b' : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ center D))}
    (hb : ∀ x y : D, ⁅x, y⁆ = z ^ (b (Additive.ofMul (x : D ⧸ center D))
      (Additive.ofMul (y : D ⧸ center D))).val)
    (hb' : ∀ x y : D, ⁅x, y⁆ = z ^ (b' (Additive.ofMul (x : D ⧸ center D))
      (Additive.ofMul (y : D ⧸ center D))).val) : b' = b := by
  apply LinearMap.ext₂
  intro v w
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
  have hv : v = Additive.ofMul (x : D ⧸ center D) := by rw [hx]; rfl
  have hw : w = Additive.ofMul (y : D ⧸ center D) := by rw [hy]; rfl
  rw [hv, hw]
  apply ZMod.val_injective
  apply pow_injOn_Iio_orderOf (x := z)
  · rw [Set.mem_Iio, hz]
    exact ZMod.val_lt _
  · rw [Set.mem_Iio, hz]
    exact ZMod.val_lt _
  · exact (hb' x y).symm.trans (hb x y)

end Complements

end CFSG.LocalAnalysis.GorensteinLyons
