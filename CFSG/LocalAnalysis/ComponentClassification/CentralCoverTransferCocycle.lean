module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

theorem zmod_two_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  revert e
  decide

@[simp] theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

theorem zmod_two_add_self (e : ZMod 2) : e + e = 0 := CharTwo.add_self_eq_zero e

theorem zmod_two_two : (2 : ZMod 2) = 0 := rfl

@[expose] def coboundary {Q : Type*} [Mul Q] (b : Q → ZMod 2) (x y : Q) : ZMod 2 :=
  b x + b y + b (x * y)

theorem coboundary_apply {Q : Type*} [Mul Q] (b : Q → ZMod 2) (x y : Q) :
    coboundary b x y = b x + b y + b (x * y) := rfl

structure NormCocycle (Q : Type*) [Group Q] where
  toFun : Q → Q → ZMod 2
  map_one_left : ∀ b, toFun 1 b = 0
  map_one_right : ∀ a, toFun a 1 = 0
  cocycle : ∀ a b c, toFun a b + toFun (a * b) c = toFun b c + toFun a (b * c)

namespace NormCocycle

variable {Q : Type*} [Group Q]

instance : CoeFun (NormCocycle Q) fun _ => Q → Q → ZMod 2 := ⟨toFun⟩

theorem inv_comm (f : NormCocycle Q) (a : Q) : f a a⁻¹ = f a⁻¹ a := by
  have h := f.cocycle a a⁻¹ a
  rwa [mul_inv_cancel, inv_mul_cancel, f.map_one_left, f.map_one_right, add_zero,
    add_zero] at h

end NormCocycle

@[ext] structure CocycleExtension {Q : Type*} [Group Q] (f : NormCocycle Q) where
  fst : ZMod 2
  snd : Q
deriving DecidableEq

namespace CocycleExtension

variable {Q : Type*} [Group Q] {f : NormCocycle Q}

instance : Group (CocycleExtension f) where
  mul x y := ⟨x.fst + y.fst + f x.snd y.snd, x.snd * y.snd⟩
  mul_assoc x y w := by
    ext
    · change x.fst + y.fst + f x.snd y.snd + w.fst + f (x.snd * y.snd) w.snd =
        x.fst + (y.fst + w.fst + f y.snd w.snd) + f x.snd (y.snd * w.snd)
      linear_combination f.cocycle x.snd y.snd w.snd
    · exact mul_assoc x.snd y.snd w.snd
  one := ⟨0, 1⟩
  one_mul x := by
    ext
    · change 0 + x.fst + f 1 x.snd = x.fst
      rw [f.map_one_left, zero_add, add_zero]
    · exact one_mul x.snd
  mul_one x := by
    ext
    · change x.fst + 0 + f x.snd 1 = x.fst
      rw [f.map_one_right, add_zero, add_zero]
    · exact mul_one x.snd
  inv x := ⟨x.fst + f x.snd x.snd⁻¹, x.snd⁻¹⟩
  inv_mul_cancel x := by
    ext
    · change x.fst + f x.snd x.snd⁻¹ + x.fst + f x.snd⁻¹ x.snd = 0
      rw [f.inv_comm]
      linear_combination (x.fst + f x.snd⁻¹ x.snd) * zmod_two_two
    · exact inv_mul_cancel x.snd

@[simp] theorem mul_fst (x y : CocycleExtension f) :
    (x * y).fst = x.fst + y.fst + f x.snd y.snd := rfl

@[simp] theorem mul_snd (x y : CocycleExtension f) : (x * y).snd = x.snd * y.snd := rfl

@[simp] theorem one_fst : (1 : CocycleExtension f).fst = 0 := rfl

@[simp] theorem one_snd : (1 : CocycleExtension f).snd = 1 := rfl

@[simp] theorem inv_fst (x : CocycleExtension f) : x⁻¹.fst = x.fst + f x.snd x.snd⁻¹ := rfl

@[simp] theorem inv_snd (x : CocycleExtension f) : x⁻¹.snd = x.snd⁻¹ := rfl

theorem mk_mul_mk (e d : ZMod 2) (s t : Q) :
    (⟨e, s⟩ * ⟨d, t⟩ : CocycleExtension f) = ⟨e + d + f s t, s * t⟩ := rfl

theorem one_def : (1 : CocycleExtension f) = ⟨0, 1⟩ := rfl

theorem mk_one_mul (e : ZMod 2) (x : CocycleExtension f) :
    (⟨e, 1⟩ : CocycleExtension f) * x = ⟨e + x.fst, x.snd⟩ := by
  ext
  · change e + x.fst + f 1 x.snd = e + x.fst
    rw [f.map_one_left, add_zero]
  · exact one_mul x.snd

theorem mul_mk_one (x : CocycleExtension f) (e : ZMod 2) :
    x * (⟨e, 1⟩ : CocycleExtension f) = ⟨x.fst + e, x.snd⟩ := by
  ext
  · change x.fst + e + f x.snd 1 = x.fst + e
    rw [f.map_one_right, add_zero]
  · exact mul_one x.snd

theorem mk_one_mem_center (e : ZMod 2) :
    (⟨e, 1⟩ : CocycleExtension f) ∈ center (CocycleExtension f) := by
  rw [Subgroup.mem_center_iff]
  intro x
  rw [mk_one_mul, mul_mk_one, add_comm]

theorem mem_center_of_snd_eq_one {x : CocycleExtension f} (hx : x.snd = 1) :
    x ∈ center (CocycleExtension f) := by
  have : x = ⟨x.fst, 1⟩ := by ext <;> simp [hx]
  rw [this]
  exact mk_one_mem_center x.fst

theorem mk_one_pow_val (e : ZMod 2) : (⟨1, 1⟩ : CocycleExtension f) ^ e.val = ⟨e, 1⟩ := by
  rcases zmod_two_cases e with rfl | rfl
  · rfl
  · exact pow_one _

theorem mk_one_one_ne_one : (⟨1, 1⟩ : CocycleExtension f) ≠ 1 := by
  intro h
  have h1 : (1 : ZMod 2) = 0 := congrArg CocycleExtension.fst h
  exact absurd h1 (by decide)

@[expose] def proj (f : NormCocycle Q) : CocycleExtension f →* Q where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem proj_apply (x : CocycleExtension f) : proj f x = x.snd := rfl

@[expose] def equivProd (f : NormCocycle Q) : CocycleExtension f ≃ ZMod 2 × Q where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Q] : Fintype (CocycleExtension f) := Fintype.ofEquiv _ (equivProd f).symm

instance [Finite Q] : Finite (CocycleExtension f) := Finite.of_equiv _ (equivProd f).symm

theorem card_eq [Finite Q] : Nat.card (CocycleExtension f) = 2 * Nat.card Q := by
  rw [Nat.card_congr (equivProd f), Nat.card_prod, Nat.card_zmod]

@[expose] def coboundaryEquiv {f f' : NormCocycle Q} (η : Q → ZMod 2)
    (h : ∀ x y, f' x y = f x y + coboundary η x y) :
    CocycleExtension f' ≃* CocycleExtension f where
  toFun x := ⟨x.fst + η x.snd, x.snd⟩
  invFun x := ⟨x.fst + η x.snd, x.snd⟩
  left_inv x := by
    ext
    · change x.fst + η x.snd + η x.snd = x.fst
      rw [add_assoc, zmod_two_add_self, add_zero]
    · rfl
  right_inv x := by
    ext
    · change x.fst + η x.snd + η x.snd = x.fst
      rw [add_assoc, zmod_two_add_self, add_zero]
    · rfl
  map_mul' x y := by
    ext
    · change x.fst + y.fst + f' x.snd y.snd + η (x.snd * y.snd) =
        x.fst + η x.snd + (y.fst + η y.snd) + f x.snd y.snd
      rw [h, coboundary_apply]
      linear_combination η (x.snd * y.snd) * zmod_two_two
    · rfl

@[simp] theorem coboundaryEquiv_apply {f f' : NormCocycle Q} (η : Q → ZMod 2)
    (h : ∀ x y, f' x y = f x y + coboundary η x y) (x : CocycleExtension f') :
    coboundaryEquiv η h x = ⟨x.fst + η x.snd, x.snd⟩ := rfl

theorem mulEquiv_eq_mk_one_one {A : Type*} [Group A] (Φ : A ≃* CocycleExtension f) {a : A}
    (ha : a ≠ 1) (hΦ : (Φ a).snd = 1) : Φ a = ⟨1, 1⟩ := by
  ext
  · rcases zmod_two_cases (Φ a).fst with h | h
    · refine absurd ?_ ha
      apply Φ.injective
      rw [map_one]
      ext
      · exact h
      · exact hΦ
    · exact h
  · exact hΦ

end CocycleExtension

structure IsCentralDoubleExt {E Q : Type*} [Group E] [Group Q] (π : E →* Q) (z : E) : Prop where
  surjective : Function.Surjective π
  mem_center : z ∈ center E
  orderOf_eq : orderOf z = 2
  ker_eq : π.ker = zpowers z

theorem CocycleExtension.isCentralDoubleExt_proj {Q : Type*} [Group Q] (f : NormCocycle Q) :
    IsCentralDoubleExt (CocycleExtension.proj f) ⟨1, 1⟩ where
  surjective q := ⟨⟨0, q⟩, rfl⟩
  mem_center := CocycleExtension.mk_one_mem_center 1
  orderOf_eq := by
    apply orderOf_eq_prime
    · rw [sq, CocycleExtension.mk_mul_mk, f.map_one_left]
      ext
      · rfl
      · exact mul_one 1
    · exact CocycleExtension.mk_one_one_ne_one
  ker_eq := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 rfl))
    have hx1 : x.snd = 1 := hx
    have : x = (⟨1, 1⟩ : CocycleExtension f) ^ x.fst.val := by
      rw [CocycleExtension.mk_one_pow_val]
      ext
      · rfl
      · exact hx1
    rw [this]
    exact pow_mem (mem_zpowers _) _

noncomputable def binCoord {E : Type*} (x y : E) : ZMod 2 :=
  haveI := Classical.propDecidable (x = y)
  if x = y then 0 else 1

namespace IsCentralDoubleExt

variable {E Q : Type*} [Group E] [Group Q] {π : E →* Q} {z : E} (hπ : IsCentralDoubleExt π z)
include hπ

theorem sq_eq_one : z ^ 2 = 1 := by
  rw [← hπ.orderOf_eq]
  exact pow_orderOf_eq_one z

theorem ne_one : z ≠ 1 := by
  intro h
  have h2 := hπ.orderOf_eq
  rw [h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem map_z : π z = 1 := by
  rw [← MonoidHom.mem_ker, hπ.ker_eq]
  exact mem_zpowers z

theorem commute (x : E) : z * x = x * z :=
  ((Subgroup.mem_center_iff.1 hπ.mem_center) x).symm

theorem pow_val_add (a b : ZMod 2) : z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · change z ^ 0 = z ^ 1 * z ^ 1
    rw [← pow_add, hπ.sq_eq_one, pow_zero]

theorem pow_val_injective : Function.Injective fun a : ZMod 2 => z ^ a.val := by
  intro a b h
  have h' : z ^ a.val = z ^ b.val := h
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [ZMod.val_zero, zmod_two_val_one, pow_zero, pow_one] at h'
    exact absurd h'.symm hπ.ne_one
  · rw [ZMod.val_zero, zmod_two_val_one, pow_zero, pow_one] at h'
    exact absurd h' hπ.ne_one
  · rfl

theorem pow_val_inj {a b : ZMod 2} : z ^ a.val = z ^ b.val ↔ a = b :=
  ⟨fun h => hπ.pow_val_injective h, fun h => h ▸ rfl⟩

theorem pow_val_commute (a : ZMod 2) (x : E) : z ^ a.val * x = x * z ^ a.val :=
  ((Subgroup.mem_center_iff.1 (pow_mem hπ.mem_center a.val)) x).symm

theorem mul_pow_val_mul (a : ZMod 2) (x y : E) : x * (z ^ a.val * y) = z ^ a.val * (x * y) :=
  (mul_assoc x _ y).symm.trans
    ((congrArg (· * y) (hπ.pow_val_commute a x).symm).trans (mul_assoc _ x y))

theorem map_pow_val (a : ZMod 2) : π (z ^ a.val) = 1 := by
  rw [map_pow, hπ.map_z, one_pow]

theorem pow_val_mul_cancel {a b : ZMod 2} {x : E} (h : z ^ a.val * x = z ^ b.val * x) : a = b :=
  hπ.pow_val_inj.1 (mul_right_cancel h)

theorem eq_or_eq_mul {x y : E} (h : π x = π y) : x = y ∨ x = z * y := by
  have hmem : x * y⁻¹ ∈ zpowers z := by
    rw [← hπ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  rw [← zpow_mod_orderOf, hπ.orderOf_eq] at hk
  rcases Int.emod_two_eq_zero_or_one k with h2 | h2
  · left
    rw [Nat.cast_ofNat, h2, zpow_zero] at hk
    exact mul_inv_eq_one.1 hk.symm
  · right
    rw [Nat.cast_ofNat, h2, zpow_one] at hk
    rw [hk, inv_mul_cancel_right]

theorem eq_pow_binCoord_mul {x y : E} (h : π x = π y) : x = z ^ (binCoord x y).val * y := by
  unfold binCoord
  split_ifs with hxy
  · rw [hxy]
    simp
  · rcases hπ.eq_or_eq_mul h with h' | h'
    · exact absurd h' hxy
    · rw [h']
      simp

theorem binCoord_eq {x y : E} {e : ZMod 2} (h : x = z ^ e.val * y) : binCoord x y = e := by
  have hxy : π x = π y := by rw [h, map_mul, hπ.map_pow_val, one_mul]
  have h' := hπ.eq_pow_binCoord_mul hxy
  exact hπ.pow_val_mul_cancel (h'.symm.trans h)

theorem subgroupComap (S : Subgroup Q) :
    IsCentralDoubleExt (π.subgroupComap S)
      ⟨z, by rw [Subgroup.mem_comap, hπ.map_z]; exact S.one_mem⟩ where
  surjective s := by
    obtain ⟨x, hx⟩ := hπ.surjective s
    refine ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact s.2⟩, Subtype.ext ?_⟩
    exact hx
  mem_center := Subgroup.mem_center_iff.2 fun x => Subtype.ext (hπ.commute x).symm
  orderOf_eq := by
    rw [← Subgroup.orderOf_coe]
    exact hπ.orderOf_eq
  ker_eq := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      have hx' : (x : E) ∈ zpowers z := by
        rw [← hπ.ker_eq, MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx'
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, rfl⟩
      apply Subtype.ext
      change π ((z : E) ^ k) = 1
      rw [map_zpow, hπ.map_z, one_zpow]

theorem exists_mulEquiv_of_section (u : Q → E) (hu : ∀ g, π (u g) = g) (F : NormCocycle Q)
    (η : Q → ZMod 2) (hF : ∀ g k, u g * u k = z ^ (F g k + coboundary η g k).val * u (g * k)) :
    ∃ Ψ : E ≃* CocycleExtension F,
      (∀ x, (Ψ x).snd = π x) ∧ Ψ z = ⟨1, 1⟩ ∧ ∀ g, Ψ (u g) = ⟨η g, g⟩ := by
  set c : E → ZMod 2 := fun x => binCoord x (u (π x))
  have hc : ∀ x, x = z ^ (c x).val * u (π x) := fun x => hπ.eq_pow_binCoord_mul (by rw [hu])
  have hcu : ∀ g, c (u g) = 0 := fun g =>
    hπ.binCoord_eq (by rw [hu]; simp)
  have hmul : ∀ x y, c (x * y) = c x + c y + (F (π x) (π y) + coboundary η (π x) (π y)) := by
    intro x y
    apply hπ.binCoord_eq
    rw [map_mul]
    calc x * y = z ^ (c x).val * u (π x) * (z ^ (c y).val * u (π y)) := by
          rw [← hc x, ← hc y]
      _ = z ^ (c x).val * z ^ (c y).val * (u (π x) * u (π y)) := by
          rw [mul_assoc (z ^ (c x).val) (u (π x)), hπ.mul_pow_val_mul,
            ← mul_assoc (z ^ (c x).val) (z ^ (c y).val)]
      _ = _ := by
          rw [hF, ← mul_assoc, ← hπ.pow_val_add, ← hπ.pow_val_add]
  let Ψ₀ : E →* CocycleExtension F := MonoidHom.mk' (fun x => ⟨c x + η (π x), π x⟩) fun x y => by
    ext
    · change c (x * y) + η (π (x * y)) = c x + η (π x) + (c y + η (π y)) + F (π x) (π y)
      rw [hmul, map_mul, coboundary_apply]
      linear_combination η (π x * π y) * zmod_two_two
    · exact map_mul π x y
  have hinj : Function.Injective Ψ₀ := by
    intro x y h
    have h1 : π x = π y := congrArg CocycleExtension.snd h
    have h2 : c x + η (π x) = c y + η (π y) := congrArg CocycleExtension.fst h
    rw [h1, add_left_inj] at h2
    rw [hc x, hc y, h1, h2]
  have hsurj : Function.Surjective Ψ₀ := by
    intro w
    refine ⟨z ^ (w.fst + η w.snd).val * u w.snd, ?_⟩
    have hπw : π (z ^ (w.fst + η w.snd).val * u w.snd) = w.snd := by
      rw [map_mul, hπ.map_pow_val, one_mul, hu]
    have hcw : c (z ^ (w.fst + η w.snd).val * u w.snd) = w.fst + η w.snd :=
      hπ.binCoord_eq (by rw [hπw])
    ext
    · change c _ + η (π _) = w.fst
      rw [hcw, hπw, add_assoc, zmod_two_add_self, add_zero]
    · exact hπw
  have hu1 : u 1 = z ^ (η 1).val := by
    have h := hF 1 1
    rw [F.map_one_left, coboundary_apply, mul_one, zero_add, zmod_two_add_self, zero_add] at h
    exact mul_right_cancel h
  refine ⟨MulEquiv.ofBijective Ψ₀ ⟨hinj, hsurj⟩, fun x => rfl, ?_, fun g => ?_⟩
  · have hz : c z = 1 + η 1 := by
      apply hπ.binCoord_eq
      rw [hπ.map_z, hu1, ← hπ.pow_val_add, add_assoc, zmod_two_add_self, add_zero]
      exact (pow_one z).symm
    ext
    · change c z + η (π z) = 1
      rw [hz, hπ.map_z, add_assoc, zmod_two_add_self, add_zero]
    · exact hπ.map_z
  · ext
    · change c (u g) + η (π (u g)) = η g
      rw [hcu, hu, zero_add]
    · exact hu g

theorem exists_comap_mulEquiv_of_section (S : Subgroup Q) (u₀ : S → E)
    (hu₀ : ∀ s, π (u₀ s) = s) (f : NormCocycle S) (b : S → ZMod 2)
    (hf : ∀ s t, u₀ s * u₀ t = z ^ (f s t + coboundary b s t).val * u₀ (s * t)) :
    ∃ ι : S.comap π ≃* CocycleExtension f,
      (∀ x, ((ι x).snd : Q) = π x) ∧ ∀ s, ((ι.symm ⟨b s, s⟩ : S.comap π) : E) = u₀ s := by
  have hmem : ∀ s : S, u₀ s ∈ S.comap π := fun s => by
    rw [Subgroup.mem_comap, hu₀]
    exact s.2
  obtain ⟨Ψ, hΨ, -, hΨu⟩ := (hπ.subgroupComap S).exists_mulEquiv_of_section
    (fun s => ⟨u₀ s, hmem s⟩) (fun s => Subtype.ext (hu₀ s)) f b
    (fun s t => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow]
      exact hf s t))
  refine ⟨Ψ, fun x => congrArg Subtype.val (hΨ x), fun s => ?_⟩
  rw [← hΨu s, MulEquiv.symm_apply_apply]

end IsCentralDoubleExt

theorem exists_comap_mulEquiv {E G : Type*} [Group E] [Group G] {π : E →* G}
    {F : NormCocycle G} (Ψ : E ≃* CocycleExtension F) (hΨ : ∀ x, (Ψ x).snd = π x)
    {S : Subgroup G} (f : NormCocycle S) (μ : S → ZMod 2)
    (hμ : ∀ s t : S, F s t + coboundary μ s t = f s t) :
    ∃ ι : S.comap π ≃* CocycleExtension f,
      ∀ x : S.comap π, ι x = ⟨(Ψ x).fst + μ ⟨π x, x.2⟩, ⟨π x, x.2⟩⟩ := by
  let ι₀ : S.comap π →* CocycleExtension f :=
    MonoidHom.mk' (fun x => ⟨(Ψ x).fst + μ ⟨π x, x.2⟩, ⟨π x, x.2⟩⟩) fun x y => by
      have hxy : (⟨π (x * y : E), (x * y).2⟩ : S) = ⟨π x, x.2⟩ * ⟨π y, y.2⟩ :=
        Subtype.ext (map_mul π (x : E) y)
      have hfst : (Ψ (x * y : E)).fst = (Ψ x).fst + (Ψ y).fst + F (π x) (π y) := by
        rw [map_mul, CocycleExtension.mul_fst, hΨ, hΨ]
      have h := hμ ⟨π x, x.2⟩ ⟨π y, y.2⟩
      rw [coboundary_apply] at h
      refine CocycleExtension.ext ?_ ?_
      · change (Ψ (x * y : E)).fst + μ ⟨π (x * y : E), (x * y).2⟩ =
          (Ψ x).fst + μ ⟨π x, x.2⟩ + ((Ψ y).fst + μ ⟨π y, y.2⟩) + f ⟨π x, x.2⟩ ⟨π y, y.2⟩
        rw [hfst, hxy, ← h]
        change _ = _ + _ + (F (π x) (π y) + _)
        grind
      · exact hxy
  have hinj : Function.Injective ι₀ := by
    intro x y h
    have h1 : π x = π y := congrArg Subtype.val (congrArg CocycleExtension.snd h)
    have h2 : (Ψ x).fst + μ ⟨π x, x.2⟩ = (Ψ y).fst + μ ⟨π y, y.2⟩ :=
      congrArg CocycleExtension.fst h
    have h3 : (⟨π x, x.2⟩ : S) = ⟨π y, y.2⟩ := Subtype.ext h1
    rw [h3, add_left_inj] at h2
    apply Subtype.ext
    apply Ψ.injective
    refine CocycleExtension.ext ?_ ?_
    · exact h2
    · rw [hΨ, hΨ, h1]
  have hsurj : Function.Surjective ι₀ := by
    intro w
    have hmem : Ψ.symm ⟨w.fst + μ w.snd, w.snd⟩ ∈ S.comap π := by
      rw [Subgroup.mem_comap, ← hΨ, MulEquiv.apply_symm_apply]
      exact w.snd.2
    have hπw : (⟨π (Ψ.symm ⟨w.fst + μ w.snd, w.snd⟩), hmem⟩ : S) = w.snd := by
      apply Subtype.ext
      change π _ = _
      rw [← hΨ, MulEquiv.apply_symm_apply]
    refine ⟨⟨_, hmem⟩, ?_⟩
    refine CocycleExtension.ext ?_ ?_
    · change (Ψ (Ψ.symm _)).fst + μ ⟨π (Ψ.symm _), hmem⟩ = w.fst
      rw [hπw, MulEquiv.apply_symm_apply, add_assoc, zmod_two_add_self, add_zero]
    · exact hπw
  exact ⟨MulEquiv.ofBijective ι₀ ⟨hinj, hsurj⟩, fun x => rfl⟩

end CFSG.ComponentClassification.CentralCover
