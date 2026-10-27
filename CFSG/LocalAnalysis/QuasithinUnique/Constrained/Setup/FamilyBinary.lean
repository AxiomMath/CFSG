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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.QuasithinUnique.Setup.Family

open Module

variable {W : Type*} [CommGroup W]

instance binaryModule [h : Fact (∀ w : W, w * w = 1)] : Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    have h2 : Additive.toMul x * Additive.toMul x = 1 := h.out _
    apply Additive.toMul.injective
    simp only [toMul_nsmul, toMul_zero]
    rw [pow_two]
    exact h2

@[expose] def binaryLin [Fact (∀ w : W, w * w = 1)] :
    MulAut W →* (Additive W ≃ₗ[ZMod 2] Additive W) where
  toFun g :=
    { (MulEquiv.toAdditive g : Additive W ≃+ Additive W) with
      map_smul' := fun r x =>
        ZMod.map_smul (MulEquiv.toAdditive g : Additive W ≃+ Additive W) r x }
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

theorem binaryLin_apply [Fact (∀ w : W, w * w = 1)] (g : MulAut W) (w : W) :
    binaryLin g (Additive.ofMul w) = Additive.ofMul (g w) := rfl

theorem toMul_binaryLin [Fact (∀ w : W, w * w = 1)] (g : MulAut W) (x : Additive W) :
    Additive.toMul (binaryLin g x) = g (Additive.toMul x) := rfl

theorem binaryLin_injective [Fact (∀ w : W, w * w = 1)] :
    Function.Injective (binaryLin : MulAut W →* (Additive W ≃ₗ[ZMod 2] Additive W)) := by
  intro g h hgh
  ext w
  have := LinearEquiv.congr_fun hgh (Additive.ofMul w)
  simpa [binaryLin_apply] using this

theorem card_fixed_binaryLin [Fact (∀ w : W, w * w = 1)] {G : Type*} [Group G]
    (ρ : G →* MulAut W) (A : Subgroup G) :
    Nat.card {w : Additive W // ∀ g ∈ A, binaryLin (ρ g) w = w} =
      Nat.card {w : W // ∀ g ∈ A, ρ g w = w} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun w => ?_)
  constructor
  · intro h g hg
    exact congrArg Additive.toMul (h g hg)
  · intro h g hg
    exact congrArg Additive.ofMul (h g hg)

theorem card_range_displacement [Fact (∀ w : W, w * w = 1)] [Finite W] (l : MulAut W) :
    Nat.card (Set.range fun v : W => l v * v⁻¹) =
      2 ^ finrank (ZMod 2)
        (LinearMap.range ((binaryLin l : Additive W →ₗ[ZMod 2] Additive W) - 1)) := by
  have h1 : Nat.card ↥(LinearMap.range ((binaryLin l : Additive W →ₗ[ZMod 2] Additive W) - 1)) =
      2 ^ finrank (ZMod 2)
        (LinearMap.range ((binaryLin l : Additive W →ₗ[ZMod 2] Additive W) - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun w => ?_)
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨Additive.ofMul v, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, binaryLin_apply]
    rw [← ofMul_div, div_eq_mul_inv]
  · rintro ⟨x, hx⟩
    refine ⟨Additive.toMul x, ?_⟩
    have := congrArg Additive.toMul hx
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, toMul_sub,
      toMul_binaryLin] at this
    rw [div_eq_mul_inv] at this
    exact this

theorem eq_one_of_centralizes_irreducible {W : Type} [CommGroup W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {c : MulAut W} (hc : ∀ l ∈ L, c * l = l * c) (hc2 : c * c = 1) : c = 1 := by
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w : W, c w ≠ w := by
    by_contra h
    push Not at h
    exact hne (MulEquiv.ext h)
  let U : Subgroup W :=
    { carrier := {x | c x = x}
      one_mem' := map_one c
      mul_mem' := fun {x y} hx hy => by
        have hx' : c x = x := hx
        have hy' : c y = y := hy
        show c (x * y) = x * y
        rw [map_mul, hx', hy']
      inv_mem' := fun {x} hx => by
        have hx' : c x = x := hx
        show c x⁻¹ = x⁻¹
        rw [map_inv, hx'] }
  have hUinv : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U := by
    intro g hg u hu
    have hu' : c u = u := hu
    show c (g u) = g u
    have := congrArg (fun f : MulAut W => f u) (hc g hg)
    simp only [MulAut.mul_apply] at this
    rw [this, hu']
  have hw' : c w * w⁻¹ ∈ U := by
    show c (c w * w⁻¹) = c w * w⁻¹
    have h1 : c (c w) = w := by
      have := congrArg (fun f : MulAut W => f w) hc2
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, h1]
    have h2 : c w * w⁻¹ = (c w * w⁻¹)⁻¹ := by
      have := hW (c w * w⁻¹)
      exact eq_inv_of_mul_eq_one_left this
    rw [h2]
    group
  rcases hL U hUinv with h | h
  · rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hw'
    exact hw hw'
  · have hwU : w ∈ U := by rw [h]; trivial
    exact hw (hwU : c w = w)

theorem eq_one_of_pow_two_pow {W : Type} [CommGroup W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {z : MulAut W} (hz : ∀ l ∈ L, z * l = l * z) :
    ∀ k : ℕ, z ^ (2 ^ k) = 1 → z = 1 := by
  intro k
  induction k with
  | zero => intro h; simpa using h
  | succ k ih =>
    intro h
    apply ih
    apply eq_one_of_centralizes_irreducible hW hL (c := z ^ (2 ^ k))
    · intro l hl
      exact ((Commute.pow_left (hz l hl) (2 ^ k))).eq
    · rw [← pow_add, ← two_mul, ← pow_succ']
      exact h

theorem odd_card_center_of_irreducible {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 2 h2
  have hzz : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  have hz2 : ((z : ↥L) : MulAut W) * ((z : ↥L) : MulAut W) = 1 := by
    have := congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut W)) hzz
    simpa using this
  have hzc : ∀ l ∈ L, ((z : ↥L) : MulAut W) * l = l * ((z : ↥L) : MulAut W) := by
    intro l hl
    have := Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have h1 : ((z : ↥L) : MulAut W) = 1 :=
    eq_one_of_centralizes_irreducible hW hL hzc hz2
  have hz1 : z = 1 := Subtype.ext (Subtype.ext h1)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem le_of_inner_action {G : Type*} [Group G] {L P : Subgroup G}
    (hLz : ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) → x = 1)
    (hC : ∀ z : G, (∀ l ∈ L, z * l = l * z) → ∀ k : ℕ, z ^ (2 ^ k) = 1 → z = 1)
    (hP : ∀ p ∈ P, ∃ k : ℕ, p ^ (2 ^ k) = 1)
    (hinn : ∀ p ∈ P, ∃ l ∈ L, ∀ y ∈ L, p * y * p⁻¹ = l * y * l⁻¹) : P ≤ L := by
  intro p hp
  obtain ⟨l, hl, hinn'⟩ := hinn p hp
  obtain ⟨k, hk⟩ := hP p hp
  set z := l⁻¹ * p with hzdef
  have hzc : ∀ y ∈ L, z * y = y * z := by
    intro y hy
    have h := hinn' y hy
    have h' : p * y = l * y * l⁻¹ * p := by
      calc p * y = (p * y * p⁻¹) * p := by group
        _ = l * y * l⁻¹ * p := by rw [h]
    calc z * y = l⁻¹ * (p * y) := by rw [hzdef, mul_assoc]
      _ = l⁻¹ * (l * y * l⁻¹ * p) := by rw [h']
      _ = y * (l⁻¹ * p) := by group
  have hpz : p = l * z := by rw [hzdef]; group
  have hlz : Commute l z := (hzc l hl).symm
  have hzk : z ^ (2 ^ k) = 1 := by
    have h1 : (l * z) ^ (2 ^ k) = l ^ (2 ^ k) * z ^ (2 ^ k) := hlz.mul_pow _
    rw [hpz, h1] at hk
    have h2 : z ^ (2 ^ k) = (l ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk
    have h3 : z ^ (2 ^ k) ∈ L := by rw [h2]; exact inv_mem (pow_mem hl _)
    apply hLz _ h3
    intro y hy
    exact (Commute.pow_left (hzc y hy) (2 ^ k)).eq
  have hz1 : z = 1 := hC z hzc k hzk
  rw [hpz, hz1, mul_one]
  exact hl

theorem eq_conj_of_congr_eq_conj {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (φ : MulAut G)
    (s : H) (h : MulAut.congr θ φ = MulAut.conj s) :
    ∀ y : G, φ y = θ.symm s * y * (θ.symm s)⁻¹ := by
  intro y
  have h1 := congrArg (fun f : MulAut H => f (θ y)) h
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  apply θ.injective
  rw [h1]
  simp

theorem isPGroup_two_of_mul_self_eq_one {G : Type*} [Group G] (A : Subgroup G)
    (hA : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  refine IsPGroup.iff_orderOf.2 fun a => ?_
  have h2 : (a : G) ^ 2 = 1 := by rw [pow_two]; exact hA a a.2
  have : orderOf (a : G) ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one h2
  obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk'⟩

theorem exists_pow_two_pow_eq_one {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 2 P)
    {p : G} (hp : p ∈ P) : ∃ k : ℕ, p ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨p, hp⟩
  refine ⟨k, ?_⟩
  have h : orderOf p = 2 ^ k := by rw [← hk, Subgroup.orderOf_mk]
  rw [← h]
  exact pow_orderOf_eq_one p

end CFSG.QuasithinUnique.Setup.Family
