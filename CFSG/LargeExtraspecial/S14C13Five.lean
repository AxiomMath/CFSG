module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.S14

open Module

theorem eq_or_fixfree_of_pow_five {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hW : Nat.card W = 16) {f : W ≃ₗ[ZMod 2] W} (hf : f ^ 5 = 1) :
    (∀ w, f w = w) ∨ ∀ w, f w = w → w = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hf) with h1 | h5
  · left
    intro w
    rw [orderOf_eq_one_iff.mp h1]
    rfl
  have hG : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h5, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints W
  set K : Submodule (ZMod 2) W := LinearMap.ker ((f : W →ₗ[ZMod 2] W) - LinearMap.id)
  have hfix : ∀ w, w ∈ MulAction.fixedPoints (Subgroup.zpowers f) W ↔ w ∈ K := by
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    constructor
    · intro h
      exact h ⟨f, Subgroup.mem_zpowers f⟩
    · intro h g
      have hs : f ∈ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) w := h
      exact (Subgroup.zpowers_le.mpr hs) g.2
  have hK : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) W) = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight hfix)
  have hcW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  have hcK := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [Nat.card_zmod] at hcW hcK
  have hd4 : finrank (ZMod 2) W = 4 := by
    exact Nat.pow_right_injective le_rfl (hcW.symm.trans (hW.trans (by norm_num)))
  have hdK : finrank (ZMod 2) K ≤ 4 := hd4 ▸ Submodule.finrank_le K
  rw [hK, hcK, hW] at hmod
  generalize hd : finrank (ZMod 2) K = d at hmod hdK
  interval_cases d <;> norm_num [Nat.ModEq] at hmod
  · right
    intro w hw
    have hK0 : K = ⊥ := Submodule.finrank_eq_zero.mp hd
    have : w ∈ K := (hfix w).mp fun g => by
      have hs : f ∈ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) w := hw
      exact (Subgroup.zpowers_le.mpr hs) g.2
    rw [hK0] at this
    exact (Submodule.mem_bot _).mp this
  · left
    intro w
    have hKt : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hd, hd4])
    have : w ∈ K := hKt ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at this
    exact this

theorem eq_or_fixfree_on {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {A : Submodule (ZMod 2) M} [Finite A] (hA : Nat.card A = 16) {f : M ≃ₗ[ZMod 2] M}
    (hf : f ^ 5 = 1) (hfA : ∀ v ∈ A, f v ∈ A) :
    (∀ w ∈ A, f w = w) ∨ ∀ w ∈ A, f w = w → w = 0 := by
  let fA : A →ₗ[ZMod 2] A := (f : M →ₗ[ZMod 2] M).restrict hfA
  have hinj : Function.Injective fA := fun a b h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
  let eA : A ≃ₗ[ZMod 2] A := LinearEquiv.ofBijective fA
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hpow : ∀ (k : ℕ) (a : A), ((eA ^ k) a : M) = (f ^ k) (a : M) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [pow_succ', LinearEquiv.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have he5 : eA ^ 5 = 1 := LinearEquiv.ext fun a => Subtype.ext (by rw [hpow, hf]; rfl)
  rcases eq_or_fixfree_of_pow_five hA he5 with h | h
  · exact Or.inl fun w hw => congrArg Subtype.val (h ⟨w, hw⟩)
  · exact Or.inr fun w hw hfw => congrArg Subtype.val (h ⟨w, hw⟩ (Subtype.ext hfw))

theorem fixfree_of_swap {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (hM : Nat.card M = 256) {A B : Submodule (ZMod 2) M} (hAB : IsCompl A B)
    {f h : M ≃ₗ[ZMod 2] M} (hf5 : f ^ 5 = 1) (hfA : ∀ v ∈ A, f v ∈ A) (hfB : ∀ v ∈ B, f v ∈ B)
    (hhA : ∀ v ∈ A, h v ∈ B) (hhB : ∀ v ∈ B, h v ∈ A) (hfh : ∀ v, f (h v) = h (f v))
    (hf1 : ∃ v, f v ≠ v) : ∀ w, f w = w → w = 0 := by
  have hcAB : Nat.card A = Nat.card B := le_antisymm
    (Nat.card_le_card_of_injective (fun a : A => (⟨h a, hhA a a.2⟩ : B))
      fun a b e => Subtype.ext (h.injective (congrArg Subtype.val e)))
    (Nat.card_le_card_of_injective (fun b : B => (⟨h b, hhB b b.2⟩ : A))
      fun a b e => Subtype.ext (h.injective (congrArg Subtype.val e)))
  have hprod : Nat.card A * Nat.card B = 256 := by
    rw [← hM, ← Nat.card_prod]
    exact Nat.card_congr (Submodule.prodEquivOfIsCompl A B hAB).toEquiv
  have hA : Nat.card A = 16 := by
    rw [← hcAB] at hprod
    generalize Nat.card A = k at hprod ⊢
    have hk : k ≤ 16 := by nlinarith
    interval_cases k <;> omega
  have hdecomp : ∀ w : M, ∃ a ∈ A, ∃ b ∈ B, w = a + b := fun w => by
    have hw : w ∈ A ⊔ B := hAB.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    exact ⟨a, ha, b, hb, rfl⟩
  have huniq : ∀ a ∈ A, ∀ b ∈ B, a + b = 0 → a = 0 := fun a ha b hb e => by
    have hb' : a = -b := eq_neg_of_add_eq_zero_left e
    have : a ∈ A ⊓ B := ⟨ha, hb' ▸ B.neg_mem hb⟩
    rw [hAB.inf_eq_bot] at this
    exact (Submodule.mem_bot _).mp this
  have hBfix : ∀ b ∈ B, (∀ w ∈ A, f w = w → w = 0) → f b = b → b = 0 := fun b hb hfr hfb => by
    have h1 : f (h b) = h b := by rw [hfh, hfb]
    have h2 := hfr _ (hhB b hb) h1
    exact h.injective (h2.trans (map_zero h).symm)
  rcases eq_or_fixfree_on hA hf5 hfA with hid | hfree
  · exfalso
    obtain ⟨v, hv⟩ := hf1
    apply hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp v
    have hbB : f b = b := by
      have h1 := hid (h b) (hhB b hb)
      rw [hfh] at h1
      exact h.injective h1
    rw [map_add, hid a ha, hbB]
  · intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecomp w
    have hsum : (f a - a) + (f b - b) = 0 := by
      rw [map_add] at hw
      rw [sub_add_sub_comm, hw, sub_self]
    have ha0 : f a - a = 0 := huniq _ (A.sub_mem (hfA a ha) ha) _ (B.sub_mem (hfB b hb) hb) hsum
    have hb0 : f b - b = 0 := by rwa [ha0, zero_add] at hsum
    rw [hfree a ha (sub_eq_zero.mp ha0), hBfix b hb hfree (sub_eq_zero.mp hb0), add_zero]

end CFSG.LargeExtraspecial.S14
