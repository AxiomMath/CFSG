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

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u v

theorem all_fibers_card_eq_of_card_eq_mul
    {A : Type u} {B : Type v} [Finite A] [Finite B]
    (f : A → B) (m : ℕ)
    (hbound : ∀ b : B, Nat.card {a : A // f a = b} ≤ m)
    (htotal : Nat.card A = Nat.card B * m) :
    ∀ b : B, Nat.card {a : A // f a = b} = m := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have hsum : (∑ b : B, Nat.card {a : A // f a = b}) = ∑ _b : B, m := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f), htotal]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  intro b
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hbound b)).mp hsum b (Finset.mem_univ b)

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]

theorem involution_flips_pair {a b : Ω} {t : G}
    (ht : orderOf t = 2) (himage : t • a = b) : t • b = a := by
  have hsquare := pow_orderOf_eq_one t
  rw [ht, pow_two] at hsquare
  rw [← himage, ← mul_smul, hsquare, one_smul]

theorem flip_product_mem_two_point_stabilizer {a b : Ω} {t s : G}
    (ht : orderOf t = 2) (hs : orderOf s = 2)
    (htimage : t • a = b) (hsimage : s • a = b) :
    t * s ∈ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
  constructor
  · change (t * s) • a = a
    rw [mul_smul, hsimage, involution_flips_pair ht htimage]
  · change (t * s) • b = b
    rw [mul_smul, involution_flips_pair hs hsimage, htimage]

@[expose] def conjugacyWithin (H : Subgroup G) (z : G) : Set G :=
  {x | ∃ h : H, (h : G)⁻¹ * z * h = x}

theorem right_conjugates_eq_iff {z a b : G} :
    a⁻¹ * z * a = b⁻¹ * z * b ↔
      a * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  constructor
  · intro h
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h' := congrArg (fun x : G => a * x * b⁻¹) h
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel, mul_one] using h'.symm
  · intro h
    have h' := congrArg (fun x : G => a⁻¹ * x * b)
      (Subgroup.mem_centralizer_singleton_iff.mp h)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using h'.symm

theorem flip_representatives_difference {z t s t₀ : G}
    (hs : orderOf s = 2) :
    (t * t₀)⁻¹ * z * (t * t₀) = (s * t₀)⁻¹ * z * (s * t₀) ↔
      t * s ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [right_conjugates_eq_iff, mul_inv_rev,
    inv_eq_self_of_orderOf_eq_two hs]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem conjugacy_class_card_mul_centralizer [Finite G] (z : G) :
    Nat.card (conjugatesOf z) * Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card G := by
  have horbit : MulAction.orbit (ConjAct G) z = conjugatesOf z := by
    ext x
    exact ConjAct.mem_orbit_conjAct.trans ⟨IsConj.symm, IsConj.symm⟩
  have hcard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) z)
  rw [Nat.card_prod, horbit,
    ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at hcard
  exact hcard

def conjugacyWithinEquiv (H : Subgroup G) (z : H) :
    conjugatesOf z ≃ conjugacyWithin H (z : G) :=
  Equiv.ofBijective (fun x => ⟨(x : H), by
    obtain ⟨h, hh⟩ := isConj_iff.mp x.property
    exact ⟨h⁻¹, by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      using congrArg Subtype.val hh⟩⟩) (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : conjugacyWithin H (z : G) => (x : G)) h
      · rintro ⟨x, h, hx⟩
        let y : H := ⟨x, hx ▸ H.mul_mem (H.mul_mem (H.inv_mem h.property) z.property)
          h.property⟩
        refine ⟨⟨y, isConj_iff.mpr ⟨h⁻¹, ?_⟩⟩, rfl⟩
        exact Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
          y] using hx))

@[expose] def flipFiber (z : G) (a b : Ω) : Set G :=
  {t | IsConj z t ∧ t • a = b}

theorem flip_fiber_class_map_injective (a b : Ω) (z : G)
    (hz : orderOf z = 2) (hba : b ≠ a)
    (hconfine : ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G a ∧ s ∈ MulAction.stabilizer G a)
    (t₀ : G) :
    Function.Injective (fun t : flipFiber z a b =>
      (t.val * t₀)⁻¹ * z * (t.val * t₀)) := by
  intro t s hsame
  have hsorder : orderOf (s : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp s.property.1
    rw [← hg]
    exact (MulAut.conj g).orderOf_eq z |>.trans hz
  have hproduct := (flip_representatives_difference hsorder).mp hsame
  by_contra hne
  have htsne : (t : G) * s ≠ 1 := by
    intro hone
    have heq : (t : G) = (s : G) := by
      have h := mul_eq_one_iff_eq_inv.mp hone
      rwa [inv_eq_self_of_orderOf_eq_two hsorder] at h
    exact hne (Subtype.ext heq)
  have htfix := (hconfine t s t.property.1 s.property.1 htsne hproduct).1
  exact hba (t.property.2.symm.trans (MulAction.mem_stabilizer_iff.mp htfix))

theorem flip_fiber_card_le [Finite G] (a b : Ω) (z : G)
    (hz : orderOf z = 2) (hba : b ≠ a)
    (hconfine : ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G a ∧ s ∈ MulAction.stabilizer G a) :
    Nat.card (flipFiber z a b) ≤ Nat.card (conjugacyWithin (MulAction.stabilizer G a) z) := by
  classical
  by_cases hnonempty : (flipFiber z a b).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hnonempty
    have ht₀order : orderOf t₀ = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp ht₀.1
      rw [← hg]
      exact (MulAut.conj g).orderOf_eq z |>.trans hz
    let f : flipFiber z a b → conjugacyWithin (MulAction.stabilizer G a) z :=
      fun t => ⟨(t.val * t₀)⁻¹ * z * (t.val * t₀), ⟨⟨t.val * t₀,
        (flip_product_mem_two_point_stabilizer
          (by obtain ⟨g, hg⟩ := isConj_iff.mp t.property.1; rw [← hg];
              exact (MulAut.conj g).orderOf_eq z |>.trans hz)
          ht₀order t.property.2 ht₀.2).1⟩, rfl⟩⟩
    exact Nat.card_le_card_of_injective f (fun t s h =>
      flip_fiber_class_map_injective a b z hz hba hconfine t₀
        (congrArg Subtype.val h))
  · have hEmpty : flipFiber z a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hEmpty]
    simp

theorem class_card_eq_sum_flip_fibers [Finite G] [Fintype Ω] (a : Ω) (z : G) :
    Nat.card (conjugatesOf z) = ∑ b : Ω, Nat.card (flipFiber z a b) := by
  classical
  let f : conjugatesOf z → Ω := fun t => (t : G) • a
  have hequiv (b : Ω) : {t : conjugatesOf z // f t = b} ≃ flipFiber z a b :=
    { toFun := fun t => ⟨t.val.val, t.val.property, t.property⟩
      invFun := fun t => ⟨⟨t.val, t.property.1⟩, t.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card (conjugatesOf z) = Nat.card (Σ b : Ω, {t : conjugatesOf z // f t = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : Ω, Nat.card {t : conjugatesOf z // f t = b} := Nat.card_sigma
    _ = ∑ b : Ω, Nat.card (flipFiber z a b) :=
      Finset.sum_congr rfl (fun b _ => Nat.card_congr (hequiv b))

theorem uniform_flip_fiber_cards [Finite G] [Finite Ω] (a : Ω) (z : G)
    (hz : orderOf z = 2)
    (hconfine : ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G a ∧ s ∈ MulAction.stabilizer G a)
    (hfixed : Nat.card (flipFiber z a a) =
      Nat.card (conjugacyWithin (MulAction.stabilizer G a) z))
    (hclass : Nat.card (conjugatesOf z) = Nat.card Ω *
      Nat.card (conjugacyWithin (MulAction.stabilizer G a) z)) :
    ∀ b : Ω, Nat.card (flipFiber z a b) =
      Nat.card (conjugacyWithin (MulAction.stabilizer G a) z) := by
  classical
  let := Fintype.ofFinite Ω
  let m := Nat.card (conjugacyWithin (MulAction.stabilizer G a) z)
  have hbound : ∀ b : Ω, Nat.card (flipFiber z a b) ≤ m := by
    intro b
    by_cases hba : b = a
    · subst b
      exact hfixed.le
    · exact flip_fiber_card_le a b z hz hba hconfine
  have hsum : (∑ b : Ω, Nat.card (flipFiber z a b)) = ∑ _b : Ω, m := by
    rw [← class_card_eq_sum_flip_fibers a z, hclass]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, m]
  intro b
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => hbound b)).mp hsum b (Finset.mem_univ b)

theorem flip_products_class_map_bijective [Finite G]
    (a b : Ω) (z : G) (hz : orderOf z = 2) (hba : b ≠ a)
    (hconfine : ∀ t s : G, IsConj z t → IsConj z s → t * s ≠ 1 →
      t * s ∈ Subgroup.centralizer ({z} : Set G) →
        t ∈ MulAction.stabilizer G a ∧ s ∈ MulAction.stabilizer G a)
    (hcard : Nat.card (flipFiber z a b) =
      Nat.card (conjugacyWithin (MulAction.stabilizer G a) z))
    (t₀ : G) (ht₀ : t₀ ∈ flipFiber z a b) :
    ∀ h : MulAction.stabilizer G a, ∃! t : flipFiber z a b,
      t.val * t₀ * (h : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  classical
  have ht₀order : orderOf t₀ = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ht₀.1
    rw [← hg]
    exact (MulAut.conj g).orderOf_eq z |>.trans hz
  let f : flipFiber z a b → conjugacyWithin (MulAction.stabilizer G a) z :=
    fun t => ⟨(t.val * t₀)⁻¹ * z * (t.val * t₀), ⟨⟨t.val * t₀,
      (flip_product_mem_two_point_stabilizer
        (by obtain ⟨g, hg⟩ := isConj_iff.mp t.property.1; rw [← hg];
            exact (MulAut.conj g).orderOf_eq z |>.trans hz)
        ht₀order t.property.2 ht₀.2).1⟩, rfl⟩⟩
  have hinj : Function.Injective f := fun t s h =>
    flip_fiber_class_map_injective a b z hz hba hconfine t₀ (congrArg Subtype.val h)
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  intro h
  obtain ⟨t, ht⟩ := hbij.2 ⟨(h : G)⁻¹ * z * h, ⟨h, rfl⟩⟩
  refine ⟨t, (right_conjugates_eq_iff).mp (congrArg Subtype.val ht), ?_⟩
  intro s hs
  apply hinj
  apply Subtype.ext
  exact ((right_conjugates_eq_iff).mpr hs).trans (congrArg Subtype.val ht).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
