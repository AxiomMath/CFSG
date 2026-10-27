module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.OddSolvableUnitary

open Subgroup
open scoped commutatorElement

variable {D : Type*} [Group D]

section Pairing

variable (hZ : center D = commutator D)
include hZ

theorem commutatorElement_mem_center (x y : D) : ⁅x, y⁆ ∈ center D := by
  rw [hZ, _root_.commutator_def]
  exact commutator_mem_commutator (mem_top x) (mem_top y)

theorem commutatorElement_mul_left_of_center (x x' y : D) :
    ⁅x * x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ := by
  have h := mem_center_iff.1 (commutatorElement_mem_center hZ x' y) x
  simp only [commutatorElement_def] at h ⊢
  calc x * x' * y * (x * x')⁻¹ * y⁻¹ = x * (x' * y * x'⁻¹ * y⁻¹) * y * x⁻¹ * y⁻¹ := by group
    _ = x' * y * x'⁻¹ * y⁻¹ * x * y * x⁻¹ * y⁻¹ := by rw [h]
    _ = x' * y * x'⁻¹ * y⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group

theorem commutatorElement_mul_right_of_center (x y y' : D) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h := mem_center_iff.1 (commutatorElement_mem_center hZ x y') y
  simp only [commutatorElement_def] at h ⊢
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * y⁻¹ * (y * (x * y' * x⁻¹ * y'⁻¹)) * y⁻¹ := by
        group
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹ * y) * y⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ * (x * y' * x⁻¹ * y'⁻¹) := by group

variable {r : ℕ} (ε : center D ≃* Multiplicative (ZMod r))

@[expose] def commRight (x : D) : D →* Multiplicative (ZMod r) where
  toFun y := ε ⟨⁅x, y⁆, commutatorElement_mem_center hZ x y⟩
  map_one' := by
    rw [← map_one ε]
    exact congrArg ε (Subtype.ext (commutatorElement_one_right x))
  map_mul' y y' := by
    rw [← map_mul]
    exact congrArg ε (Subtype.ext (commutatorElement_mul_right_of_center hZ x y y'))

theorem commRight_apply (x y : D) :
    commRight hZ ε x y = ε ⟨⁅x, y⁆, commutatorElement_mem_center hZ x y⟩ :=
  rfl

@[expose] def commPairing : Abelianization D →* Abelianization D →* Multiplicative (ZMod r) :=
  Abelianization.lift
    { toFun := fun x => Abelianization.lift (commRight hZ ε x)
      map_one' := by
        refine Abelianization.hom_ext _ _ (MonoidHom.ext fun y => ?_)
        simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of, commRight_apply,
          MonoidHom.one_apply]
        rw [← map_one ε]
        exact congrArg ε (Subtype.ext (commutatorElement_one_left y))
      map_mul' := fun x x' => by
        refine Abelianization.hom_ext _ _ (MonoidHom.ext fun y => ?_)
        simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of, commRight_apply,
          MonoidHom.mul_apply]
        rw [mul_comm, ← map_mul]
        exact congrArg ε (Subtype.ext (commutatorElement_mul_left_of_center hZ x x' y)) }

theorem commPairing_of (x y : D) :
    commPairing hZ ε (Abelianization.of x) (Abelianization.of y) =
      ε ⟨⁅x, y⁆, commutatorElement_mem_center hZ x y⟩ :=
  rfl

end Pairing

theorem nsmul_abelianization_eq_zero {r : ℕ} (hD : ∀ x : D, x ^ r = 1)
    (v : Additive (Abelianization D)) : r • v = 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
  induction u using QuotientGroup.induction_on with
  | H x =>
    change r • Additive.ofMul (Abelianization.of x) = 0
    rw [← ofMul_pow, ← map_pow, hD, map_one]
    rfl

theorem exists_commForm {r : ℕ} [Module (ZMod r) (Additive (Abelianization D))]
    (hZ : center D = commutator D) (ε : center D ≃* Multiplicative (ZMod r)) :
    ∃ B : LinearMap.BilinForm (ZMod r) (Additive (Abelianization D)),
      LinearMap.BilinForm.IsAlt B ∧ LinearMap.BilinForm.Nondegenerate B ∧ ∀ x y : D,
        B (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)) =
          Multiplicative.toAdd (ε ⟨⁅x, y⁆, commutatorElement_mem_center hZ x y⟩) := by
  let β : Additive (Abelianization D) →+ Additive (Abelianization D) →+ ZMod r :=
    { toFun := fun u =>
        { toFun := fun v => Multiplicative.toAdd
            (commPairing hZ ε (Additive.toMul u) (Additive.toMul v))
          map_zero' := by
            change Multiplicative.toAdd (commPairing hZ ε (Additive.toMul u) 1) = 0
            rw [map_one, toAdd_one]
          map_add' := fun v v' => by
            change Multiplicative.toAdd (commPairing hZ ε (Additive.toMul u)
              (Additive.toMul v * Additive.toMul v')) = _
            rw [map_mul, toAdd_mul] }
      map_zero' := by
        refine AddMonoidHom.ext fun v => ?_
        change Multiplicative.toAdd (commPairing hZ ε 1 (Additive.toMul v)) = 0
        rw [map_one, MonoidHom.one_apply, toAdd_one]
      map_add' := fun u u' => by
        refine AddMonoidHom.ext fun v => ?_
        change Multiplicative.toAdd (commPairing hZ ε (Additive.toMul u * Additive.toMul u')
          (Additive.toMul v)) = _
        rw [map_mul, MonoidHom.mul_apply, toAdd_mul]
        rfl }
  let B : LinearMap.BilinForm (ZMod r) (Additive (Abelianization D)) :=
    AddMonoidHom.toZModLinearMap r
      { toFun := fun u => AddMonoidHom.toZModLinearMap r (β u)
        map_zero' := by ext v; simp
        map_add' := fun u u' => by ext v; simp }
  have hB : ∀ x y : D, B (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) =
        Multiplicative.toAdd (ε ⟨⁅x, y⁆, commutatorElement_mem_center hZ x y⟩) := fun x y => rfl
  have hof : ∀ v : Additive (Abelianization D), ∃ x : D,
      Additive.ofMul (Abelianization.of x) = v := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, hx⟩
  have hzero : ∀ x : D, Additive.ofMul (Abelianization.of x) = 0 ↔ x ∈ center D := by
    intro x
    rw [hZ, ← Abelianization.ker_of, MonoidHom.mem_ker]
    exact Additive.ofMul.injective.eq_iff' rfl
  have hval : ∀ x y : D, B (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = 0 ↔ ⁅x, y⁆ = 1 := by
    intro x y
    rw [hB, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε,
      ε.injective.eq_iff, Subtype.ext_iff, OneMemClass.coe_one]
  refine ⟨B, fun u => ?_, ⟨fun u hu => ?_, fun v hv => ?_⟩, hB⟩
  · obtain ⟨x, rfl⟩ := hof u
    exact (hval x x).2 (commutatorElement_self x)
  · obtain ⟨x, rfl⟩ := hof u
    refine (hzero x).2 (mem_center_iff.2 fun y => ?_)
    exact (commutatorElement_eq_one_iff_mul_comm.1 ((hval x y).1 (hu _))).symm
  · obtain ⟨y, rfl⟩ := hof v
    refine (hzero y).2 (mem_center_iff.2 fun x => ?_)
    exact commutatorElement_eq_one_iff_mul_comm.1 ((hval x y).1 (hv _))

theorem nonempty_center_mulEquiv {r : ℕ} [Fact r.Prime] (hc : Nat.card (center D) = r) :
    Nonempty (center D ≃* Multiplicative (ZMod r)) := by
  have := isCyclic_of_prime_card hc
  exact ⟨(zmodCyclicMulEquiv this).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hc).toAddEquiv)⟩

theorem card_eq_card_abelianization_mul {r : ℕ} (hZ : center D = commutator D)
    (hc : Nat.card (center D) = r) : Nat.card D = Nat.card (Abelianization D) * r := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator D), ← hc, hZ]
  rfl

theorem card_abelianization_eq_pow [Finite D] {r : ℕ} [Fact r.Prime] (hD : ∀ x : D, x ^ r = 1)
    (hZ : center D = commutator D) (hc : Nat.card (center D) = r) :
    ∃ a : ℕ, Nat.card (Abelianization D) = r ^ (2 * a) := by
  obtain ⟨ε⟩ := nonempty_center_mulEquiv hc
  have := AddCommGroup.zmodModule (nsmul_abelianization_eq_zero hD)
  obtain ⟨B, hBa, hBn, -⟩ := exists_commForm hZ ε
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod r) (Additive (Abelianization D)) := Module.Finite.of_finite
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod r) hBa hBn
  refine ⟨a, ?_⟩
  change Nat.card (Additive (Abelianization D)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod, ha, two_mul]

theorem card_eq_pow_one_add_two_mul [Finite D] {r : ℕ} [Fact r.Prime] (hD : ∀ x : D, x ^ r = 1)
    (hZ : center D = commutator D) (hc : Nat.card (center D) = r) :
    ∃ a : ℕ, Nat.card D = r ^ (1 + 2 * a) ∧ (¬IsMulCommutative D → 1 ≤ a) := by
  obtain ⟨a, ha⟩ := card_abelianization_eq_pow hD hZ hc
  have hD' : Nat.card D = r ^ (1 + 2 * a) := by
    rw [card_eq_card_abelianization_mul hZ hc, ha, pow_add, pow_one, mul_comm]
  refine ⟨a, hD', fun hnc => Nat.one_le_iff_ne_zero.2 fun h0 => hnc ?_⟩
  rw [h0, mul_zero, add_zero, pow_one, ← hc] at hD'
  have htop : center D = ⊤ := Subgroup.eq_top_of_card_eq _ hD'.symm
  exact ⟨⟨fun x y => (mem_center_iff.1 (htop ▸ mem_top y) x)⟩⟩

theorem exists_symplectic_lifts [Finite D] {r a : ℕ} [Fact r.Prime] (hD : ∀ x : D, x ^ r = 1)
    (hZ : center D = commutator D) (hc : Nat.card (center D) = r)
    (hcard : Nat.card D = r ^ (1 + 2 * a)) :
    ∃ b c : Fin a → D, (∀ i j, ⁅b i, b j⁆ = 1) ∧ (∀ i j, i ≠ j → ⁅c i, b j⁆ = 1) ∧
      ∀ i, ⁅c i, b i⁆ ≠ 1 := by
  obtain ⟨ε⟩ := nonempty_center_mulEquiv hc
  have := AddCommGroup.zmodModule (nsmul_abelianization_eq_zero hD)
  obtain ⟨B, hBa, hBn, hB⟩ := exists_commForm hZ ε
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod r) (Additive (Abelianization D)) := Module.Finite.of_finite
  obtain ⟨m, bs, hbs⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (K := ZMod r) hBa hBn
  have hr : 2 ≤ r := (Fact.out : r.Prime).two_le
  have hm : m = a := by
    have h1 : Nat.card (Additive (Abelianization D)) = r ^ (2 * m) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod,
        Module.finrank_eq_card_basis bs, Fintype.card_sum, Fintype.card_fin, two_mul]
    have h2 := card_eq_card_abelianization_mul hZ hc
    change Nat.card (Abelianization D) = _ at h1
    rw [h1, hcard, ← pow_succ, add_comm] at h2
    have := Nat.pow_right_injective hr h2
    omega
  subst hm
  have hof : ∀ v : Additive (Abelianization D), ∃ x : D,
      Additive.ofMul (Abelianization.of x) = v := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, hx⟩
  choose lift hlift using hof
  have hval : ∀ x y : D, ⁅x, y⁆ = 1 ↔ B (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = 0 := by
    intro x y
    rw [hB, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε,
      ε.injective.eq_iff, Subtype.ext_iff, OneMemClass.coe_one]
  have hJ : ∀ u v, B (bs u) (bs v) = Matrix.J (Fin m) (ZMod r) u v := fun u v => by
    rw [← hbs, LinearMap.BilinForm.toMatrix_apply]
  refine ⟨fun i => lift (bs (Sum.inl i)), fun i => lift (bs (Sum.inr i)), fun i j => ?_,
    fun i j hij => ?_, fun i => ?_⟩
  · rw [hval, hlift, hlift, hJ]
    simp [Matrix.J]
  · rw [hval, hlift, hlift, hJ]
    simp [Matrix.J, hij]
  · rw [Ne, hval, hlift, hlift, hJ]
    simp [Matrix.J]

end CFSG.OddSolvableUnitary
