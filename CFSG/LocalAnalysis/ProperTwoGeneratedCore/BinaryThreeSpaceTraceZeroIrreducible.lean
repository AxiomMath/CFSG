module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev E13 : Mat3 := Matrix.single 0 2 1

@[expose] def conjLin (g : GL (Fin 3) (ZMod 2)) : Mat3 →ₗ[ZMod 2] Mat3 where
  toFun X := (g : Mat3) * X * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3)
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem conjLin_apply (g : GL (Fin 3) (ZMod 2)) (X : Mat3) :
    conjLin g X = (g : Mat3) * X * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) :=
  rfl

theorem conjLin_one (X : Mat3) : conjLin 1 X = X := by
  rw [conjLin_apply, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem conjLin_mul (g h : GL (Fin 3) (ZMod 2)) (X : Mat3) :
    conjLin (g * h) X = conjLin g (conjLin h X) := by
  simp only [conjLin_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem conjLin_mem (g : GL (Fin 3) (ZMod 2)) {X : Mat3} (hX : X ∈ traceZero) :
    conjLin g X ∈ traceZero := by
  rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at hX ⊢
  rw [conjLin_apply, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]
  exact hX

@[expose] def conjRep : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) traceZero where
  toFun g := (conjLin g).restrict fun _ hX => conjLin_mem g hX
  map_one' := LinearMap.ext fun X => Subtype.ext (conjLin_one X)
  map_mul' g h := LinearMap.ext fun X => Subtype.ext (conjLin_mul g h X)

theorem conjRep_apply (g : GL (Fin 3) (ZMod 2)) (X : traceZero) :
    ((conjRep g X : traceZero) : Mat3) = conjLin g X :=
  rfl

theorem fixed_traceZeroMat : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2,
    (∀ a b c : ZMod 2, unitri a b c * traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 *
      unitri a (a * c + b) c = traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7) →
    traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 = 0 ∨ traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 = E13 := by
  decide +kernel

theorem eq_zero_or_eq_E13 {X : Mat3} (hX : X ∈ traceZero)
    (hfix : ∀ t ∈ sylowT, conjLin t X = X) : X = 0 ∨ X = E13 := by
  rw [eq_traceZeroMat hX] at hfix ⊢
  exact fixed_traceZeroMat _ _ _ _ _ _ _ _ fun a b c => hfix (unitriGL a b c) ⟨a, b, c, rfl⟩

theorem card_sylowT : Nat.card sylowT = 2 ^ 3 := by
  rw [← Nat.card_congr tripleEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

theorem E13_mem {W : Submodule (ZMod 2) Mat3} (hWA : W ≤ traceZero) (hW : W ≠ ⊥)
    (hinv : ∀ t ∈ sylowT, ∀ X ∈ W, conjLin t X ∈ W) : E13 ∈ W := by
  let _ : MulAction sylowT W :=
    { smul := fun t X => ⟨conjLin t X, hinv t t.2 X X.2⟩
      one_smul := fun X => Subtype.ext (conjLin_one X)
      mul_smul := fun s t X => Subtype.ext (conjLin_mul s t X) }
  have hT : IsPGroup 2 sylowT := IsPGroup.of_card card_sylowT
  have hcard : 2 ∣ Nat.card W := by
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    exact dvd_pow_self 2 (Submodule.finrank_eq_zero.not.mpr hW)
  have h0 : (0 : W) ∈ MulAction.fixedPoints sylowT W := fun t =>
    Subtype.ext (by change conjLin t 0 = 0; rw [map_zero])
  obtain ⟨X, hXfix, hX0⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard h0
  rcases eq_zero_or_eq_E13 (hWA X.2) fun t ht =>
      congrArg Subtype.val (hXfix ⟨t, ht⟩) with h | h
  · exact absurd (Subtype.ext h.symm) hX0
  · exact h ▸ X.2

@[expose] def swap13 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩

theorem conjLin_swap13_E13 : conjLin swap13 E13 = E31 := by decide

theorem trace_zero_irreducibility :
    Module.finrank (ZMod 2) traceZero = 8 ∧
    (∀ g : GL (Fin 3) (ZMod 2), ∀ X ∈ traceZero,
      (g : Mat3) * X * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) ∈ traceZero) ∧
    ∀ W : Submodule (ZMod 2) Mat3, W ≤ traceZero →
      (∀ g : GL (Fin 3) (ZMod 2), ∀ X ∈ W,
        (g : Mat3) * X * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) ∈ W) →
      W = ⊥ ∨ W = traceZero := by
  refine ⟨?_, fun g X hX => conjLin_mem g hX, fun W hWA hinv => ?_⟩
  · rw [Module.finrank_eq_card_basis conjBasis, ← Nat.card_eq_fintype_card, card_sylowT]
    norm_num
  · by_cases hW : W = ⊥
    · exact Or.inl hW
    refine Or.inr (le_antisymm hWA ?_)
    have hE13 : E13 ∈ W := E13_mem hWA hW fun t _ X hX => hinv t X hX
    have hE31 : E31 ∈ W := conjLin_swap13_E13 ▸ hinv swap13 E13 hE13
    intro X hX
    have hspan := span_conjFamily (Submodule.mem_top (x := (⟨X, hX⟩ : traceZero)))
    have hle : Submodule.span (ZMod 2) (Set.range conjFamily) ≤ W.comap traceZero.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact hinv t E31 hE31
    exact hle hspan

theorem conjRep_isIrreducible : conjRep.IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, fun h => by
    have hE31A : E31 ∈ traceZero := by
      rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
      decide
    have hmem : (⟨E31, hE31A⟩ : traceZero) ∈ (⊤ : Subrepresentation conjRep) :=
      Submodule.mem_top
    rw [← h] at hmem
    have h0 : (⟨E31, hE31A⟩ : traceZero) = 0 := (Submodule.mem_bot (ZMod 2)).mp hmem
    have hne : E31 ≠ 0 := by decide
    exact hne (congrArg Subtype.val h0)⟩
  eq_bot_or_eq_top ρ' := by
    rcases (trace_zero_irreducibility.2.2 (ρ'.toSubmodule.map traceZero.subtype)
        (Submodule.map_subtype_le _ _) fun g X hX => by
          obtain ⟨Y, hY, rfl⟩ := hX
          exact ⟨conjRep g Y, ρ'.apply_mem_toSubmodule g hY, rfl⟩) with h | h
    · left
      refine Subrepresentation.toSubmodule_injective ?_
      exact Submodule.map_injective_of_injective traceZero.injective_subtype
        (h.trans (Submodule.map_bot _).symm)
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.mpr fun X _ => ?_)
      have hX : (X : Mat3) ∈ ρ'.toSubmodule.map traceZero.subtype := by
        rw [h]
        exact X.2
      obtain ⟨Y, hY, hYX⟩ := hX
      exact (Subtype.ext hYX : Y = X) ▸ hY

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
