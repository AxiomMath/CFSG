module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModulesModels
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem flagAct_one (pf : Flags V) : flagAct 1 pf = pf :=
  rfl

theorem flagAct_mul (g h : V ≃ₗ[ZMod 2] V) (pf : Flags V) :
    flagAct (g * h) pf = flagAct g (flagAct h pf) :=
  rfl

variable (V) in
@[expose, instance_reducible] def flagMulAction : MulAction (V ≃ₗ[ZMod 2] V) (Flags V) where
  smul := flagAct
  one_smul := flagAct_one
  mul_smul := flagAct_mul

@[expose] def flagStab (pf : Flags V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  letI := flagMulAction V
  MulAction.stabilizer (V ≃ₗ[ZMod 2] V) pf

theorem mem_flagStab {pf : Flags V} {g : V ≃ₗ[ZMod 2] V} : g ∈ flagStab pf ↔ flagAct g pf = pf :=
  Iff.rfl

theorem exists_flagAct_eq [Fintype V] (hV : finrank (ZMod 2) V = 3) (pf pf' : Flags V) :
    ∃ g : V ≃ₗ[ZMod 2] V, flagAct g pf = pf' := by
  obtain ⟨g, hp, hf⟩ := exists_flag_eq hV pf.1.1.2 pf'.1.1.2 pf.1.2.2 pf'.1.2.2 pf.2 pf'.2
  refine ⟨g, Subtype.ext (Prod.ext (Subtype.ext hp) (Subtype.ext (LinearMap.ext fun v => ?_)))⟩
  change (pf.1.2 : Module.Dual (ZMod 2) V) (g.symm v) = (pf'.1.2 : Module.Dual (ZMod 2) V) v
  rw [← hf, LinearMap.comp_apply, LinearEquiv.coe_coe, g.apply_symm_apply]

theorem natCard_linearEquiv (hV : finrank (ZMod 2) V = 3) : Nat.card (V ≃ₗ[ZMod 2] V) = 168 := by
  have := Module.finite_of_finrank_eq_succ hV
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let e : (V ≃ₗ[ZMod 2] V) ≃ GL (Fin 3) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.toEquiv.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv).toEquiv
  rw [Nat.card_congr e, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  rfl

variable [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)]

theorem natCard_flagStab (hV : finrank (ZMod 2) V = 3) (pf : Flags V) :
    Nat.card (flagStab pf) = 2 ^ 3 := by
  let _ := flagMulAction V
  have : MulAction.IsPretransitive (V ≃ₗ[ZMod 2] V) (Flags V) :=
    ⟨fun x y => exists_flagAct_eq hV x y⟩
  have h := (flagStab pf).card_mul_index
  rw [flagStab, MulAction.index_stabilizer_of_transitive, natCard_linearEquiv hV,
    Nat.card_eq_fintype_card (α := Flags V), card_flags hV] at h
  change Nat.card (MulAction.stabilizer (V ≃ₗ[ZMod 2] V) pf) = 2 ^ 3
  omega

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
  (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E)

theorem exists_fixed_ne_zero [Nontrivial E] (hV : finrank (ZMod 2) V = 3) (pf : Flags V) :
    ∃ e : E, e ≠ 0 ∧ ∀ g ∈ flagStab pf, ρ g e = e := by
  let _ : MulAction (flagStab pf) E :=
    { smul := fun t e => ρ t e
      one_smul := fun e => by
        change ρ 1 e = e
        rw [map_one, Module.End.one_apply]
      mul_smul := fun s t e => by
        change ρ ((s : V ≃ₗ[ZMod 2] V) * t) e = ρ s (ρ t e)
        rw [map_mul, Module.End.mul_apply] }
  have hT : IsPGroup 2 (flagStab pf) := IsPGroup.of_card (natCard_flagStab hV pf)
  have hcard : 2 ∣ Nat.card E := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 E]
    have : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := E)).ne'
  have h0 : (0 : E) ∈ MulAction.fixedPoints (flagStab pf) E := fun t => map_zero (ρ t)
  obtain ⟨e, he, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hcard h0
  exact ⟨e, hne.symm, fun g hg => he ⟨g, hg⟩⟩

omit [Fintype V] [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)]
  [DecidableEq (Module.Dual (ZMod 2) V)] [Finite E] in
theorem apply_eq_of_flagAct_eq {pf₀ : Flags V} {e : E} (he : ∀ g ∈ flagStab pf₀, ρ g e = e)
    {g g' : V ≃ₗ[ZMod 2] V} (h : flagAct g pf₀ = flagAct g' pf₀) : ρ g e = ρ g' e := by
  have ht : g⁻¹ * g' ∈ flagStab pf₀ := by
    rw [mem_flagStab, flagAct_mul, ← h, ← flagAct_mul, inv_mul_cancel, flagAct_one]
  calc ρ g e = ρ g (ρ (g⁻¹ * g') e) := by rw [he _ ht]
    _ = ρ g' e := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

@[expose] def flagElt (hV : finrank (ZMod 2) V = 3) (pf₀ pf : Flags V) : V ≃ₗ[ZMod 2] V :=
  (exists_flagAct_eq hV pf₀ pf).choose

omit [DecidableEq V] [Fintype (Module.Dual (ZMod 2) V)] [DecidableEq (Module.Dual (ZMod 2) V)] in
theorem flagAct_flagElt (hV : finrank (ZMod 2) V = 3) (pf₀ pf : Flags V) :
    flagAct (flagElt hV pf₀ pf) pf₀ = pf :=
  (exists_flagAct_eq hV pf₀ pf).choose_spec

omit [Finite E] in
@[expose] def flagMap (hV : finrank (ZMod 2) V = 3) (pf₀ : Flags V) (e : E) :
    (Flags V → ZMod 2) →ₗ[ZMod 2] E :=
  Fintype.linearCombination (ZMod 2) fun pf => ρ (flagElt hV pf₀ pf) e

omit [Finite E] in
theorem flagMap_single (hV : finrank (ZMod 2) V = 3) {pf₀ : Flags V} {e : E}
    (he : ∀ g ∈ flagStab pf₀, ρ g e = e) : flagMap ρ hV pf₀ e (Pi.single pf₀ 1) = e := by
  rw [flagMap, Fintype.linearCombination_apply_single, one_smul]
  exact he _ (flagAct_flagElt hV pf₀ pf₀)

omit [Finite E] in
theorem flagMap_flagPermAct (hV : finrank (ZMod 2) V = 3) {pf₀ : Flags V} {e : E}
    (he : ∀ g ∈ flagStab pf₀, ρ g e = e) (h : V ≃ₗ[ZMod 2] V) (z : Flags V → ZMod 2) :
    flagMap ρ hV pf₀ e (flagPermAct h z) = ρ h (flagMap ρ hV pf₀ e z) := by
  simp only [flagMap, Fintype.linearCombination_apply, map_sum, map_smul]
  rw [← Equiv.sum_comp (flagPerm h)]
  refine Finset.sum_congr rfl fun pf _ => ?_
  change z (flagAct h.symm (flagAct h pf)) • ρ (flagElt hV pf₀ (flagAct h pf)) e =
    z pf • ρ h (ρ (flagElt hV pf₀ pf) e)
  rw [flagAct_symm_flagAct, ← Module.End.mul_apply, ← map_mul,
    apply_eq_of_flagAct_eq ρ he (g' := h * flagElt hV pf₀ pf)]
  rw [flagAct_flagElt, flagAct_mul, flagAct_flagElt]

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
