module


public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

namespace CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition

open Module Polynomial CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

universe u

theorem span_eq_top {F : Type u} [Field F] [IsAlgClosed F] {V E : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [CommGroup E] [Finite E]
    (τ : Representation F E V) (hcard : (Nat.card E : F) ≠ 0) :
    (⨆ χ : E →* Fˣ, weightSpace τ χ) = ⊤ := by
  have isSemisimple_apply (τ : Representation F E V)
      (hcard : (Nat.card E : F) ≠ 0) (g : E) : Module.End.IsSemisimple (τ g) := by
    have hn : 0 < Nat.card E := Nat.card_pos
    have hsq : Squarefree ((X : F[X]) ^ Nat.card E - C (1 : F)) :=
      (Polynomial.separable_X_pow_sub_C (1 : F) hcard one_ne_zero).squarefree
    have hT : (τ g) ^ Nat.card E = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    have hev : aeval (τ g) ((X : F[X]) ^ Nat.card E - C (1 : F)) = 0 := by
      simp [hT]
    exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev
  classical
  have hcomm : Pairwise fun g h : E => Commute (τ g) (τ h) := by
    intro g h _
    show τ g * τ h = τ h * τ g
    rw [← map_mul, ← map_mul, mul_comm]
  have h' : ∀ g : E, ⨆ μ, Module.End.maxGenEigenspace (τ g) μ = ⊤ := by
    intro g
    have hss := isSemisimple_apply τ hcard g
    exact Module.End.iSup_maxGenEigenspace_eq_top (τ g)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun g : E => τ g) hcomm h'
  rw [eq_top_iff, ← htop]
  refine iSup_le fun χ => ?_
  have hss : ∀ g, Module.End.IsFinitelySemisimple (τ g) := fun g => (isSemisimple_apply τ hcard g).isFinitelySemisimple
  have heq : ∀ g, Module.End.maxGenEigenspace (τ g) (χ g) = Module.End.eigenspace (τ g) (χ g) :=
    fun g => (hss g).maxGenEigenspace_eq_eigenspace _
  simp only [heq]
  by_cases hbot : (⨅ g, Module.End.eigenspace (τ g) (χ g)) = ⊥
  · rw [hbot]; exact bot_le
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hv' : ∀ g, τ g v = χ g • v := fun g =>
      Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hv g)
    have hmul : ∀ g h, χ (g * h) = χ g * χ h := by
      intro g h
      have : (χ (g * h) - χ g * χ h) • v = 0 := by
        rw [sub_smul, ← hv' (g * h), map_mul]
        show _ - _ = 0
        rw [Module.End.mul_apply, hv' h, map_smul, hv' g, smul_smul, mul_comm, sub_self]
      rcases smul_eq_zero.1 this with h0 | h0
      · exact sub_eq_zero.1 h0
      · exact absurd h0 hv0
    have hone : χ 1 = 1 := by
      have : (χ 1 - 1) • v = 0 := by
        rw [sub_smul, ← hv' 1, one_smul, map_one]; simp
      rcases smul_eq_zero.1 this with h0 | h0
      · exact sub_eq_zero.1 h0
      · exact absurd h0 hv0
    let ψ : E →* Fˣ :=
      MonoidHom.toHomUnits (G := E) (M := F)
        { toFun := χ, map_one' := hone, map_mul' := hmul }
    refine le_trans ?_ (le_iSup (fun ψ : E →* Fˣ => weightSpace τ ψ) ψ)
    intro w hw g
    exact Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hw g)

end CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
