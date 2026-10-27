module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCharacter
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def positiveProjection (T : Module.End K V) (b : K) : Module.End K V :=
  (2 : K)⁻¹ • (1 + b⁻¹ • T)

@[expose] def negativeProjection (T : Module.End K V) (b : K) : Module.End K V :=
  (2 : K)⁻¹ • (1 - b⁻¹ • T)

theorem positiveProjection_mem (T : Module.End K V) (b : K) (hb : b ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) (x : V) :
    positiveProjection T b x ∈ T.eigenspace b := by
  have hs : T (T x) = b ^ 2 • x := by
    simpa using congrArg (fun f : Module.End K V => f x) hsquare
  rw [Module.End.mem_eigenspace_iff]
  simp only [positiveProjection, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_smul, map_add, hs, smul_smul, smul_add]
  match_scalars <;> field_simp

theorem negativeProjection_mem (T : Module.End K V) (b : K) (hb : b ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) (x : V) :
    negativeProjection T b x ∈ T.eigenspace (-b) := by
  have hs : T (T x) = b ^ 2 • x := by
    simpa using congrArg (fun f : Module.End K V => f x) hsquare
  rw [Module.End.mem_eigenspace_iff]
  simp only [negativeProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_smul, map_sub, hs, smul_smul, smul_sub]
  match_scalars <;> field_simp

theorem positiveProjection_add_negativeProjection (T : Module.End K V) (b : K)
    (htwo : (2 : K) ≠ 0) (x : V) :
    positiveProjection T b x + negativeProjection T b x = x := by
  have hh : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by field_simp; ring
  simp only [positiveProjection, negativeProjection, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply]
  calc
    (2 : K)⁻¹ • (x + b⁻¹ • T x) + (2 : K)⁻¹ • (x - b⁻¹ • T x) =
        ((2 : K)⁻¹ + (2 : K)⁻¹) • x := by module
    _ = x := by rw [hh, one_smul]

theorem squareScalar_eigenspaces_isCompl (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) :
    IsCompl (T.eigenspace b) (T.eigenspace (-b)) := by
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    rw [Module.End.mem_eigenspace_iff] at hx hy
    have hzero : (2 * b) • x = 0 := by
      calc
        (2 * b) • x = b • x - (-b) • x := by module
        _ = 0 := by rw [← hx, ← hy, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (mul_ne_zero htwo hb)
  · rw [codisjoint_iff_le_sup]
    intro x _
    exact Submodule.mem_sup.mpr ⟨positiveProjection T b x,
      positiveProjection_mem T b hb hsquare x, negativeProjection T b x,
      negativeProjection_mem T b hb hsquare x,
      positiveProjection_add_negativeProjection T b htwo x⟩

@[expose] def squareScalar_eigenspaceEquiv (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) :
    (T.eigenspace b × T.eigenspace (-b)) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl _ _ (squareScalar_eigenspaces_isCompl T b hb htwo hsquare)

theorem squareScalar_eigenspace_finrank [FiniteDimensional K V]
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V)) :
    Module.finrank K (T.eigenspace b) + Module.finrank K (T.eigenspace (-b)) =
      Module.finrank K V :=
  Submodule.finrank_add_eq_of_isCompl (squareScalar_eigenspaces_isCompl T b hb htwo hsquare)

theorem eigenspace_eq_top_iff_scalar (T : Module.End K V) (b : K) :
    T.eigenspace b = ⊤ ↔ T = b • (1 : Module.End K V) := by
  constructor
  · intro h
    ext x
    have hx : x ∈ T.eigenspace b := by rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.mp hx
  · intro h
    subst T
    apply top_unique
    intro x _
    simp

theorem squareScalar_eigenspaces_ne_bot (T : Module.End K V) (b : K)
    (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hnonscalar : ∀ c : K, T ≠ c • (1 : Module.End K V)) :
    T.eigenspace b ≠ ⊥ ∧ T.eigenspace (-b) ≠ ⊥ := by
  have h := squareScalar_eigenspaces_isCompl T b hb htwo hsquare
  constructor
  · intro hz
    have htop : T.eigenspace (-b) = ⊤ := by simpa only [hz, bot_sup_eq] using h.sup_eq_top
    exact hnonscalar (-b) ((eigenspace_eq_top_iff_scalar T (-b)).mp htop)
  · intro hz
    have htop : T.eigenspace b = ⊤ := by simpa only [hz, sup_bot_eq] using h.sup_eq_top
    exact hnonscalar b ((eigenspace_eq_top_iff_scalar T b).mp htop)

theorem squareScalar_eigenspace_finrank_pos [FiniteDimensional K V]
    (T : Module.End K V) (b : K) (hb : b ≠ 0) (htwo : (2 : K) ≠ 0)
    (hsquare : T * T = b ^ 2 • (1 : Module.End K V))
    (hnonscalar : ∀ c : K, T ≠ c • (1 : Module.End K V)) :
    0 < Module.finrank K (T.eigenspace b) ∧
      0 < Module.finrank K (T.eigenspace (-b)) := by
  have h := squareScalar_eigenspaces_ne_bot T b hb htwo hsquare hnonscalar
  exact ⟨Nat.pos_of_ne_zero (fun hz => h.1 (Submodule.finrank_eq_zero.mp hz)),
    Nat.pos_of_ne_zero (fun hz => h.2 (Submodule.finrank_eq_zero.mp hz))⟩

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
