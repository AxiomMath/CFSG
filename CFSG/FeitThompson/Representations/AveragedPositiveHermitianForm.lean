module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexOrder

noncomputable section

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

def IsInvariantSesqForm (ρ : Representation ℂ G V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : Prop :=
  ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y

theorem isInvariantSesqForm_iff {ρ : Representation ℂ G V} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} :
    IsInvariantSesqForm ρ B ↔ ∀ (g : G) (x y : V), B (ρ g x) (ρ g y) = B x y :=
  Iff.rfl

def averageSesqForm [Fintype G] (ρ : Representation ℂ G V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (B.comp (ρ g)).compl₂ (ρ g)

@[simp]
theorem averageSesqForm_apply [Fintype G] (ρ : Representation ℂ G V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x y : V) :
    averageSesqForm ρ B x y = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, B (ρ g x) (ρ g y) := by
  simp [averageSesqForm, Finset.mul_sum]

theorem isInvariantSesqForm_averageSesqForm [Fintype G] (ρ : Representation ℂ G V)
    (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) : IsInvariantSesqForm ρ (averageSesqForm ρ B) := by
  intro h x y
  rw [averageSesqForm_apply, averageSesqForm_apply]
  congr 1
  calc ∑ g : G, B (ρ g (ρ h x)) (ρ g (ρ h y))
      = ∑ g : G, B (ρ (g * h) x) (ρ (g * h) y) := by simp [map_mul]
    _ = ∑ g : G, B (ρ g x) (ρ g y) := Fintype.sum_equiv (Equiv.mulRight h) _ _ fun _ => rfl

theorem averageSesqForm_isSymm [Fintype G] (ρ : Representation ℂ G V)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : B.IsSymm) : (averageSesqForm ρ B).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [averageSesqForm_apply, averageSesqForm_apply]
  simp only [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  exact congrArg _ (Finset.sum_congr rfl fun g _ => hB.eq _ _)

theorem averageSesqForm_pos [Fintype G] (ρ : Representation ℂ G V)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : ∀ x : V, x ≠ 0 → 0 < B x x) (x : V) (hx : x ≠ 0) :
    0 < averageSesqForm ρ B x x := by
  have hcard : (0 : ℂ) < (Fintype.card G : ℂ)⁻¹ := by
    have h : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
    simpa using inv_pos.2 (Complex.zero_lt_real.mpr h)
  rw [averageSesqForm_apply]
  refine mul_pos hcard (Finset.sum_pos' (fun g _ => (hB _ ?_).le)
    ⟨1, Finset.mem_univ 1, hB _ (by simpa using hx)⟩)
  intro hc
  exact hx (by simpa using congrArg (ρ g⁻¹) hc)

private def euclidEquiv (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  (Module.finBasis ℂ V).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

private def stdSesqForm (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).comp (euclidEquiv V).toLinearMap).compl₂ (euclidEquiv V).toLinearMap

private theorem stdSesqForm_apply [FiniteDimensional ℂ V] (x y : V) :
    stdSesqForm V x y = inner ℂ (euclidEquiv V x) (euclidEquiv V y) := by
  simp [stdSesqForm]

private theorem stdSesqForm_isSymm [FiniteDimensional ℂ V] : (stdSesqForm V).IsSymm :=
  ⟨fun x y => by simp [stdSesqForm_apply, inner_conj_symm]⟩

private theorem stdSesqForm_pos [FiniteDimensional ℂ V] (x : V) (hx : x ≠ 0) :
    0 < stdSesqForm V x x := by
  rw [stdSesqForm_apply, inner_self_eq_norm_sq_to_K]
  have h : 0 < ‖euclidEquiv V x‖ := by simpa using (euclidEquiv V).map_ne_zero_iff.2 hx
  have h2 : (0 : ℝ) < ‖euclidEquiv V x‖ ^ 2 := by positivity
  simpa using Complex.zero_lt_real.mpr h2

theorem exists_isSymm_pos_isInvariantSesqForm [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, B.IsSymm ∧ (∀ x : V, x ≠ 0 → 0 < B x x) ∧
      IsInvariantSesqForm ρ B := by
  have : Fintype G := Fintype.ofFinite G
  exact ⟨averageSesqForm ρ (stdSesqForm V), averageSesqForm_isSymm ρ stdSesqForm_isSymm,
    averageSesqForm_pos ρ stdSesqForm_pos, isInvariantSesqForm_averageSesqForm ρ _⟩

@[instance_reducible]
def sesqFormCore {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hsymm : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) : InnerProductSpace.Core ℂ V where
  inner x y := B x y
  conj_inner_symm x y := hsymm.eq y x
  re_inner_nonneg x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact ((RCLike.pos_iff (K := ℂ)).1 (hpos x hx)).1.le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    exact (hpos x h).ne' hx

@[simp]
theorem sesqFormCore_inner {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hsymm : B.IsSymm)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (x y : V) :
    (sesqFormCore hsymm hpos).inner x y = B x y := (rfl)

theorem exists_invariant_innerProductSpaceCore [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ c : InnerProductSpace.Core ℂ V,
      ∀ (g : G) (x y : V), c.inner (ρ g x) (ρ g y) = c.inner x y := by
  obtain ⟨B, hsymm, hpos, hinv⟩ := exists_isSymm_pos_isInvariantSesqForm ρ
  exact ⟨sesqFormCore hsymm hpos, fun g x y => hinv g x y⟩

end

end CFSG.FeitThompson
