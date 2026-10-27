module

public import CFSG.ClassicalInvolution.Asc77.AscT7OG
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Klein

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Assembly.Dichotomy QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {X : Type} [Group X]

theorem eq_of_e_eq_of_fix_perp {e : ↥(elementaryGroup Q) →* X} (hker : KerScalar Q e)
    {fr : Frame Q} (hperp : fr.perp ≠ ⊥) {g h : ↥(elementaryGroup Q)} (hgh : e g = e h)
    (hg : ∀ u ∈ fr.perp, (g : V ≃ₗ[F] V) u = u) (hh : ∀ u ∈ fr.perp, (h : V ≃ₗ[F] V) u = u) :
    g = h := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have h1 : e (g * h⁻¹) = 1 := by rw [map_mul, map_inv, hgh, mul_inv_cancel]
  obtain ⟨c, hc⟩ := mem_scalars.mp (hker _ h1)
  have hhi : (h : V ≃ₗ[F] V)⁻¹ u = u := by
    apply (h : V ≃ₗ[F] V).injective
    rw [LinearEquiv.apply_inv_apply', hh u hu]
  have h2 := hc u
  have h3 : ((g * h⁻¹ : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) u = u := by
    change (g : V ≃ₗ[F] V) ((h : V ≃ₗ[F] V)⁻¹ u) = u
    rw [hhi, hg u hu]
  rw [h3] at h2
  have hc1 : c = 1 := by
    have : (c - 1) • u = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)
  have h4 : g * h⁻¹ = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc v, hc1, one_smul]
    rfl
  exact mul_inv_eq_one.mp h4

section Commute

variable (fr : Frame Q) {w : V ≃ₗ[F] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
  (hws : ∀ s ∈ fr.span, w s = s)

include hwO hws in
theorem w_comm_La (A : SL(2, F)) : fr.La A * w = w * fr.La A :=
  mul_comm_of_fix_span fr (fun _ hr => La_fix_perp fr A hr) (fun _ hs => La_mem_span fr A hs) hws
    (fun _ hr => map_mem_perp_of_fix fr hwO hws hr)

include hwO hws in
theorem w_comm_swap_La (A : SL(2, F)) : fr.swap.La A * w = w * fr.swap.La A :=
  mul_comm_of_fix_span fr (fun _ hr => swap_La_fix_perp fr A hr)
    (fun _ hs => swap_La_mem_span fr A hs) hws (fun _ hr => map_mem_perp_of_fix fr hwO hws hr)

end Commute

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
