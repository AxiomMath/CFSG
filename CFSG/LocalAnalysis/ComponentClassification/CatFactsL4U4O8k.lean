module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] {b c : K}

theorem left_comm (hnd : (Q8 K b c).polarBilin.Nondegenerate)
    (hT : ∃ S : Submodule K (Fin (2 * 4) → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q8 K b c v = 0)
    (hAP : CatalogueBOrthogonalPointAction.ActionProperties (Q8 K b c)
      (CatalogueBOrthogonalPointData.projectivePointAction (Q8 K b c)))
    (ψ φ : MulAut (G0 K b c)) (g gφ : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (hgφ : matrixProjectiveConjugationHom (Q8 K b c) gφ = MulAut.congr (psiC K b c) φ)
    (hg1 : g.val.right = 1) (hgφ1 : gφ.val.right = 1) (hcomm : ψ * φ = φ * ψ) :
    ∃ a : Kˣ, g.val.left * gφ.val.left =
      GeneralLinearGroup.scalar (Fin (2 * 4)) a * (gφ.val.left * g.val.left) := by
  have hker := RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff
    (Q8 K b c) hnd hT hAP
  have h1 : matrixProjectiveConjugationHom (Q8 K b c) (g * gφ * (gφ * g)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hg, hgφ, ← map_mul, ← map_mul, hcomm,
      mul_inv_cancel]
  obtain ⟨-, a, ha⟩ := (hker _).mp h1
  refine ⟨a, ?_⟩
  have e : (g * gφ * (gφ * g)⁻¹).val.left =
      g.val.left * gφ.val.left * (gφ.val.left * g.val.left)⁻¹ := by
    change (g.val * gφ.val * (gφ.val * g.val)⁻¹).left = _
    rw [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_left,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
      hg1, hgφ1, mul_one, inv_one, map_one]
    simp only [MulAut.one_apply]
  rw [e] at ha
  calc g.val.left * gφ.val.left = g.val.left * gφ.val.left * (gφ.val.left * g.val.left)⁻¹ *
        (gφ.val.left * g.val.left) := by group
    _ = _ := by rw [ha]

theorem left_sq (gφ : similarityPairs (Q8 K b c)) (c₀ : Kˣ)
    (hsq : ∀ x, matrixLinearEquiv gφ.val.left (matrixLinearEquiv gφ.val.left x) = (c₀ : K) • x) :
    gφ.val.left * gφ.val.left = GeneralLinearGroup.scalar (Fin (2 * 4)) c₀ := by
  apply matrixLinearIso.injective
  apply LinearEquiv.ext
  intro x
  rw [map_mul, LinearEquiv.mul_apply]
  exact (hsq x).trans (matrixLinearEquiv_scalar c₀ x).symm

theorem sq_eq_one (B A : GL (Fin (2 * 4)) K) (a c₀ : Kˣ)
    (hA : A * A = GeneralLinearGroup.scalar (Fin (2 * 4)) c₀)
    (h : B * A = GeneralLinearGroup.scalar (Fin (2 * 4)) a * (A * B)) : a * a = 1 := by
  have hc : ∀ (u : Kˣ) (X : GL (Fin (2 * 4)) K),
      GeneralLinearGroup.scalar (Fin (2 * 4)) u * X =
        X * GeneralLinearGroup.scalar (Fin (2 * 4)) u := fun u X => by
    have hs : GeneralLinearGroup.scalar (Fin (2 * 4)) u ∈
        Subgroup.center (GL (Fin (2 * 4)) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact (Subgroup.mem_center_iff.mp hs X).symm
  set s := GeneralLinearGroup.scalar (Fin (2 * 4)) a with hs
  set s₀ := GeneralLinearGroup.scalar (Fin (2 * 4)) c₀ with hs₀
  have h1 : B * (A * A) = s * s * (A * A) * B := by
    calc B * (A * A) = (B * A) * A := by group
      _ = s * (A * B) * A := by rw [h]
      _ = s * A * (B * A) := by group
      _ = s * A * (s * (A * B)) := by rw [h]
      _ = s * (A * s) * (A * B) := by group
      _ = s * (s * A) * (A * B) := by rw [hc a A]
      _ = s * s * (A * A) * B := by group
  rw [hA, ← hc c₀ B] at h1
  have h2 : s₀ = s * s * s₀ := mul_right_cancel h1
  have h3 : s * s = 1 := by
    have h4 : (1 : GL (Fin (2 * 4)) K) * s₀ = s * s * s₀ := by rw [one_mul]; exact h2
    exact (mul_right_cancel h4).symm
  have h5 := congrArg (fun X : GL (Fin (2 * 4)) K => (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
    0 0) h3
  rw [hs, ← map_mul] at h5
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h5
  exact Units.ext (by simpa using h5)

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
