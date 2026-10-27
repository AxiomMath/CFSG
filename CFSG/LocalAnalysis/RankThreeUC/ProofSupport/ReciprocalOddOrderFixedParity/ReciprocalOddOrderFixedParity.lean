module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace.OddOrderMovedSubspace
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.InvertibleAnticonjugateEvenDimension.InvertibleAnticonjugateEvenDimension

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ReciprocalOddOrderFixedParity

open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace

theorem even_moved {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (h2 : (2 : F) ≠ 0) (r : ℕ) (hr : Odd r) (hrF : (r : F) ≠ 0)
    (t : W ≃ₗ[F] W) (ht : t ^ r = 1) (j : W ≃ₗ[F] W) (hj : j * t * j⁻¹ = t⁻¹) :
    Even (Module.finrank F W - Module.finrank F (LinearMap.ker (t.toLinearMap - LinearMap.id))) := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (t.toLinearMap - LinearMap.id)
  have hfin : Module.finrank F W - Module.finrank F (LinearMap.ker (t.toLinearMap - LinearMap.id))
      = Module.finrank F (moved t) := by
    show _ = Module.finrank F (LinearMap.range (t.toLinearMap - LinearMap.id))
    omega
  rw [hfin]
  have hj1 : ∀ x, j (t x) = t⁻¹ (j x) := fun x => by
    have := congrArg (fun g : W ≃ₗ[F] W => g (j x)) hj
    simpa [LinearEquiv.mul_apply] using this
  have hj2 : ∀ x, j (t⁻¹ x) = t (j x) := fun x => by
    have h : j x = t⁻¹ (j (t⁻¹ x)) := by
      have := hj1 (t⁻¹ x)
      have e : t (t⁻¹ x) = x := by simp
      rw [e] at this
      exact this
    rw [h]
    simp
  have hMti : ∀ w, t⁻¹ w - w ∈ moved t := fun w => ⟨-(t⁻¹ w), by simp; abel⟩
  have hjM : ∀ x ∈ moved t, j x ∈ moved t := by
    rintro x ⟨w, rfl⟩
    have : j ((t.toLinearMap - LinearMap.id : W →ₗ[F] W) w) = t⁻¹ (j w) - j w := by
      simp [hj1]
    rw [this]
    exact hMti (j w)
  let j' : moved t →ₗ[F] moved t := (j.toLinearMap).restrict hjM
  have hinj : Function.Injective j' := fun x y h =>
    Subtype.ext (j.injective (congrArg Subtype.val h))
  let jE := LinearEquiv.ofInjectiveEndo j' hinj
  apply CFSG.LocalAnalysis.RankThreeUC.ProofSupport.InvertibleAnticonjugateEvenDimension.even h2
    (differenceAut hr hrF t ht) jE
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [jE, j', LinearEquiv.coe_ofInjectiveEndo, differenceAut_apply, hj1]
  exact hj2 _

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ReciprocalOddOrderFixedParity
