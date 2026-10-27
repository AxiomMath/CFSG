module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Kernel
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {Q W B : Type*} [Group Q] [CommGroup W] [Group B] {ρ : Q →* MulAut W}
  (X : ExtData ρ B)

theorem equivAut_ker (hEnd : ModEquivAutTrivial ρ) (φ : ↥X.π.ker ≃* ↥X.π.ker)
    (hφ : ∀ (b : B) (x : ↥X.π.ker),
      φ (MulAut.conjNormal b x) = MulAut.conjNormal b (φ x)) :
    φ = MulEquiv.refl ↥X.π.ker := by
  let e := X.kerEquiv
  let ψ : W ≃* W := e.symm.trans (φ.trans e)
  have hψ : ∀ w : W, ψ w = e (φ (e.symm w)) := fun _ => rfl
  have hcomm : ∀ q w, ψ (ρ q w) = ρ q (ψ w) := by
    intro q w
    obtain ⟨b, hb⟩ := X.π_surjective q
    let x : ↥X.π.ker := e.symm w
    have hx : e x = w := e.apply_symm_apply w
    have hconj : e (MulAut.conjNormal b x) = ρ q w := by
      rw [X.kerEquiv_conj b x, hb, hx]
    calc
      ψ (ρ q w) = e (φ (e.symm (ρ q w))) := hψ _
      _ = e (φ (MulAut.conjNormal b x)) := by rw [← hconj, e.symm_apply_apply]
      _ = e (MulAut.conjNormal b (φ x)) := by rw [hφ b x]
      _ = ρ (X.π b) (e (φ x)) := X.kerEquiv_conj b (φ x)
      _ = ρ q (e (φ x)) := by rw [hb]
      _ = ρ q (ψ w) := by rw [hψ w]
  have hψrefl : ψ = MulEquiv.refl W := hEnd ψ hcomm
  ext x
  exact congrArg Subtype.val (e.injective (by
    have hx : ψ (e x) = e x := by rw [hψrefl]; rfl
    rwa [hψ, e.symm_apply_apply] at hx))

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
