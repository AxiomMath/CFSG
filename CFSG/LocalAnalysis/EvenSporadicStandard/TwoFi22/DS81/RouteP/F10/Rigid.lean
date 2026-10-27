module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.CrossedKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.EndKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.SplitExtAut

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {Q W B : Type*} [Group Q] [CommGroup W] [Group B] {ρ : Q →* MulAut W}
  (X : ExtData ρ B)

theorem trivialModInner_ker (hH1 : ModH1Trivial ρ) (hEnd : ModEquivAutTrivial ρ) :
    TrivialModInner X.π.ker :=
  trivialModInner_of_forall_crossedHom (fun _ hx _ hy => X.ker_comm hx hy)
    (fun F hF hFE => X.exists_principal_of_crossedHom hH1 F hF hFE)
    (fun φ hφ => X.equivAut_ker hEnd φ hφ)

theorem exists_conj_of_trivialMod (hH1 : ModH1Trivial ρ) (hEnd : ModEquivAutTrivial ρ)
    (γ : B ≃* B) (hγ : ∀ b, X.π (γ b) = X.π b) :
    ∃ x : B, X.π x = 1 ∧ ∀ b, γ b = x * b * x⁻¹ := by
  obtain ⟨x, hx, h⟩ := X.trivialModInner_ker hH1 hEnd γ fun b => by
    rw [MonoidHom.mem_ker, map_mul, hγ b, map_inv, mul_inv_cancel]
  exact ⟨x, hx, h⟩

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
