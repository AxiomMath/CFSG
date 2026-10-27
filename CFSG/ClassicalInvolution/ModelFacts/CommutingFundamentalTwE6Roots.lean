module

public import Mathlib
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4Data
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Adjoint

theorem twistedE6_short_lift_check :
    ∀ b₀ b₁ b₂ b₃ : Bool, ∀ x ∈ rootFinset .E6, rho x ≠ x →
      maskPairing (τ := .F4) ![b₀, b₁, b₂, b₃] (proj x) % 2 = 0 →
      ∃ y ∈ rootFinset .E6, rho y = y ∧
        maskPairing (τ := .F4) ![b₀, b₁, b₂, b₃] (proj y) % 2 = 0 ∧
        x - y ∈ rootFinset .E6 ∧ rho (x - y) ≠ x - y ∧
        (x - y) + rho (x - y) + y ∈ rootFinset .E6 := by
  decide +kernel

theorem exists_e6_lift_of_short_root {m : Fin Tag.F4.rank → Bool} {s' : Fin Tag.F4.rank → ℤ}
    (hs' : IsRoot .F4 s') (hl : iform s' s' ≠ 4) (hm : maskPairing m s' % 2 = 0) :
    ∃ a b : Fin Tag.E6.rank → ℤ, IsRoot .E6 a ∧ IsRoot .E6 b ∧ rho b = b ∧ rho a ≠ a ∧
      proj (a + b) = s' ∧ maskPairing m (proj b) % 2 = 0 ∧ IsRoot .E6 (a + b) ∧
      IsRoot .E6 (a + rho a + b) := by
  obtain ⟨x, hx, rfl⟩ := exists_proj_eq hs'
  have hρx : rho x ≠ x := fun h => hl (iform_proj_eq_four_of_rho_eq hx h)
  have hm' : m = ![m (0 : Fin 4), m (1 : Fin 4), m (2 : Fin 4), m (3 : Fin 4)] := by
    funext i
    fin_cases i <;> rfl
  rw [hm'] at hm ⊢
  obtain ⟨y, hy, hρy, hmy, hxy, hρxy, hγ⟩ :=
    twistedE6_short_lift_check _ _ _ _ x (mem_rootFinset.2 hx) hρx hm
  refine ⟨x - y, y, mem_rootFinset.1 hxy, mem_rootFinset.1 hy, hρy, hρxy, ?_, hmy, ?_,
    mem_rootFinset.1 hγ⟩
  · rw [sub_add_cancel]
  · rw [sub_add_cancel]
    exact hx

end CFSG.ClassicalInvolution.ModelFacts
