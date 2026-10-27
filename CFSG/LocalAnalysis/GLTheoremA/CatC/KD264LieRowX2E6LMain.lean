module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LAmbient
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.E6Descent
open CFSG.RankThree.Classical2

section Residual

@[expose] def X2E6TorusComponentP
    (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1) (g : ModGL Tag.E6 Ω)
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    (ζ : Ωˣ) (hζ : ζ ^ 3 = 1) (_hζ' : orderOf ζ = 3)
    (G : Subgroup (Multiplicative (Fin 6 → ZMod 3))), Sel G →
    RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
      (G : Set _)) →
    ∃ J : Subgroup (twistedE6RootGroup K σ),
      IsSubnormal J (⨅ f ∈ G.map (torusAut hK σ hσ Fr hFr hg hgn hζ),
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup f) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)

theorem x2e6TorusGoodP_of_componentP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop)
    (h : X2E6TorusComponentP Sel) : X2E6TorusGoodP Sel := by
  intro K _ _ hK σ hσ Ω _ _ _ _ Fr hFr g hg hgn ζ hζ hζ' G hS hG
  haveI : Finite (twistedE6RootGroup K σ) := inferInstance
  obtain ⟨J, hJ, hq, hd⟩ := h K hK σ hσ Ω Fr hFr g hg hgn ζ hζ hζ' G hS hG
  exact isGood_of_subnormal_quasisimple Nat.prime_three hJ hq hd

end Residual

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
