module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Spor

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup

@[expose] def SporNoTwoFix (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nonempty (Y ≃* Blueprint.NativeSporadic.Carrier s) →
    ∀ a : MulAut Y, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a)

theorem twoNilpFor_spor_of {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s) (hfix : SporNoTwoFix s) :
    TwoNilpFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s := by
  intro Y _ _ hY hs hna a ha hP
  obtain ⟨e⟩ := hY
  have hO : pPrimeCore 2 ↥(fixedPoints a) = ⊥ :=
    N36.pPrimeCore_fixedPoints_eq_bot_of_mulAut hna
      (fun i hi => N36.mulAut_oddCore_eq_bot hodd hna e i hi) ha
  exact absurd (isPGroup_of_pPrimeCore_eq_bot hO hP) (hfix Y ⟨e⟩ a ha)

end CFSG.ComponentClassification.HarrisLit.L33
