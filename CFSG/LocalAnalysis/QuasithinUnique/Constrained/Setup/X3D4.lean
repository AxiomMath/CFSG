module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Case1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Case2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Dim

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer CFSG.SectionRank

theorem sixPointQuotient_holds : SixPointQuotient := by
  have hD : A6ShortGeneration := X3Aut.a6ShortGeneration
  have hE : A6SimpleModules := X3E.a6SimpleModules
  intro W _ _ _ H _ _ ρ hρ L A hN hqs hQ hcent hodd hne hel hLA hoff hstrict
  obtain ⟨eQ⟩ := hQ
  obtain ⟨sec⟩ := exists_d4Section ρ hρ L A hqs hcent hodd hne hel hLA hoff hstrict
  have hcard := card_M_le hD ρ L A hqs eQ hcent hodd hne hel sec
  by_cases hZ : ∀ z ∈ Subgroup.center ↥L, ∀ m ∈ sec.M, cvAct ρ L (z : H) m = m
  · exact six_point_case_one ρ L A hE hqs eQ hcent sec hcard hZ
  · push Not at hZ
    obtain ⟨z, hz, m, hm, hne'⟩ := hZ
    exact six_point_case_two ρ L A hqs eQ hcent hodd sec hcard ⟨z, hz, m, hm, hne'⟩

theorem no_A6_component_unconditional (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (hFF : Family.FFHyp V H T M E) (hns : ¬ Group.IsSolvable ↥H)
    (hsqtk : IsSQTKCat ↥H) {L : Subgroup (MulAut V)} (hL : Family.IsComp L H) :
    ¬ Nonempty (Family.CQ L ≃* alternatingGroup (Fin 6)) :=
  no_A6_component hcent hcat sixPointQuotient_holds hFF hns hsqtk hL

end CFSG.QuasithinUnique.Setup.X3
