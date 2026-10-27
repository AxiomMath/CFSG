module

public import CFSG.GH74.QTGen4.U42.ModelCoordsRelabelled

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5
open CFSG.Quasithin.H13.F431.U42 U42F431

section Model

theorem exists_model_coords_plain :
    ∃ e : ↥P2 ≃* Mof (alternatingGroup (Fin 5)),
      (∀ (v : Y) (hv : v ∈ Vsub),
        ((e ⟨v, Vsub_le_P2 hv⟩ : Mof _) : Mc) =
          SemidirectProduct.inl (pact sigma0 (psiEq ⟨v, hv⟩))) ∧
      ∀ g : ↥P2, ((e g : Mof _) : Mc).right = permOf4 g :=
  exists_model_coords_relabelled

end Model

end CFSG.GH74.QTGen4.U42
