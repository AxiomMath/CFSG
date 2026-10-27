module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.Walter.J1Props.Factor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint CFSG.LieType.Ree

theorem ivk95_j1 :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e0⟩ := hJ
  let e : J ≃* CFSG.Open.walterJ1 := e0.trans CFSG.Walter.walterJ1EquivNative.symm
  exact (hz.of_equiv e).false_of_abelian_sylow CFSG.Walter.J1Props.hasAbelianSylowTwo

theorem ivk95_ree :
    ∀ f : ℕ, Ivk95Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  have hR : ReeTitsModel J .twistedG2 3 f := by
    rcases hJ with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  exact (hz.of_equiv e).false_of_abelian_sylow
    (CFSG.Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK hw₀)

end CFSG.GH74.GLS.IVK.Proofs2
