module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint CFSG.LieType.Ree

theorem ivk93_ree :
    ∀ f : ℕ, Ivk93Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  have hR : ReeTitsModel J .twistedG2 3 f := by
    rcases hJ with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  obtain ⟨a, K, _, _, _, hK, ⟨e⟩⟩ := GHInv.ree_model_data hR
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (CFSG.LieType.Chevalley.coxeterSystem ReeTag.G2.tag).length
  exact (hc.of_equiv e).false_of_abelian_sylow
    (CFSG.Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK hw₀)

end CFSG.GH74.GLS.IVK.Proofs2
