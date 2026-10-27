module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem ivk73_ree :
    ∀ f : ℕ, Ivk73Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro f N _ _ L K Q h hM
  have hR : ReeTitsModel ↥L .twistedG2 3 f := by
    rcases hM with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
    · exact absurd hh (by decide)
    · exact absurd hh (by decide)
    · exact hR
    · exact absurd hh (by decide)
  exact h.false_of_rank_out (r := 3) (s := 0) (by norm_num)
    (fun E hE => GHInv.ree_card_elementary_le hR E hE)
    (fun E hE => GHInv.ree_card_outer_elementary hR E hE)

end CFSG.GH74.GLS.IVK
