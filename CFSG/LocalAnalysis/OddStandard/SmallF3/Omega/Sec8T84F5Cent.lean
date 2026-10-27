module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Up

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84_no_E8_cent_t (F : Sec8T84Base) (hI : Asc82Step84IK)
    (hKP : CFSG.Assembly.KProper Catalog G) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    ∀ R : Subgroup G, R ≤ centralizer ({t} : Set G) → ¬ IsElemAb2 R 8 := by
  intro R hR hR8
  obtain ⟨γ, -, -, -, -, hcard⟩ := sec8t84_gamma0 F hI hKP hctx
  obtain ⟨B', -, -, -, -, -, honly⟩ := sec8t84_SL_E16 F hctx
  have hlt := sec8t84_rank_up4 (t := t) (S := S) (P := S ⊓ L) (B1 := B) (B2 := B')
    hctx.sylow inf_le_left hcard
    (fun U hU hUe hU16 => honly U hU ⟨hUe, by rw [hU16]; norm_num⟩) hR hR8.1
  rw [hR8.2] at hlt
  norm_num at hlt

end CFSG.OddStandard.SmallF3.Omega
