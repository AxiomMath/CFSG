module

public import CFSG.Quasithin.EmptyFaithful.S152L25
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

variable {T Mc M : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}

theorem stageLemma15225_of_F4 (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4)
    (h15 : StageTheorem15215_F4) (hF : Claim15225F) : StageLemma15225_F4 := by
  intro G _ _ T Mc M hs
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  have hc : Case15213i T Mc M :=
    case15213i_of_claim hs.qtfe hs.mf (h13 G T Mc M hs H hH)
      (fun B₀ hB₀ => h14 G T Mc M hs B₀ hB₀) (fun B₀ hB₀ => h15 G T Mc M hs B₀ hB₀)
      (fun hii B₀ hB₀ => hF G T Mc M hs H hH hii B₀ hB₀)
  exact lemma_15_2_25_of_cases hs.qtfe hs.mf hc (fun B₀ hB₀ => h14 G T Mc M hs B₀ hB₀)

end CFSG.Quasithin
