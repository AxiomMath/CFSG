module

public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Par
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {H R M K V : Subgroup G}

namespace G2StarData

variable (hd : G2StarData R K V)
include hd

theorem three_F4 (hC132 : ASInputs.AS_C_1_32_F4) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V) :
    C27Three H R M K V := by
  have hB : IsG2Block K := isG2Block_of_card_autOn h hs hd.card_K
    (hC132 G (K ⊔ R) R K (hd.isMSPair h hs hnS hrad) h.mem_cComp_sup h.coe_sup)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hB, hd.g2Two, (hd.maxParabolic h hs hnS hrad).2⟩)))))

end G2StarData

end CFSG.Quasithin.SmithC27
