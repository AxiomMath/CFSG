module

public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.SmithC27RCaseIIG2Par

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {H R M K V : Subgroup G}

theorem three_of_residueTypeII_g2_of_radical_F4
    (hC132 : ASInputs.AS_C_1_32_F4) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V)
    (hV : IsElemAbelian 2 V)
    (hKT : ∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    C27Three H R M K V :=
  (g2StarData_of hs hV hKT hG).2.three_F4 hC132 h hs hnS hrad

end CFSG.Quasithin.SmithC27
