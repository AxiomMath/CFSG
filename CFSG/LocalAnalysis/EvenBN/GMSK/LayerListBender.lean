module

public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOneBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatAltBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBender
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

theorem stdTypeFacts_T_U3 : StdTypeFacts T_U3 := fun _ _ _ _ h =>
  ⟨isSimpleGroup_of_lieModel_PSU3 h.2, exists_mul_ne_of_lieModel_PSU3 h.2,
    exists_four_of_lieModel_PSU3 h.2⟩

theorem stdTypeFacts_T_Sz : StdTypeFacts T_Sz := fun _ _ _ _ h =>
  ⟨isSimpleGroup_of_lieModel_twistedB2 h, exists_mul_ne_of_lieModel_twistedB2 h,
    exists_four_of_lieModel_twistedB2 h⟩

section LayerLists

theorem gmsUnitary_sharp {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hA : StdUnitaryData G A n) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ Subgroup.centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (Subgroup.zpowers t).relIndex (Subgroup.centralizer (A : Set G))) :
    SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * n)) G A t :=
  gmsUnitary_sharp_of_selector stdTypeFacts_T_U3
    (catalog_selectorOf (fun n S _ _ h => (stdTypeFacts_T_U3 n S h).2.1)
      fixedRootSelectorOf_alternating_U3 fixedRootSelectorOf_oddLieType_U3
      fixedRootSelectorOf_evenLieType_U3 fixedRootSelectorOf_sporadicRep_U3)
    hG hO hA ht htA hsyl

theorem gmsSuzuki_sharp {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hA : StdSuzukiData G A n) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ Subgroup.centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (Subgroup.zpowers t).relIndex (Subgroup.centralizer (A : Set G))) :
    SharpOutcome (fun D _ => LieModel D .PSp 2 2 n) G A t :=
  gmsSuzuki_sharp_of_selector stdTypeFacts_T_Sz
    (catalog_selectorOf (fun n S _ _ h => (stdTypeFacts_T_Sz n S h).2.1)
      fixedRootSelectorOf_alternating_Sz fixedRootSelectorOf_oddLieType_Sz
      fixedRootSelectorOf_evenLieType_Sz fixedRootSelectorOf_sporadicRep_Sz)
    hG hO hA ht htA hsyl

end LayerLists

end CFSG.LocalAnalysis.EvenBN.GMSK
