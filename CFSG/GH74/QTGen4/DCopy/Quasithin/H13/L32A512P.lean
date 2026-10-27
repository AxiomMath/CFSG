module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53a
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.Recognition.GoldschmidtTriple

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_5_12CaseOne_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G),
    Ctx_F4 G T L V V₂ Y →
    quasithinO2QuotientIso (xL L V₂ ⊔ T) (Equiv.Perm (Fin 3)) →
    (xL L V₂ ⊔ T) ⊓ (Y ⊔ T) = T →
    pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ → Group.IsSolvable ↥(hY T L V₂ Y) →
    thompsonJ T ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) →
    xL L V₂ = ⁅xL L V₂, thompsonJk 1 T⁆ →
    (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)).map (hY T L V₂ Y).subtype ≤
      Subgroup.centralizer (vH T L V V₂ Y : Set G) →
    IsGoldschmidtAmalgam
      (((xL L V₂ ⊔ T).subgroupOf (hY T L V₂ Y)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y))))
      (((Y ⊔ T).subgroupOf (hY T L V₂ Y)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(hY T L V₂ Y)))) →
    pCoreOf 2 (xL L V₂ ⊔ T) = pCoreOf 2 (Y ⊔ T) → False

end CFSG.Quasithin.H13.L32A.T53
