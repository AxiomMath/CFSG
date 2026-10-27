module

public import CFSG.Assembly.InCatalog
public import CFSG.Assembly.CatalogTransport

public section

namespace CFSG.Assembly.Quasithin

@[expose] def quasithinEvenCharacteristic (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsTwoLocal H → (∃ S : Sylow 2 G, (S : Subgroup G) ≤ H) →
    H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H

@[expose] def QTKEOver (C : GroupProp) (G : Type) [Group G] [Finite G] : Prop :=
  KProper C G ∧ quasithinEvenCharacteristic G ∧ evenRank G ≤ 2

@[expose] def quasithinIsQTKE (G : Type) [Group G] [Finite G] : Prop :=
  QTKEOver InCatalog G

theorem quasithinEvenCharacteristic_of_isCharTwoType {G : Type*} [Group G]
    (h : IsCharTwoType G) : quasithinEvenCharacteristic G :=
  fun H hH _ => h H hH

section Transport

variable {C D : GroupProp} {G : Type} [Group G] [Finite G]

theorem QTKEOver.of_isCharTwoType (hK : KProper C G) (hchar : IsCharTwoType G)
    (he : evenRank G ≤ 2) : QTKEOver C G :=
  ⟨hK, quasithinEvenCharacteristic_of_isCharTwoType hchar, he⟩

theorem QTKEOver.of_catalogImp (h : CatalogImp C D) (hG : QTKEOver C G) : QTKEOver D G :=
  ⟨hG.1.of_catalogImp h, hG.2.1, hG.2.2⟩

theorem QTKEOver.of_catalogAgree (h : CatalogAgreeOn C D) (hG : QTKEOver C G) : QTKEOver D G :=
  hG.of_catalogImp h.imp

theorem qtkeOver_iff_of_catalogAgree (h : CatalogAgreeOn C D) : QTKEOver C G ↔ QTKEOver D G :=
  ⟨QTKEOver.of_catalogAgree h, QTKEOver.of_catalogAgree h.symm⟩

end Transport

@[expose] def quasithinIsMaxTwoLocal {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  CFSG.Open.IsMaxTwoLocalSubgroup M

section Local

variable {G : Type*} [Group G]

@[expose] def quasithinIsCComponent (L X : Subgroup G) : Prop :=
  L ≠ ⊥ ∧ ⁅L, L⁆ = L ∧ IsSubnormal L X ∧
    ∀ K : Subgroup G, K < L → K ≠ ⊥ → ⁅K, K⁆ = K → ¬ IsSubnormal K X

@[expose] def quasithinGenFitting (L : Subgroup G) : Subgroup G :=
  sSup {N | N ≤ L ∧ (N.subgroupOf L).Normal ∧ Group.IsNilpotent N} ⊔
    sSup {K | IsComponentOf K L}

@[expose] def quasithinV2 (L : Subgroup G) : Subgroup G :=
  ⁅Subgroup.closure {z | z ∈ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ∧
    z ^ 2 = 1}, L⁆

@[expose] def quasithinIsLocal (T L : Subgroup G) : Prop :=
  IsPGroup 2 T ∧ quasithinIsCComponent L (L ⊔ T) ∧
    ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index ∧ pCoreOf 2 (L ⊔ T) ≠ ⊥

@[expose] def quasithinIsFaithfulLocal (T L : Subgroup G) : Prop :=
  quasithinIsLocal T L ∧
    (∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L) ∧
    quasithinGenFitting L = pCoreOf 2 L ∧
    quasithinV2 L ≠ ⊥

end Local

end CFSG.Assembly.Quasithin
