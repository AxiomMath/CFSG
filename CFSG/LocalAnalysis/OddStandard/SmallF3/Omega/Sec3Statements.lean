module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (standardComponentIsStandard)

structure Sec3SettingLB (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) : Prop
    extends Sec3Setting G t L where
  lBalance : AschLBalance G
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  notCat : ¬ CFSG.Blueprint.Catalog G

structure Sec3PocketData {G : Type} [Group G] (x : G) (X : Subgroup G) (y : G)
    (K : Subgroup G) : Prop where
  involution_x : orderOf x = 2
  component : IsComponentIn X (centralizer ({x} : Set G))
  inFStar : InFStar X
  involution_y : orderOf y = 2
  mem : y ∈ X
  le : K ≤ X
  pocket : Sl23Pocket x y K

@[expose] def Asc82PocketExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (X : Subgroup G),
    orderOf x = 2 → IsComponentIn X (centralizer ({x} : Set G)) → (InF X ∨ IsL3Eps3 X) →
      ∃ (y : G) (K : Subgroup G), orderOf y = 2 ∧ K ≤ X ∧ Sl23Pocket x y K

@[expose] def Asc82NonCommuteNonPocketed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ X : Subgroup G, InCStar X → InFStar X → ¬ InF X → ¬ IsL3Eps3 X →
      ∀ g : G, ⁅X, X.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥

@[expose] def Asc82StandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ¬ CFSG.Blueprint.Catalog G →
    AschA1 G → AschA2 G → (∃ L : Subgroup G, InF L ∧ InC L) →
      ∀ X : Subgroup G, standardComponentIsStandard X → InFStar X →
        (∃ S : Sylow 2 (centralizer (X : Set G)),
          ¬ IsCyclic (S : Subgroup (centralizer (X : Set G)))) → Chev3 G

@[expose] def Asc82Omega8MinusData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    InF L → LieModel (L ⧸ oddCore L) .POmegaMinus 4 3 1 →
      ∃ z : G, IsI4PlusIn L z ∧
        ∃ J : Subgroup G, IsComponentIn J (L ⊓ centralizer ({z} : Set G)) ∧ InFStar J

@[expose] def Asc82Lemma33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ X : Subgroup G, InCStar X → InFStar X →
      ∀ S : Sylow 2 (centralizer (X : Set G)), IsCyclic (S : Subgroup (centralizer (X : Set G)))

@[expose] def Asc82Lemma34a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G) (u : G) (I : Subgroup G),
      Sec3PocketData x X y K → orderOf u = 2 →
      (∃ c ∈ centralizer ((X ⊔ zpowers x : Subgroup G) : Set G), u = c * y) →
      IsComponentIn I (centralizer ({u} : Set G)) → InFStar I →
        ⁅K, I⁆ = ⊥ ∨ CFSG.inSubgroup (CFSG.pCore 2) K ≤ I

@[expose] def Asc82Lemma34b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G) (u : G) (I : Subgroup G),
      Sec3PocketData x X y K → orderOf u = 2 →
      (∃ c ∈ centralizer ((X ⊔ zpowers x : Subgroup G) : Set G), u = c * y) →
      IsComponentIn I (centralizer ({u} : Set G)) → InFStar I →
        CFSG.inSubgroup (CFSG.pCore 2) K ≤ I → ⁅zpowers y, I⁆ ≠ ⊥ →
          (InF I ∧ IsI4PlusIn I y) ∨ IsLnEps3 I

@[expose] def Asc82Lemma34c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G), Sec3PocketData x X y K →
      ∀ J : Subgroup G, IsComponentIn J (centralizer ({y} : Set G)) → ¬ InFStar J

@[expose] def Asc82Lemma35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G) (u : G),
      Sec3PocketData x X y K → orderOf u = 2 → u ∈ centralizer ({y} : Set G) →
        ∀ J : Subgroup G, ¬ (IsComponentIn J (centralizer ({u, y} : Set G)) ∧ InFStar J)

@[expose] def Asc82Lemma36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G), orderOf x = 2 → IsComponentIn X (centralizer ({x} : Set G)) →
      (InF X ∨ IsL3Eps3 X) →
        InFStar X ∧ ∀ I : Subgroup G, IsComponentIn I (centralizer ({x} : Set G)) →
          InFStar I → I = X

@[expose] def Asc82Lemma37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ z g : G, IsI4PlusIn L z → g⁻¹ * z * g ∈ centralizer ({t} : Set G) →
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({g⁻¹ * z * g} : Set G)) = ⊥

@[expose] def Asc82Lemma37F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ z g : G, IsI4PlusIn L z → g⁻¹ * z * g ∈ centralizer ({t} : Set G) →
      ∀ J : Subgroup G, ¬ (IsComponentIn J (L ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ∧ InFStar J)

@[expose] def Asc82Lemma38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ¬ LieModel (L ⧸ oddCore L) .POmegaMinus 4 3 1

@[expose] def Asc82Lemma39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (u : G) (K : Subgroup G), orderOf u = 2 → u ∈ L → u ∈ K →
      IsComponentIn K (L ⊓ centralizer ({u} : Set G)) → IsTwoU43 (K ⧸ oddCore K) →
        IsComponentIn K (centralizer ({u} : Set G)) ∧ InFStar K ∧
          ∀ I : Subgroup G, IsComponentIn I (centralizer ({u} : Set G)) → InFStar I → I = K

@[expose] def Asc82Lemma311 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ¬ LieModel (L ⧸ oddCore L) .POmegaPlus 4 3 1

end CFSG.OddStandard.SmallF3.Omega
