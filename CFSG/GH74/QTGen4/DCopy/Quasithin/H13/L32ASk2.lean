module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_30_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, CFSG.IsQuasisimple (L32A.cStar K) ∧ ¬ K ≤ Subgroup.normalizer (L : Set G) ∧
      Setting147 G T L V (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T)) ∧
      HypF918 T V L (fsuV1 T V) V (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T)) K

@[expose] def Lemma14_7_36_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ∀ s : TauCeti.SporadicName,
      ¬ IsSporadic s (L32A.cStar K ⧸ Subgroup.center (L32A.cStar K))

@[expose] def Thm14_7_40_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (L32A.cStar K ⧸ Subgroup.center (L32A.cStar K)) →
        quasithinO2QuotientIso H (Equiv.Perm (Fin 5)) ∧
          L32A.IsL24Section K (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) K)

@[expose] def Lemma14_7_47_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, L32A.l1 T L V ≤ K ∧
      ((∃ n : ℕ, IsPSL n 2 1 (L32A.cStar K)) ∨ (∃ n : ℕ, IsAlt n (L32A.cStar K)) ∨
        IsPSU 3 3 1 (L32A.cStar K))

@[expose] def Lemma14_7_48_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∃ K : Subgroup G, cComp H = {K} ∧ H = K ⊔ T ∧ conjClosure V H = ⁅conjClosure V H, K⁆

@[expose] def Thm14_7_52_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ T ∧ H = A6.g1 T V ∧
      (∀ H' : Subgroup G, Setting147 G T L V H' → H' = H) ∧ conjClosure V H = fsuU T V ∧
      (IsAlt 5 (L32A.cStar K) ∨ IsPSU 3 3 1 (L32A.cStar K))

@[expose] def Thm14_7_53_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ IsPSU 3 3 1 (L32A.cStar K)

end CFSG.Quasithin.H13
