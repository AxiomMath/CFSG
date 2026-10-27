module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def Thm14_5_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ Y V₂ : Subgroup G, A6.IsV2 T V V₂ → oTwoUpper Y = Y → Y ≤ A6.g1 T V →
      T ≤ Subgroup.normalizer (Y : Set G) →
      quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) →
      (Y ≤ Subgroup.normalizer (L : Set G) ∨ ⁅V₂, Y⁆ = ⊥) ∧
        ((Y : Set G) * (L32A.l1 T L V : Set G) = (L32A.l1 T L V : Set G) * (Y : Set G) →
          Y ≤ Subgroup.normalizer (L : Set G)) ∧
        (fsuV1 T V).relIndex (conjClosure V₂ Y) ≠ 8

@[expose] def Lemma14_5_19_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ K ≤ Subgroup.normalizer (L : Set G) ∧
      Setting147 G T L V (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T))

@[expose] def Lemma14_5_20_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ (Y : Subgroup G) (p : ℕ), p.Prime → Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) →
      (∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) →
      Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y ∨
        (p = 3 ∧ L32A.l1 T L V ≤ Y ∧
          ((L32A.l1 T L V ⊔ pCoreOf 2 Y = Y ∧
              H ≤ Subgroup.normalizer (L32A.l1 T L V : Set G)) ∨
            (IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) ∧
              L32A.l1 T L V = oTwoUpper (L32A.o2z Y) ∧
              L32A.l1 T L V = oTwoUpper (Y ⊓ Subgroup.normalizer (L : Set G)) ∧
              ∀ W : Subgroup G, L32A.l1 T L V ⊔ pCoreOf 2 Y ≤ W → W ≤ Y →
                T ≤ Subgroup.normalizer (W : Set G) →
                W = L32A.l1 T L V ⊔ pCoreOf 2 Y ∨ W = Y) ∨
            (IsElemAbelianOfRank 3 2 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) ∧
              ∃ Y₀ : Subgroup G, Y₀ ≤ H ∧ L32A.l1 T L V ≤ Y₀ ∧
                T ≤ Subgroup.normalizer (Y₀ : Set G) ∧
                Nonempty (↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀ ≃* Multiplicative (ZMod 9)) ∧
                ¬ Y₀ ≤ Subgroup.normalizer (L : Set G))))

end CFSG.Quasithin.H13
