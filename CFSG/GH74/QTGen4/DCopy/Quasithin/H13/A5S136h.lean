module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5S136h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def List1367_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
      CFSG.IsQuasisimple ↥(S.plus K) ∧ B56QuasisimpleList ↥(S.plus K)

@[expose] def Lemma13618_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13618Four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13619_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ n → Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Open.quasithinG2 F))

end CFSG.Quasithin.H13.A5
