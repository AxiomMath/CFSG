module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Strong

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo SmallRankCover smallRankR smallRankD
  smallRankIsQ8D8 Lemma628Concl Lemma629Concl Lemma630Iii)

@[expose] def S62Prop65 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        p = 5 → smallRankIsQ8D8 (smallRankR x z T) →
          ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) →
            Nat.Coprime p (Nat.card F) → Odd (Nat.card F) → normalizer (F : Set G) ≤ M

@[expose] def S62L630Iii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → Prop614At M x z →
      ∀ T : Subgroup G, SmallRankSylowTwo P M T → SmallRankCover p M x →
        Lemma628Concl p M x z T → ∀ f : ℕ, f.Prime → f ≠ 2 → pCoreOf f (smallRankD p x) ≠ ⊥ →
          Lemma629Concl p M x z T f → Lemma630Iii p f x

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
