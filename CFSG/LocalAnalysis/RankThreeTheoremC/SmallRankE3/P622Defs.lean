module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Delta
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622KFactD S622IsSimpleSection)

@[expose] def P622Prop614At {G : Type} [Group G] (M : Subgroup G) (x z : G) : Prop :=
  ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H →
    (∃ S : Subgroup G, S ≤ H ⊓ M ∧ IsPGroup 2 S ∧ S ≠ ⊥ ∧
      zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) → H ≤ M

@[expose] def P622KFactDThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (D V M₀ : Subgroup A) (z : A),
    CFSG.Open.IsKGroup ↥D → orderOf z = 3 → z ∈ normalizer (D : Set A) →
    ¬ 3 ∣ Nat.card D → CFSG.ABGLocalTools.IsSylowOf 2 V D → z ∈ normalizer (V : Set A) →
    M₀ ≤ D →
    (∀ U : Subgroup A, U ≤ V → U ≠ ⊥ → z ∈ normalizer (U : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    centralizer ({z} : Set A) ⊓ D ≤ M₀ →
    (∀ U : Subgroup A, U ≤ D → IsPGroup 2 U → U ≠ ⊥ → U ≤ centralizer ({z} : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    D ≤ M₀ ⊔ rankThreePrimeCore 2 D

@[expose] def P622KFactD : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (D V M₀ : Subgroup A) (z : A),
    p.Prime → p ≠ 2 → CFSG.Open.IsKGroup ↥D → orderOf z = p → z ∈ normalizer (D : Set A) →
    ¬ p ∣ Nat.card D → CFSG.ABGLocalTools.IsSylowOf 2 V D → z ∈ normalizer (V : Set A) →
    M₀ ≤ D →
    (∀ U : Subgroup A, U ≤ V → U ≠ ⊥ → z ∈ normalizer (U : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    centralizer ({z} : Set A) ⊓ D ≤ M₀ →
    (∀ U : Subgroup A, U ≤ D → IsPGroup 2 U → U ≠ ⊥ → U ≤ centralizer ({z} : Set A) →
      normalizer (U : Set A) ⊓ D ≤ M₀) →
    D ≤ M₀ ⊔ rankThreePrimeCore 2 D

theorem p622KFactD_of_three_five (h3 : P622KFactDThree) (h5 : S622KFactD) : P622KFactD := by
  intro A _ _ p D V M₀ z hp hp2 hD hz hzD hpD hV hzV hM hU hC hU2
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 A D V M₀ z hD hz hzD hpD hV hzV hM hU hC hU2
  · have h5p : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      omega
    exact h5 A p D V M₀ z hp h5p hD hz hzD hpD hV hzV hM hU hC hU2

@[expose] def P622CaseDelta4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ¬ HasPrimeConstraint (G := M) 3 → SmallRankCaseDelta3 P M →
          CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G))

@[expose] def P622Lemma62Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        HasPrimeConstraint (G := M) 3 ∨ CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G))

theorem p622Lemma62Three_of_delta4 (hL62 : ∀ (G : Type) [Group G] [Finite G],
    GL83SmallRankLemma62At3 G) (h4 : P622CaseDelta4) : P622Lemma62Three := by
  intro G _ _ hS hD1 hD2 hU0 P M hsit x z hx hz
  by_cases hα : HasPrimeConstraint (G := M) 3
  · exact Or.inl hα
  · rcases hL62 G hS hU0 P M hsit x z hx hz with h | hδ
    · exact absurd h hα
    · exact Or.inr (h4 G hS hD1 hD2 hU0 P M hsit x z hx hz hα hδ)

@[expose] def P622Prop65Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (p : ℕ), p ≠ 3 → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
          ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
            zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def P622Prop65 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)) →
        ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def P622Kx : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → TheoremD2 G → FullCoreLocal G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T S : Subgroup G),
      Prop627Failure G p P M x z T → P622Prop614At M x z →
      IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) S →
      smallRankS x T ≤ S → rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥ →
      ∀ L : Subgroup G, S622IsSimpleSection L ⊥ → L ≤ centralizer ({x} : Set G) → z ∈ L →
        CFSG.Open.pRank p L ≤ 1 → ¬ L ≤ M →
        centralizer ({x} : Set G) ≤ normalizer (L : Set G) → False

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
