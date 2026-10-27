module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Stmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Lemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

open S1248

@[expose] def HypX1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    (∃ X : Subgroup G, X ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card X = 3 ∧
      ¬ X ≤ Subgroup.centralizer (U : Set G) ∧
      ∃ l ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (X : Set G),
        l ∉ Subgroup.normalizer (U : Set G) ∧ l ^ 2 ∈ Subgroup.normalizer (U : Set G)) ∨
    ∃ Y : Subgroup G, Y ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ Subgroup.centralizer (U : Set G) = ⊥

@[expose] def Comp1248Type_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ K : Subgroup G, QuasithinUnique.IsComponentIn K (Subgroup.centralizer (U : Set G)) →
      (¬ ∃ Y : Subgroup G, Y ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card Y = 27 ∧
        (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ Subgroup.centralizer (U : Set G) = ⊥) ∧
      IsSimpleGroup ↥K ∧
      (∃ p : ℕ, QuasithinUnique.Ch1.IsFermatOrMersennePrime p ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1) ∧
      ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ V ⊓ Subgroup.centralizer (K : Set G) = U

@[expose] def Comp1248Lift_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ X : Subgroup G, X ≤ L ⊓ Subgroup.normalizer (U : Set G) → Nat.card X = 3 →
      ¬ X ≤ Subgroup.centralizer (U : Set G) →
    ∀ l ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (X : Set G),
      l ∉ Subgroup.normalizer (U : Set G) → l ^ 2 ∈ Subgroup.normalizer (U : Set G) →
    ∀ K : Subgroup G, QuasithinUnique.IsComponentIn K (Subgroup.centralizer (U : Set G)) →
      (∃ p : ℕ, QuasithinUnique.Ch1.IsFermatOrMersennePrime p ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 p 1) →
      QuasithinUnique.IsComponentIn K
          (Subgroup.centralizer ((U ⊓ conjSubgroup U l : Subgroup G) : Set G)) ∧
        ∀ K' : Subgroup G, QuasithinUnique.IsComponentIn K'
            (Subgroup.centralizer ((U ⊓ conjSubgroup U l : Subgroup G) : Set G)) →
          3 ∣ Nat.card K' → K' = K

@[expose] def NoComp1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ K : Subgroup G, ¬ QuasithinUnique.IsComponentIn K (Subgroup.centralizer (U : Set G))

@[expose] def OddInv1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ z ∈ V ⊓ Subgroup.centralizer (L : Set G), z ≠ 1 →
      ∀ W : Subgroup G, (W = U ∨ (W ≤ U ∧ W.relIndex U = 2)) →
        ∀ x ∈ QuasithinUnique.oddCoreIn (Subgroup.centralizer (W : Set G)), z * x * z⁻¹ = x⁻¹

@[expose] def OddCentE1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ U₀ : Subgroup G, U₀ ≤ U → U₀.relIndex U = 2 →
      ∀ K₀ : Subgroup G, QuasithinUnique.IsComponentIn K₀
          (Subgroup.centralizer (U₀ : Set G)) →
        QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) ≤
          Subgroup.centralizer (K₀ : Set G)

@[expose] def OddCentQ1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ U₀ : Subgroup G, U₀ ≤ U → U₀.relIndex U = 2 →
      QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) ≤
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer (U₀ : Set G)) : Set G)

@[expose] def OddFinal1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    ∀ P : Subgroup G, P ≠ ⊥ → Odd (Nat.card P) → IsMulCommutative ↥P →
      Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (P : Set G) →
        V ≤ Subgroup.centralizer (P : Set G)

@[expose] def OddCore1248_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V U : Subgroup G), Setting G T L V U →
    QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) = ⊥

theorem charTwo1248_of_F4 (hNC : NoComp1248_F4) (hOC : OddCore1248_F4) : CharTwo1248_F4 := by
  intro G _ _ T L V hcx hq U hUV hidx hesc
  have hS : Setting G T L V U := ⟨hcx, hq, hUV, hidx, hesc⟩
  exact QuasithinUnique.DoubleA3.charTwo_of_no_component (hNC G T L V U hS)
    (hOC G T L V U hS)

end CFSG.Quasithin.H13
