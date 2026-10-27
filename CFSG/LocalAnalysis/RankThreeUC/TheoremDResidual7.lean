module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual6
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThreeConstrained
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

@[expose] def U4Shape (p : ℕ) (M : Subgroup G) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .twistedA 3 q ∧ p ∣ q.card + 1) ∧
    Nonempty ((↥(CFSG.RankThree.PartOne.pElementSubgroup p M) ⧸
      CFSG.pCore 2 ↥(CFSG.RankThree.PartOne.pElementSubgroup p M)) ≃*
        (TauCeti.CFSGIndex.lie d).Group)

@[expose] def AGL81Residual7With (G : Type) [Group G] [Finite G] (S : ℕ → Subgroup G → Prop) :
    Prop :=
  rankThreeUC G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsWitness p P M → S p M → ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ CFSG.Open.thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)) →
      ¬ normalizer (T : Set G) ≤
        normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ T → ∃ n ∈ normalizer (T : Set G),
        CFSG.Open.pRank p
          (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) ≤ 1) →
      2 ≤ CFSG.Open.pRank p (thompsonCore M T) →
      2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) →
      rankThreeGamma 1 p (P : Subgroup G) ≤ M →
      normalizer (T : Set G) ≤ M

@[expose] def AGL81Residual7NoU4 (G : Type) [Group G] [Finite G] : Prop :=
  AGL81Residual7With G fun p M => ¬ U4Shape p M

@[expose] def AGL81Residual7U4 (G : Type) [Group G] [Finite G] : Prop :=
  AGL81Residual7With G U4Shape

@[expose] def AGL81Residual7WithGen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) (S : ℕ → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → S p M → ∀ T : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ CFSG.Open.thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)) →
      ¬ normalizer (T : Set G) ≤
        normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ T → ∃ n ∈ normalizer (T : Set G),
        CFSG.Open.pRank p
          (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) ≤ 1) →
      2 ≤ CFSG.Open.pRank p (thompsonCore M T) →
      2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) →
      rankThreeGamma 1 p (P : Subgroup G) ≤ M →
      normalizer (T : Set G) ≤ M

@[expose] def AGL81Residual7Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  AGL81Residual7WithGen G W fun _ _ => True

@[expose] def AGL81Residual7NoU4Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  AGL81Residual7WithGen G W fun p M => ¬ U4Shape p M

@[expose] def AGL81Residual7U4Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  AGL81Residual7WithGen G W U4Shape

theorem agl81Residual7With_iff_gen (S : ℕ → Subgroup G → Prop) :
    AGL81Residual7With G S ↔
      (rankThreeUC G → AGL81Residual7WithGen G (witnessThree G) S) := by
  constructor
  · intro hR hUC p P M hw hS' T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
    exact hR hUC p hw.1 P M hw.2 hS' T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  · intro h hUC p hp P M hw hS' T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
    exact h hUC p P M ⟨hp, hw⟩ hS' T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10

theorem agl81Residual7Gen_of_splitGen
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hN : AGL81Residual7NoU4Gen G W) (hU : AGL81Residual7U4Gen G W) :
    AGL81Residual7Gen G W := by
  intro p P M hw _ T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  by_cases hshape : U4Shape p M
  · exact hU p P M hw hshape T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  · exact hN p P M hw hshape T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10

theorem agl81Residual6Gen_of_residual7Gen (hHup : KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual7Gen G W) : AGL81Residual6Gen G W := by
  intro p P M hw T hT H1 H2 H3 H4 _ H6 H7 H8 H9 H10 _
  obtain ⟨hp, hw'⟩ := hW p P M hw
  by_cases hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T))
  · exact hw'.normalizer_le_of_threeConstrained hHup hI59 hX hS hp hT H2 hcon
  · exact hR p P M hw trivial T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10

theorem agl81Residual6Gen_of_splitGen (hHup : KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hN : AGL81Residual7NoU4Gen G W) (hU : AGL81Residual7U4Gen G W) :
    AGL81Residual6Gen G W :=
  agl81Residual6Gen_of_residual7Gen hHup hI59 hX hS hW
    (agl81Residual7Gen_of_splitGen hN hU)

theorem agl81TheoremDGen_of_splitGen (hHup : KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hN : AGL81Residual7NoU4Gen G W) (hU : AGL81Residual7U4Gen G W) :
    AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_residual6Gen hS hW
    (agl81Residual6Gen_of_splitGen hHup hI59 hX hS hW hN hU)

theorem agl81TheoremD_of_split (hHup : KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hX : CFSG.LocalAnalysis.RankThreeTheoremC.Setting G →
      CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hS : Standing G) (hN : AGL81Residual7NoU4 G) (hU : AGL81Residual7U4 G) :
    AGL81TheoremD G :=
  (agl81TheoremD_iff_gen).mpr fun hUC =>
    agl81TheoremDGen_of_splitGen hHup hI59 (hX (setting_of_rankThreeUC hS hUC)) hS.toGen
      (witnessThree_spec hS)
      ((agl81Residual7With_iff_gen (S := fun p M => ¬ U4Shape p M)).mp hN hUC)
      ((agl81Residual7With_iff_gen (S := U4Shape)).mp hU hUC)

theorem agl81Residual7U4Gen_of_forall_not_u4Shape
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (h : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ¬ U4Shape p M) :
    AGL81Residual7U4Gen G W := by
  intro p P M hw hshape
  exact (h p P M hw hshape).elim

theorem agl81TheoremDGen_of_noU4Gen (hHup : KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hU : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ¬ U4Shape p M)
    (hN : AGL81Residual7NoU4Gen G W) : AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_splitGen hHup hI59 hX hS hW hN
    (agl81Residual7U4Gen_of_forall_not_u4Shape hU)

end CFSG.LocalAnalysis.RankThreeUC
