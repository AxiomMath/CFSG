module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2

namespace OuterFourAux

@[expose] def IsUEightIndex : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => IsTwoPow q 3 ∧ (r = 2 ∨ r = 5)
  | .twistedE6 q => IsTwoPow q 3
  | _ => False

@[expose] def IsD4EightIndex : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ IsTwoPow q 3
  | _ => False

theorem fourIndex_iff (d : TauCeti.LieTypeIndex) :
    FourIndex d ↔ IsUEightIndex d ∨ IsD4EightIndex d := by
  cases d <;> simp [FourIndex, IsUEightIndex, IsD4EightIndex]

theorem characteristic_of_fourIndex {d : TauCeti.LieTypeIndex} (h : FourIndex d) :
    d.characteristic = 2 := by
  rcases (fourIndex_iff d).1 h with h | h
  · cases d with
    | twistedA r q =>
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact h.1.1
    | twistedE6 q =>
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact h.1
    | _ => simp [IsUEightIndex] at h
  · cases d with
    | D r q =>
      rw [TauCeti.LieTypeIndex.characteristic_D]
      exact h.2.1
    | _ => simp [IsD4EightIndex] at h

theorem not_isD2Exception_of_fourIndex {d : TauCeti.LieTypeIndex} (h : FourIndex d) :
    ¬ IsD2SeitzException 3 d := by
  intro hexc
  rcases (fourIndex_iff d).1 h with h | h <;> cases d <;>
    simp_all [IsD2SeitzException, IsUEightIndex, IsD4EightIndex]

@[expose] def IsTrialityAutS (IsGraphAutS : ∀ (S : Type) [Group S], MulAut S → Prop)
    (S : Type) [Group S] (φ : MulAut S) : Prop :=
  φ ^ 3 = 1 ∧ IsGraphAutS S φ

theorem isSCp_sup_of_top {X : Type} [Group X] {p : ℕ} {B : Subgroup X} (K : Subgroup X)
    (h : IsSCp p ⊤ B) : IsSCp p (K ⊔ B) B :=
  ⟨le_sup_right, h.2.1, fun E _ hE hBE => h.2.2 E le_top hE hBE⟩

@[expose] def Seitz2310FourFree (IsFieldAutS : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → FourIndex d.1 →
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
        (∀ φ ∈ E, ¬ IsFieldAutS S φ) → CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

@[expose] def Bal209FourU (IsFieldAutS : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K IsUEightIndex →
        (∃ φ ∈ autImage B K, IsFieldAutS (↥K ⧸ Subgroup.center ↥K) φ) →
          IsStronglyBalancedIn 3 B K

@[expose] def Bal207D4 (IsGraphAutS : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      IsLieQuot ↥K IsD4EightIndex →
        (∀ φ ∈ autImage B K, ¬ IsTrialityAutS IsGraphAutS (↥K ⧸ Subgroup.center ↥K) φ) →
          IsStronglyBalancedIn 3 B K

@[expose] def Bal2010D4 (IsGraphAutS IsFieldAutS : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 (K ⊔ B) B → B ≤ Subgroup.normalizer (K : Set X) →
      IsLieQuot ↥K IsD4EightIndex →
        (∃ φ ∈ autImage B K, IsGraphAutS (↥K ⧸ Subgroup.center ↥K) φ) →
          (∃ φ ∈ autImage B K, IsFieldAutS (↥K ⧸ Subgroup.center ↥K) φ) →
            IsStronglyBalancedIn 3 B K

end OuterFourAux

open OuterFourAux in
theorem chevQOuterFour_of_inputs
    (IsFieldAutS : ∀ (S : Type) [Group S], MulAut S → Prop)
    (IsGraphAutS : ∀ (S : Type) [Group S], MulAut S → Prop)
    (hS2 : KFactSeitzRankTwo) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS3 : Seitz2310FourFree IsFieldAutS) (h209 : Bal209FourU IsFieldAutS)
    (h207 : Bal207D4 IsGraphAutS) (h2010 : Bal2010D4 IsGraphAutS IsFieldAutS) :
    ChevQOuterFour := by
  classical
  intro X _ _ hXK K B hH hNorm hLie _
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := hNorm.1
  have hBel : CFSG.Open.IsElemAbelian 3 B := hH.scp.2.1
  have hKc : CFSG.Open.IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  obtain ⟨d, hd, ⟨e⟩⟩ := hLie
  by_cases hF : ∃ φ ∈ autImage B K, IsFieldAutS (↥K ⧸ Subgroup.center ↥K) φ
  ·
    rcases (fourIndex_iff d.1).1 hd with hU | hD
    · exact Or.inr (h209 X hXK K B hKc hH.scp hBN hH.rank_local ⟨d, hU, ⟨e⟩⟩ hF)
    · by_cases hT : ∃ φ ∈ autImage B K, IsTrialityAutS IsGraphAutS (↥K ⧸ Subgroup.center ↥K) φ
      · obtain ⟨φ, hφ, hG⟩ := hT
        exact Or.inr (h2010 X hXK K B hKc (isSCp_sup_of_top K hH.scp) hBN ⟨d, hD, ⟨e⟩⟩
          ⟨φ, hφ, hG.2⟩ hF)
      · simp only [not_exists, not_and] at hT
        exact Or.inr (h207 X hXK K B hKc hH.scp hBN ⟨d, hD, ⟨e⟩⟩ hT)
  ·
    simp only [not_exists, not_and] at hF
    by_cases hc3 : 3 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X))
    · exact Or.inl ⟨hH.rank_four, isInGOne_of_centralizing hBN inf_le_left inf_le_right hc3⟩
    have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
    have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
    have hdp : (3 : ℕ) ≠ d.1.characteristic := by
      rw [OuterFourAux.characteristic_of_fourIndex hd]
      norm_num
    have hZ : CFSG.Open.pRank 3 (Subgroup.center ↥K) ≤ 1 :=
      center64_of_griess hGA 3 hH.prime hH.odd ↥K hq hOK d ⟨e⟩ hdp
    have hc1 : 1 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
      one_le_pRank_centralizer hH.prime hBel hH.centralized
    by_cases hc2 : 2 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X))
    · exact Or.inl (caseA_of_plane hS2 hH hNorm hc2 hZ d e hdp
        (OuterFourAux.not_isD2Exception_of_fourIndex hd))
    have hc : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 1 := by omega
    exact Or.inl (caseA_of_cube hH hBN hc hZ fun E hEA hEel hEcard =>
      hS3 (↥K ⧸ Subgroup.center ↥K) d ⟨e⟩ hd E hEel hEcard fun φ hφ => hF φ (hEA hφ))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
