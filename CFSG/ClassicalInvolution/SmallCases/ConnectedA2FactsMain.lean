module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsFrame
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Exact

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.SmallWeyl CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance

variable (p f : ℕ) [Fact p.Prime]

@[expose] def A2SingleClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A → ∀ a ∈ A, a ≠ 1 →
            ∀ D : LieSystemData p f (LocalQuot (conjClass K) a) (localFamily (conjClass K) a),
              SingleClassComponents p f D

@[expose] def A2NoG2D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A → ∀ a ∈ A, a ≠ 1 →
            ∀ D : LieSystemData p f (LocalQuot (conjClass K) a) (localFamily (conjClass K) a),
              ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4

@[expose] def A2PairTypes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A → ∀ K' ∈ S, ∀ L' ∈ S, K' ≠ L' → ¬ Commutes K' L' →
            LinearPair F A K' L' ∨ UnitaryPair (GaloisField p (2 * f)) p f A K' L'

@[expose] def A2InjectiveCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A →
          (∃ t ∈ A, t ≠ 1 ∧ ∀ M ∈ S, ∀ m ∈ M, m * t = t * m) →
          ∀ K' ∈ S, ∀ L' ∈ S, (∃ w, IsUniqueInvolution K' w ∧ IsUniqueInvolution L' w) →
            axisSub A K' = axisSub A L' → K' = L'

variable {p f}

theorem a2SingleClass_of_noG2D4 (h : A2NoG2D4 p f) : A2SingleClass p f :=
  fun G _ _ _ K z hb hD F _ hF A S Fr hcard hnc hP1 a ha ha1 D i =>
    RouteD.Gaps.fundamentalSingleClass_of_ne D i
      (h G K z hb hD F hF A S Fr hcard hnc hP1 a ha ha1 D i).1
      (h G K z hb hD F hF A S Fr hcard hnc hP1 a ha ha1 D i).2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem rankThreeFrameFacts_of_residuals {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hD : HasDatum p f K) (hP1 : A2P1 p f) (hS : A2SingleClass p f) (hT : A2PairTypes p f)
    (hI : A2InjectiveCentral p f) {F : Type} [Field F] (hF : Nat.card F = p ^ f)
    {A : Subgroup G} {S : Set (Subgroup G)} (Fr : RankFrame F (conjClass K) A S)
    (hcard8 : Nat.card A = 8) (hnc' : ∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L')
    (hP1A : FrameP1 (conjClass K) A) : RankThreeFrameFacts p f F (conjClass K) A S := by
  obtain ⟨K₁, h₁, K₂, h₂, hne, hnc⟩ := hnc'
  have hq := hb.five
  have hf : 0 < f := pos_of_five_le hq
  have : Finite F := Fr.finite
  have : IsMulCommutative ↥A := Fr.isMulCommutative
  have hex : ExactMembers (conjClass K) := exactMembers_of_inputs hb hD hP1
  have hfib : FibreLE2 S := fibreLE2_of_branch hb hex Fr hP1A
  have hconn : NonCommConnected S := nonCommConnected_of_card_eight hb hex Fr hP1A hcard8 h₁ h₂
    hne hnc
  have hK₀ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), pow_mul']
  have huniform := rankFrame_sign_constant_pairs Fr hconn hK₀ hF
    (hT G K z hb hD F hF A S Fr hcard8 ⟨K₁, h₁, K₂, h₂, hne, hnc⟩ hP1A)
  have hlinear : (∀ K' ∈ S, ∀ L' ∈ S, K' ≠ L' →
        Commutes K' L' ∨ LinearA2Pair F A K' L' ∨ LinearA2Pair F A L' K') ∨
      (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
        Commutes P Q ∨ UnitaryA2Pair (GaloisField p (2 * f)) p f A P Q ∨
          UnitaryA2Pair (GaloisField p (2 * f)) p f A Q P) := by
    rcases huniform with h | h
    · left
      intro K' hK' L' hL' hKL
      by_cases hc : Commutes K' L'
      · exact Or.inl hc
      · exact Or.inr (h K' hK' L' hL' hKL hc)
    · right
      intro K' hK' L' hL' hKL
      by_cases hc : Commutes K' L'
      · exact Or.inl hc
      · exact Or.inr (h K' hK' L' hL' hKL hc)
  have hA2 : A2Dichotomy A S := by
    rcases hlinear with hlin | hlinU
    · exact a2Dichotomy_of_rankFrame_linear Fr hlin
    · exact a2Dichotomy_of_rankFrame_unitary Fr hK₀ hlinU
  have hS' : S.Nonempty := ⟨K₁, h₁⟩
  have hinjF : ∀ K' ∈ S, ∀ L' ∈ S, (∃ w, IsUniqueInvolution K' w ∧ IsUniqueInvolution L' w) →
      axisSub A K' = axisSub A L' → K' = L' := by
    rcases dataFinset_card_three_or_six Fr hcard8 hS' hA2 hfib hconn h₁ h₂ hne hnc with hd3 | hd6
    · have hadj : (Fr.datum ⟨K₁, h₁⟩).Adj (Fr.datum ⟨K₂, h₂⟩) :=
        (Fr.datum_adj_iff_not_commutes hA2 hfib (fun h => hne (congrArg Subtype.val h))).mpr hnc
      exact hI G K z hb hD F hF A S Fr hcard8 ⟨K₁, h₁, K₂, h₂, hne, hnc⟩ hP1A
        (exists_ne_one_centralizes_of_card_three Fr hd3 hadj)
    · exact eq_of_datumInjective Fr
        (datumInjective_of_branch hb hex Fr hP1A hcard8 hS' hA2 hfib hconn hd6)
  refine ⟨hS G K z hb hD F hF A S Fr hcard8 ⟨K₁, h₁, K₂, h₂, hne, hnc⟩ hP1A, hfib, hinjF, ?_⟩
  rcases hlinear with hlin | hlinU
  · exact Or.inl hlin
  · exact Or.inr ⟨GaloisField p (2 * f), inferInstance, inferInstance, inferInstance, hK₀, hlinU⟩

variable (p f)

theorem a2FrameFacts_of_residuals (hP1 : A2P1 p f) (hS : A2SingleClass p f)
    (hT : A2PairTypes p f) (hI : A2InjectiveCentral p f) : A2FrameFacts p f :=
  fun _ _ _ _ _ _ hb hD _ _ hF _ _ Fr hcard8 hnc' hP1A =>
    rankThreeFrameFacts_of_residuals hb hD hP1 hS hT hI hF Fr hcard8 hnc' hP1A

end CFSG.ClassicalInvolution.ConnectedA2
