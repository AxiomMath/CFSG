module

public import CFSG.HardMathSupport.Solomon.Coordinator.AlphaEngine
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

@[expose] def AlphaGenHyp (p k : ℕ) (A : Subgroup G) : Prop :=
  ∀ D₀ : Subgroup G, IsEkIn p k A D₀ → ∀ E : Subgroup G, IsEkIn p (k + 1) A E →
    ⁅GLADelta p D₀, E⁆ ≤ ⨆ (D : Subgroup G) (_ : IsEkIn p k E D),
      ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (D : Set G), E⁆

@[expose] def AlphaGenHypAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, IsBOneMax p B → AlphaGenHyp p 2 B

@[expose] def CaseTwoFiveEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → p = 5 → 5 ≤ m →
    ¬ GLCaseOne G p → ∀ B : Subgroup G, IsBOneMax p B →
      ∃ D : Subgroup G, IsEkIn p 2 B D ∧ Even (Nat.card (⁅GLADelta p D, B⁆ : Subgroup G))

@[expose] def Prop42CaseThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p → GLCaseThree G p →
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀

theorem lambdaStarGroup_eq_psiStarGroup_of_five_le (h31 : Lemma31) {m p : ℕ}
    (hS : GLStanding G m p) (hm5 : 5 ≤ m) {B : Subgroup G} (hB : GLAIsBmax p B)
    (hsc : IsSCp p ⊤ B) : lambdaStarGroup p B = psiStarGroup p B := by
  have hr := hS.rank_eq
  have hL : ∀ b, lambdaLOf p B b = ⊥ := fun b => le_bot_iff.1 (sSup_le fun L hL => by
    obtain ⟨hp3, h4, -⟩ := hL.2.2
    subst hp3
    omega)
  have hON : ∀ b, lambdaONOf p B b = ⊥ := fun b => le_bot_iff.1 (sSup_le fun L hL => by
    obtain ⟨hp3, h4, -⟩ := hL.2.2
    subst hp3
    omega)
  have hM : ∀ b, lambdaMOf p B b = ⊥ := fun b => le_bot_iff.1 (sSup_le fun L hL => by
    obtain ⟨hp5, h4, -⟩ := hL.2.2
    subst hp5
    omega)
  unfold lambdaStarGroup psiStarGroup
  refine iSup_congr fun b => iSup_congr fun hb => iSup_congr fun hb1 => ?_
  unfold lambdaStar psiStar
  rw [lambdaOf_eq_of_lemma31 h31 hS hB hsc hb hb1, hL, hON, hM]
  simp

theorem isSCp_of_isBOneMax {m p : ℕ} (hS : GLStanding G m p) {B : Subgroup G}
    (hB : IsBOneMax p B) : IsSCp p ⊤ B :=
  lemma23_proved G m p hS B hB

theorem exists_preUniquenessSubgroup_of_caseTwo_three (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h21 : Prop21) (h22 : Prop22)
    (h31 : Lemma31) (hgen : AlphaGenHypAll) {m p : ℕ} (hS : GLStanding G m p) (hp3 : p = 3)
    (hm5 : 5 ≤ m) :
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀ := by
  obtain ⟨B, hB0, hwb⟩ := h22 G m p hS
  have hB1 : IsBOneMax p B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by omega) hB0
  have hbal := (h21 G m p hS B hB1.1).1
  have hΛ := lambdaStarGroup_eq_psiStarGroup_of_five_le h31 hS hm5 hB1.1 (isSCp_of_isBOneMax hS hB1)
  obtain ⟨-, D, hDB, hDpl, -, hD3⟩ := hB0
  refine ⟨B, hB1, exists_preUniquenessSubgroup_of_alphaE hSF hbridge hS hB1 hbal hwb
    (hgen G m p hS B hB1) hΛ ⟨D, ⟨hDB, hDpl.1, hDpl.2⟩, hD3 hp3⟩⟩

theorem exists_preUniquenessSubgroup_of_caseTwo_five (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h21 : Prop21) (h22 : Prop22)
    (h31 : Lemma31) (hgen : AlphaGenHypAll) (h45 : CaseTwoFiveEven) {m p : ℕ}
    (hS : GLStanding G m p) (hII : GLCaseTwo G p) (hp5 : p = 5) :
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀ := by
  obtain ⟨-, hm5, hnI⟩ := hII
  have hm5' : 5 ≤ m := hS.rank_eq ▸ hm5
  obtain ⟨B, hB0, hwb⟩ := h22 G m p hS
  have hB1 : IsBOneMax p B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by omega) hB0
  have hbal := (h21 G m p hS B hB1.1).1
  have hΛ :=
    lambdaStarGroup_eq_psiStarGroup_of_five_le h31 hS hm5' hB1.1 (isSCp_of_isBOneMax hS hB1)
  exact ⟨B, hB1, exists_preUniquenessSubgroup_of_alphaE hSF hbridge hS hB1 hbal hwb
    (hgen G m p hS B hB1) hΛ (h45 G m p hS hp5 hm5' hnI B hB1)⟩

theorem prop42_of_inputs (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) (h21 : Prop21) (h22 : Prop22)
    (h31 : Lemma31) (hgen : AlphaGenHypAll) (h45 : CaseTwoFiveEven) (hIII : Prop42CaseThree) :
    Prop42 := by
  intro G _ _ m p hS hcase
  rcases hcase with hI | hII | hIII'
  · exact exists_preUniquenessSubgroup_of_caseOne hSF hbridge hS hI
  · have hp := hS.prime
    have hp2 := hS.ne_two
    have hp35 : p = 3 ∨ p = 5 := by
      have h2 := hp.two_le
      have h5 := hII.1
      interval_cases p
      · exact absurd rfl hp2
      · exact Or.inl rfl
      · exact absurd hp (by decide)
      · exact Or.inr rfl
    rcases hp35 with h3 | h5
    · exact exists_preUniquenessSubgroup_of_caseTwo_three hSF hbridge h21 h22 h31 hgen hS h3
        (hS.rank_eq ▸ hII.2.1)
    · exact exists_preUniquenessSubgroup_of_caseTwo_five hSF hbridge h21 h22 h31 hgen h45 hS hII h5
  · exact hIII G m p hS hIII'

end CFSG.HardMathSupport.Solomon.Coordinator
