module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.RankThreeUC.ClauseCTI
public import CFSG.Quasithin.Background.E1Sections

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.E1 (IsCompositionFactor)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Lists

variable {G : Type} [Group G]

@[expose] def Asc1930ListA (L : Type) [Group L] : Prop :=
  ∃ n : ℕ, Odd n ∧ 1 < n ∧
    (LieModel L .PSL 2 2 n ∨ LieModel L .PSL 3 2 n ∨ LieModel L .twistedB2 0 2 n)

@[expose] def Asc1930ListB (L : Type) [Group L] : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m n : ℕ), 2 < n ∧ LieModel L t m 2 n) ∨
    LieModel L .trialityD4 0 2 1 ∨ LieModel L .trialityD4 0 2 2 ∨
    LieModel L .PSU 4 2 2 ∨ LieModel L .PSU 5 2 2 ∨ LieModel L .POmegaMinus 4 2 2 ∨
    Nonempty (L ≃* alternatingGroup (Fin 9))

theorem listA_le_listB (L : Type) [Group L] (h : Asc1930ListA L) : Asc1930ListB L := by
  obtain ⟨n, ⟨k, rfl⟩, hn, h | h | h⟩ := h
  · exact Or.inl ⟨.PSL, 2, 2 * k + 1, by omega, h⟩
  · exact Or.inl ⟨.PSL, 3, 2 * k + 1, by omega, h⟩
  · exact Or.inl ⟨.twistedB2, 0, 2 * k + 1, by omega, h⟩

@[expose] def Asc1930HasA (H : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Group L), IsCompositionFactor ↥H L ∧ Asc1930ListA L

@[expose] def Asc1930HasB (H : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Group L), IsCompositionFactor ↥H L ∧ Asc1930ListB L

@[expose] def Asc1930 (M H : Subgroup G) : Prop :=
  Asc1930HasB H ∧ (IsStronglyPEmbedded 3 M → Asc1930HasA H)

@[expose] def Hyp124 (M H : Subgroup G) : Prop :=
  ¬ Asc1930HasA H ∧ (¬ IsStronglyPEmbedded 3 M → ¬ Asc1930HasB H)

theorem asc1930_iff_not_hyp124 (M H : Subgroup G) : Asc1930 M H ↔ ¬ Hyp124 M H := by
  classical
  unfold Asc1930 Hyp124
  constructor
  · rintro ⟨hB, hA⟩ ⟨hnA, hnB⟩
    by_cases hs : IsStronglyPEmbedded 3 M
    · exact hnA (hA hs)
    · exact hnB hs hB
  · intro h
    by_cases hA : Asc1930HasA H
    · obtain ⟨L, _, hL, hLA⟩ := hA
      exact ⟨⟨L, inferInstance, hL, listA_le_listB L hLA⟩, fun _ => ⟨L, inferInstance, hL, hLA⟩⟩
    · by_cases hs : IsStronglyPEmbedded 3 M
      · exact absurd ⟨hA, fun hn => absurd hs hn⟩ h
      · by_cases hB : Asc1930HasB H
        · exact ⟨hB, fun hs' => absurd hs' hs⟩
        · exact absurd ⟨hA, fun _ => hB⟩ h

end Lists

section MSigma

variable {G : Type} [Group G] [Finite G]

@[expose] def SigmaTwo (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p ∈ rankThreeSigmaA G ∧
    ∃ (P : Sylow p G) (M : Subgroup G), IsWitness p P M ∧ rankThreeClauseB M (P : Subgroup G) p

@[expose] def SigmaChoice (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (3 ∈ rankThreeSigmaA G → p = 3) ∧
    (3 ∉ rankThreeSigmaA G → (∃ q, SigmaTwo G q) → SigmaTwo G p)

@[expose] def Setup.InMSigma (S : Setup G) : Prop :=
  SigmaChoice G S.p

theorem exists_sigmaChoice (hS : Standing G) : ∃ p ∈ rankThreeSigmaA G, SigmaChoice G p := by
  by_cases h3 : 3 ∈ rankThreeSigmaA G
  · exact ⟨3, h3, fun _ => rfl, fun h => absurd h3 h⟩
  by_cases hq : ∃ q, SigmaTwo G q
  · obtain ⟨q, hq'⟩ := hq
    exact ⟨q, hq'.1, fun h => absurd h h3, fun _ _ => hq'⟩
  · obtain ⟨p, hp⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_nonempty_of_evenRank_three hS.rank
    exact ⟨p, hp, fun h => absurd h h3, fun _ h => absurd h hq⟩

end MSigma

section Stages

variable {G : Type} [Group G] [Finite G]

@[expose] def SmallNH1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → ∀ H ∈ hSet S.T S.M, Asc1930 S.M H

@[expose] def NotTIStage1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T)

@[expose] def TIUCoreEq1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
      uCore S.M S.T = CFSG.RankThree.PartOne.omegaOneCenterIn S.T

@[expose] def TIUNoncyclic (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) → ¬ IsCyclic (uCore S.M S.T)

@[expose] def TIStageNotClauseC1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
      ¬ (S.p = 3 ∧ rankThreeClauseC S.M (S.P : Subgroup G)) → False

@[expose] def TIStage1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) → False

@[expose] def LargeNH1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) → False

@[expose] def UniquenessStageB1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → False

theorem tiStage1930_of_parts (hS : Standing G) (hU : TIUCoreEq1930 G) (hZ : TIUNoncyclic G)
    (h : TIStageNotClauseC1930 G) : TIStage1930 G := by
  intro hUC S hMS hsmall hTI
  by_cases hc : S.p = 3 ∧ rankThreeClauseC S.M (S.P : Subgroup G)
  · have hUZ := hU hUC S hMS hsmall hTI
    have hZnc : ¬ IsCyclic (CFSG.RankThree.PartOne.omegaOneCenterIn S.T) :=
      hUZ ▸ hZ hUC S hMS hsmall hTI
    obtain ⟨h3, hcl⟩ := hc
    cases S with
    | mk p hp P M w T hsM hsG hnl hnc hne V hle hln hea hnti =>
      simp only at h3 hcl hUZ hZnc
      subst h3
      have hZM : M ≤ normalizer
          ((CFSG.RankThree.PartOne.omegaOneCenterIn T : Subgroup G) : Set G) := by
        rw [← hUZ]
        exact le_normalizer_uCore M T
      exact w.false_of_clauseC_of_normal_omegaOneCenter hS hUC hp hcl hsM hZM hZnc
  · exact h hUC S hMS hsmall hTI hc

theorem parts_of_tiStage1930 (h : TIStage1930 G) :
    TIUCoreEq1930 G ∧ TIUNoncyclic G ∧ TIStageNotClauseC1930 G :=
  ⟨fun hUC S hMS hsmall hTI => (h hUC S hMS hsmall hTI).elim,
    fun hUC S hMS hsmall hTI => (h hUC S hMS hsmall hTI).elim,
    fun hUC S hMS hsmall hTI _ => h hUC S hMS hsmall hTI⟩

theorem largeNH1930_of_stages (h1 : NotTIStage1930 G) (h2 : TIStage1930 G) : LargeNH1930 G :=
  fun hUC S hMS hsmall => h2 hUC S hMS hsmall (h1 hUC S hMS hsmall)

theorem uniquenessStageB_of_small_large1930 (h1 : SmallNH1930 G) (h2 : LargeNH1930 G) :
    UniquenessStageB1930 G :=
  fun hUC S hMS => h2 hUC S hMS (h1 hUC S hMS)

theorem not_rankThreeUC_of_inputs1930 (hS : Standing G) (hcat : CatalogNoUC G)
    (hD : AGL81TheoremD G) (hPU : CFSG.RankThree.PartOne.PushingUpCorollary)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) (hB : UniquenessStageB1930 G) :
    ¬ rankThreeUC G := by
  intro hUC
  by_cases hC : CFSG.Blueprint.Catalog G
  · exact hcat hS hC hUC
  have := hS.simple
  obtain ⟨p, hp, hpc⟩ := exists_sigmaChoice hS
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hN := hD hUC p hp P M hw T hT
  have hTG := isSylowOf_top_of_normalizer_le hT hN
  obtain ⟨V, hVM, hMV, hVe, hVTI⟩ := exists_not_isTI hS hGF hC hw.maxLocal
  have hH := exists_mem_hSet_of_pushingUp hS hPU hw.maxLocal hT
  exact hB hUC ⟨p, hp, P, M, hw, T, hT, hTG, hN, hC, hH, V, hVM, hMV, hVe, hVTI⟩ hpc

end Stages

end CFSG.LocalAnalysis.RankThreeUC
