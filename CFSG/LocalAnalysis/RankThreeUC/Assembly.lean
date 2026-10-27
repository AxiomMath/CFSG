module

public import CFSG.LocalAnalysis.RankThreeUC.ReducedModule
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.RankThree.PartOne.S12.SectionalRank
import CFSG.RankThree.PartOne.LIT.KFCGTList
import CFSG.GH74.EvenRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81TheoremD (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsWitness p P M → ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M →
      normalizer (T : Set G) ≤ M

theorem IsWitness.normalizer_le_of_characteristic {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) {T C : Subgroup G} (hT : IsPGroup 2 T) (hCT : C ≤ T)
    (hC : (C.subgroupOf T).Characteristic) (hC1 : C ≠ ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (C : Set G))) : normalizer (T : Set G) ≤ M := by
  have hCM : normalizer (C : Set G) ≤ M :=
    hw.u2 _ ⟨C, hC1, hT.to_le hCT, rfl⟩ (by rwa [inf_comm])
  exact (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic hCT hC).trans
    hCM

@[expose] def AGL81TheoremC (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsWitness p P M → ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ M → IsPGroup q Q →
      2 ≤ CFSG.Open.pRank q Q → rankThreeGamma 1 q Q ≤ M →
        ∀ H : Subgroup G, IsTwoLocal H → Q ≤ H → H ≤ M

@[expose] def cgtCore (T : Subgroup G) : Subgroup G :=
  ⨆ (C : Subgroup G) (_ : C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic),
    normalizer (C : Set G)

@[expose] def GlobalCGTRankBound (G : Type) [Group G] [Finite G] : Prop :=
  ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → cgtCore T ≠ ⊤ → evenRank G ≤ 2

@[expose] def CatalogNoUC (G : Type) [Group G] [Finite G] : Prop :=
  Standing G → CFSG.Blueprint.Catalog G → ¬ rankThreeUC G

@[expose] def hSet (T M : Subgroup G) : Set (Subgroup G) :=
  {H | T ≤ H ∧ ¬ H ≤ M ∧ H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H}

structure Setup (G : Type) [Group G] [Finite G] where
  p : ℕ
  hp : p ∈ rankThreeSigmaA G
  P : Sylow p G
  M : Subgroup G
  witness : IsWitness p P M
  T : Subgroup G
  sylowM : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylowG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤
  normalizer_le : normalizer (T : Set G) ≤ M
  notCatalog : ¬ CFSG.Blueprint.Catalog G
  hSet_nonempty : (hSet T M).Nonempty
  V : Subgroup G
  le : V ≤ M
  le_normalizer : M ≤ normalizer (V : Set G)
  elemAbelian : IsElemAbelian 2 V
  not_isTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V

@[expose] def UniquenessStageB (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → Setup G → False

open Classical in
@[expose] noncomputable def kParam (M : Subgroup G) : ℕ :=
  if CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M then 1 else 2

@[expose] def SmallNH (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, ∀ H ∈ hSet S.T S.M,
    (kParam S.M : ℕ∞) < CFSG.Quasithin.E1.nParam H

@[expose] def LargeNH (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G,
    (∀ H ∈ hSet S.T S.M, (kParam S.M : ℕ∞) < CFSG.Quasithin.E1.nParam H) → False

@[expose] def uCore (M T : Subgroup G) : Subgroup G :=
  ⨆ m : M, (CFSG.RankThree.PartOne.omegaOneCenterIn T).map (MulAut.conj (m : G)).toMonoidHom

omit [Finite G] in
theorem omegaOneCenterIn_le_inf_centralizer (T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ T ⊓ centralizer (T : Set G) := fun _ hz =>
  ⟨(CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).1,
    mem_centralizer_iff.mpr (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1⟩

omit [Finite G] in
theorem le_normalizer_uCore (M T : Subgroup G) : M ≤ normalizer (uCore M T : Set G) :=
  le_normalizer_iSup_conj M _

theorem uCore_le_and_isElemAbelian (hchar : IsCharTwoType G) {M T : Subgroup G}
    (hM : IsTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    uCore M T ≤ pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ∧ IsElemAbelian 2 (uCore M T) := by
  have hX := omegaOneCenterIn_le_inf_centralizer T
  have hXe : IsElemAbelian 2 (CFSG.RankThree.PartOne.omegaOneCenterIn T) :=
    ⟨⟨⟨fun a b => Subtype.ext ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp
      b.2).2.1 a (hX a.2).1)⟩⟩,
      fun x hx => (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hx).2.2⟩
  exact ⟨iSup_conj_le_pCoreOf_inf_centralizer hchar hM hT (fun _ h => (hX h).1)
    (fun _ h => (hX h).2), isElemAbelian_iSup_conj hchar hM hT (fun _ h => (hX h).1)
    (fun _ h => (hX h).2) hXe⟩

@[expose] def NotTIStage (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G,
    (∀ H ∈ hSet S.T S.M, (kParam S.M : ℕ∞) < CFSG.Quasithin.E1.nParam H) →
      CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T)

@[expose] def TIStage (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G,
    (∀ H ∈ hSet S.T S.M, (kParam S.M : ℕ∞) < CFSG.Quasithin.E1.nParam H) →
      CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) → False

theorem largeNH_of_stages (h1 : NotTIStage G) (h2 : TIStage G) : LargeNH G :=
  fun hUC S hsmall => h2 hUC S hsmall (h1 hUC S hsmall)

theorem uniquenessStageB_of_small_large (h1 : SmallNH G) (h2 : LargeNH G) :
    UniquenessStageB G :=
  fun hUC S => h2 hUC S (h1 hUC S)

omit [Finite G] in
theorem le_normalizer_of_characteristic {C T : Subgroup G} (hCT : C ≤ T)
    (hC : (C.subgroupOf T).Characteristic) : T ≤ normalizer (C : Set G) :=
  (normal_subgroupOf_iff_le_normalizer hCT).mp inferInstance

theorem exists_mem_hSet (hS : Standing G) (hCGT : GlobalCGTRankBound G) {M T : Subgroup G}
    (hM : M ≠ ⊤) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : (hSet T M).Nonempty := by
  by_contra hempty
  have hcore : cgtCore T ≤ M := by
    refine iSup₂_le fun C hC => ?_
    by_contra hCM
    refine hempty ⟨normalizer (C : Set G), le_normalizer_of_characteristic hC.2.1 hC.2.2, hCM,
      hS.charTwo _ ⟨C, hC.1, hT.isPGroup.to_le hC.2.1, rfl⟩⟩
  have h2 := hCGT T hT fun htop => hM (top_le_iff.mp (htop ▸ hcore))
  have h3 := hS.rank
  omega

omit [Finite G] in
theorem le_centralizer_omegaOneCenterIn (T : Subgroup G) :
    T ≤ centralizer (CFSG.RankThree.PartOne.omegaOneCenterIn T : Set G) := fun t ht =>
  mem_centralizer_iff.mpr fun _ hz =>
    ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 t ht).symm

theorem exists_mem_hSet_of_pushingUp (hS : Standing G)
    (hPU : CFSG.RankThree.PartOne.PushingUpCorollary) {M T : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    (hSet T M).Nonempty := by
  have := hS.simple
  by_contra hempty
  have hMT : ∀ M' ∈ CFSG.maximalTwoLocalsContaining (T : Set G), M' ≤ M := by
    intro M' hM'
    by_contra hM'M
    exact hempty ⟨M', SetLike.coe_subset_coe.mp hM'.2, hM'M, hS.charTwo M' hM'.1.1⟩
  have hT' : CFSG.RankThree.PartOne.IsSylowOf 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hM.1 hT
  exact CFSG.RankThree.PartOne.pushing_up_contradiction hPU CFSG.RankThree.PartOne.kfCGTList
    (fun _ _ _ hchar hs =>
      CFSG.RankThree.PartOne.evenRank_le_two_of_sectionalTwoRankLEFour hchar hs)
    hS.kProper hS.charTwo hS.rank (twoLocal_ne_top hS.nonab M hM.1) hT' hT1
    (le_normalizer.trans
      (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_pushingUpS T))
    (le_centralizer_omegaOneCenterIn T) hMT hMT

omit [Finite G] in
theorem isMaximalTwoLocal_of_rankThreeIsMaxTwoLocal {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) : CFSG.IsMaximalTwoLocal M :=
  ⟨hM.1, fun H hMH hH => hMH.ne (hM.2 H hH hMH.le).symm⟩

theorem exists_not_isTI (hS : Standing G) (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) :
    ∃ V : Subgroup G, V ≤ M ∧ M ≤ normalizer (V : Set G) ∧ IsElemAbelian 2 V ∧
      ¬ CFSG.CGT.Timmesfeld75.IsTI V := by
  have := hS.simple
  obtain ⟨B, hB⟩ := (Set.toFinite {W : Subgroup G | W ≤ M ∧ M ≤ normalizer (W : Set G) ∧
    CFSG.Assembly.IsElemAbelian 2 W}).exists_maximal
      ⟨⊥, bot_le, (normalizer_eq_top_iff (H := (⊥ : Subgroup G)).mpr inferInstance).symm ▸ le_top,
        ⟨⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [mem_bot.mp hx, one_pow]⟩⟩
  refine ⟨B, hB.1.1, hB.1.2.1, hB.1.2.2, fun hTI => hcat ?_⟩
  have hK : CFSG.IsKProper G := CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hS.kProper)
  exact (hGF G hS.nonab hK (CFSG.GH74.isCharTwoType_iff.mp hS.charTwo) M
    (isMaximalTwoLocal_of_rankThreeIsMaxTwoLocal hM) B hB hTI).2

theorem not_rankThreeUC_of_inputs (hS : Standing G) (hcat : CatalogNoUC G)
    (hD : AGL81TheoremD G) (hPU : CFSG.RankThree.PartOne.PushingUpCorollary)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) (hB : UniquenessStageB G) :
    ¬ rankThreeUC G := by
  intro hUC
  by_cases hC : CFSG.Blueprint.Catalog G
  · exact hcat hS hC hUC
  have := hS.simple
  obtain ⟨p, hp⟩ := sigmaA_nonempty_of_evenRank_three hS.rank
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hN := hD hUC p hp P M hw T hT
  have hTG := isSylowOf_top_of_normalizer_le hT hN
  obtain ⟨V, hVM, hMV, hVe, hVTI⟩ := exists_not_isTI hS hGF hC hw.maxLocal
  have hH := exists_mem_hSet_of_pushingUp hS hPU hw.maxLocal hT
  exact hB hUC ⟨p, hp, P, M, hw, T, hT, hTG, hN, hC, hH, V, hVM, hMV, hVe, hVTI⟩

end CFSG.LocalAnalysis.RankThreeUC
