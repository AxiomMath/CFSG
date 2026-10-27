module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PThree
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxEmb

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

@[expose] def KFact2401Spor : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) (s : TauCeti.SporadicName),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → 2 ≤ CFSG.Open.pRank 3 L →
    (∀ E : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 3 E L → ∀ J : Subgroup A,
      (∀ S₀ : Subgroup A, S₀ ≤ E → S₀ ≠ ⊥ → normalizer (S₀ : Set A) ⊓ L ≤ J) → L ≤ J) ∨
      s = .M11

@[expose] def KFactSporM11 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) →
    ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_normal {K V : Subgroup G} (hVK : V ≤ K) (hn : K ≤ normalizer (V : Set G))
    (hV : IsPGroup 2 V) : V ≤ pCoreOf 2 K := by
  haveI : (V.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hVK).mpr hn
  have hp : IsPGroup 2 (V.subgroupOf K) :=
    IsPGroup.of_equiv hV (Subgroup.subgroupOfEquivOfLe hVK).symm
  have h : V.subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨inferInstance, hp⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hVK]
  exact Subgroup.map_mono h

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem pCoreOf_inf_facts (c : KxCfg p P M x z T S L) :
    pCoreOf 2 (L ⊓ M) ≠ ⊥ ∧ ∃ y ∈ pCoreOf 2 (L ⊓ M), z * y ≠ y * z := by
  have hp := c.conf.config.prime
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le 2 M
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) := localGroup_le_normalizer_pCoreOf 2 M
  have hzM : z ∈ M := c.conf.config.B_le_M (mem_sup_right (mem_zpowers z))
  set Q₀ : Subgroup G := pCoreOf 2 M ⊓ centralizer ({x} : Set G) with hQ₀
  have hne : ⁅zpowers z, Q₀⁆ ≠ ⊥ := c.conf.config.commutator_pCoreOf_ne_bot
  have hQ₀2 : IsPGroup 2 Q₀ := hO2.to_le inf_le_left
  have hzQ₀ : z ∈ normalizer (Q₀ : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hMO hzM,
      Subgroup.le_normalizer c.conf.config.z_mem_centralizer⟩
  have hQ₀L : Q₀ ≤ normalizer (L : Set G) :=
    (le_inf (inf_le_left.trans hOM) inf_le_right).trans c.norm
  obtain ⟨y, hy, hzy⟩ := exists_not_commute_of_ne_bot hp c.conf.config.ne_two
    c.conf.config.central.pow_eq_one hQ₀2 hzQ₀ hne
  set U : Subgroup G := ⁅zpowers z, Q₀⁆ with hU
  have hUL : U ≤ L := commutator_zpowers_le_of_le_normalizer c.z_mem hQ₀L
  have hUO : U ≤ pCoreOf 2 M := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have haM : a ∈ M := (zpowers_le.mpr hzM) ha
    have hbO : b ∈ pCoreOf 2 M := hb.1
    rw [commutatorElement_def]
    have h1 : a * b * a⁻¹ ∈ pCoreOf 2 M := (mem_normalizer_iff.mp (hMO haM) b).mp hbO
    exact (pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hbO)
  have hVK : pCoreOf 2 M ⊓ L ≤ L ⊓ M := le_inf inf_le_right (inf_le_left.trans hOM)
  have hKV : L ⊓ M ≤ normalizer ((pCoreOf 2 M ⊓ L : Subgroup G) : Set G) := fun k hk =>
    inf_normalizer_le_normalizer_inf ⟨hMO hk.2, Subgroup.le_normalizer hk.1⟩
  have hV : pCoreOf 2 M ⊓ L ≤ pCoreOf 2 (L ⊓ M) :=
    le_pCoreOf_of_normal hVK hKV (hO2.to_le inf_le_left)
  have hUY : U ≤ pCoreOf 2 (L ⊓ M) := fun u hu => hV ⟨hUO hu, hUL hu⟩
  exact ⟨fun h => hne (le_bot_iff.mp (h ▸ hUY)), y, hUY hy, hzy⟩

theorem normalizer_pCoreOf_inf_eq (c : KxCfg p P M x z T S L) :
    normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) ⊓ L = L ⊓ M := by
  have hY2 : IsPGroup 2 (pCoreOf 2 (L ⊓ M)) := pCoreOf_isPGroup 2 (L ⊓ M)
  have hYK : pCoreOf 2 (L ⊓ M) ≤ L ⊓ M := pCoreOf_le 2 (L ⊓ M)
  have hKN : L ⊓ M ≤ normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (L ⊓ M)
  have hzK : z ∈ L ⊓ M := ⟨c.z_mem, c.conf.config.B_le_M (mem_sup_right (mem_zpowers z))⟩
  have hYne : pCoreOf 2 (L ⊓ M) ⊓ M ≠ ⊥ := by
    rw [inf_eq_left.mpr (hYK.trans inf_le_right)]
    exact c.pCoreOf_inf_facts.1
  have hNM : normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) ≤ M :=
    c.normalizer_le (hYK.trans inf_le_left) hY2 (hKN hzK) hYne
  exact le_antisymm (fun g hg => ⟨hg.2, hNM hg.1⟩) (le_inf hKN inf_le_left)

theorem localRank_three_le (h313 : GL83NormalElementaryRankFour) (h2401 : KFact2401Spor)
    (hM11 : KFactSporM11) (c : KxCfg p P M x z T S L) {s : TauCeti.SporadicName}
    (e : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h3 : 2 ≤ CFSG.Open.pRank 3 L) {U : Subgroup G} (hUL : U ≤ L) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) : CFSG.Open.pRank 3 (normalizer (U : Set G) ⊓ L) ≤ 3 := by
  by_contra hlt
  push Not at hlt
  have hU4 : 4 ≤ CFSG.Open.pRank 3 (normalizer (U : Set G) ⊓ L) := hlt
  by_cases hs : s = .M11
  · subst hs
    exact absurd (hM11 G L e U hUL hU1 hU2) (by omega)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := c.conf.config.situation
  have hrk : 4 ≤ CFSG.Open.pRank 3 (normalizer (U : Set G)) :=
    hU4.trans (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left)
  have hfdvd : 3 ∣ Nat.card G :=
    prime_dvd_card_of_pRank_pos 3 (normalizer (U : Set G)) (by omega)
  have h4 : 4 ≤ GLBTwoLocalRank 3 G :=
    hrk.trans (local_pRank_le_localRank 3 (by norm_num) (normalizer (U : Set G))
      ⟨U, hU1, hU2, rfl⟩)
  have hβ : 3 ∈ GLBBetaFour G := ⟨Nat.prime_three, by norm_num, hfdvd, h4⟩
  obtain ⟨F, hFsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  obtain ⟨Fs, hFFs⟩ := hFsyl.isPGroup.exists_le_sylow
  obtain ⟨Y, hY, hWY⟩ := (hS.toGlobal.d1Global.pre 3 hβ).2 Fs
  obtain ⟨H, hYH, hH⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hY
  have hD : CFSG.AGLEmbedding.D1Local 3 Fs H := ⟨hβ, hH, hWY.trans hYH⟩
  have hcore : GLBCore 3 2 (Fs : Subgroup G) ≤ H := hS.toGlobal.fullCore 3 Fs H hD
  have hsE : GLBStronglyEmbedded 3 H := stronglyEmbedded_three_of_global hS.toGlobal h313 hD
  have hLrank : 4 ≤ CFSG.Open.pRank 3 L :=
    hU4.trans (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_right)
  have hFrank : 2 ≤ CFSG.Open.pRank 3 F := by
    rw [pRank_eq_of_isSylowOf Nat.prime_three hFsyl]
    omega
  have hFne : F ≠ ⊥ := by
    intro hF
    have h1 : 3 ∣ Nat.card F := dvd_card_of_one_le_pRank Nat.prime_three (by omega)
    rw [hF, Subgroup.card_bot] at h1
    omega
  have hFH : F ≤ H :=
    Subgroup.le_normalizer.trans (normalizer_le_of_core hFFs hcore le_rfl hFrank)
  have hFp : IsPGroup 3 F := hFsyl.isPGroup
  have hFHne : F ⊓ H ≠ ⊥ := by
    rw [inf_eq_left.mpr hFH]
    exact hFne
  have hLH : L ≤ H := by
    rcases h2401 G L s e h3 with h | h
    · exact (h F hFsyl (H ⊓ L) fun S₀ hS₀F hS₀1 =>
        inf_le_inf_right L (normalizer_le_of_stronglyEmbedded_sub hsE hFp hFHne hS₀F hS₀1)).trans
        inf_le_left
    · exact absurd h hs
  exact c.false_of_le_core hFsyl hFFs hH.1 hcore hFrank hLH

end KxCfg

@[expose] def KxSporadicCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G)
    (T S L : Subgroup G), KxCfg p P M x z T S L →
    (∃ s : TauCeti.SporadicName, Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) →
    2 ≤ CFSG.Open.pRank 3 L →
    (∀ U : Subgroup G, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set G) ⊓ L) ≤ 3) →
    pCoreOf 2 (L ⊓ M) ≠ ⊥ → (∃ y ∈ pCoreOf 2 (L ⊓ M), z * y ≠ y * z) →
    normalizer ((pCoreOf 2 (L ⊓ M) : Subgroup G) : Set G) ⊓ L = L ⊓ M →
    rankThreePrimeCore p (centralizer ({x} : Set G)) = ⊥ → False

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
