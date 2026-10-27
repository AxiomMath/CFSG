module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSwap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRMove
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddCentre
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSylow

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

theorem doubling_of_swapped_nineThreeTwo (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverDoubling) (hK : KFactStrongThreeSolv) {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) (hev : PairEvenIndex M H)
    (hXb : CFSG.AGLEmbeddingD2.NoXBlockFor G) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (t₁ : NineThreeTwo M (pCoreOf 2 H) L₁) (t₂ : NineThreeTwo M (pCoreOf 2 H) L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hswap : ∃ g ∈ H ⊓ M, barM M (L₁.map (MulAut.conj g).toMonoidHom) = barM M L₂)
    (hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂) :
    IsDoublingList (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) ∧
      IsDoublingList (↥(barM M L₂) ⧸ Subgroup.center ↥(barM M L₂)) := by
  obtain ⟨T, hT2, hQT, hNT, hT⟩ := hctx.exists_twoGroup_of_evenIndex hev
  have hNH := hctx.pair.normalizer_twoCore_H
  obtain ⟨g, hgK, hg⟩ := hswap
  obtain ⟨t, htT, ht⟩ := exists_swap_mem_sylow h₁ hne hk2 hT hNH hgK hg
  have hTM : T ≤ M := hT.1.trans inf_le_right
  have hT0 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hctx.pair.maxTwoLocal_M.1
    exact eq_bot_iff.mpr (hQT.trans h.le)
  have hZ₁' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hZ₂' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₂)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hmove := trBlocksMove_of_swap hctx hK h₁ h₂ hne hT2 hT0 hTM hNT hQT hZ₁' h3₁ h3₂ htT ht
  have hSyl := isSylowTwoOf_trX_of_nineThreeTwo h₁ h₂ hne hk2 hT hQT hNH t₁ t₂
  exact doubling_of_trX hGN hCov hK hctx hXb h₁ h₂ hne hk2 hT hNT hQT hSyl hmove.1 hmove.2
    hZ₁' hZ₂' t₁.1 t₂.1 h3₁ h3₂ hrank

@[expose] def L32Atlas : Prop :=
  ∀ (X : Type) [Group X], IsLThreeTwo X → Nat.card X = 168

theorem pRank_top_le_one_of_card_168 {X : Type} [Group X] [Finite X] (h : Nat.card X = 168) :
    Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three
    (⊤ : Subgroup X)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hEcard]; exact pow_dvd_pow 3 hlt
  have := h9.trans (Subgroup.card_subgroup_dvd_card E)
  rw [h] at this
  omega

theorem isA6OrU33_of_doubling (hU : U33Atlas) (hL32 : L32Atlas) {M S L : Subgroup G}
    (hw : IsWeakSBlock M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hm : 2 ≤ Open.pRank 3 L)
    (hd : IsDoublingList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    IsA6OrU33 ↥(barM M L) := by
  have hX : Open.IsQuasisimple ↥(barM M L) := hw.component.2.2
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
    rw [← card_inf_centralizer_eq_card_center]
    exact odd_card_center_barM hw.toIsTwoPrimeComponent
  have hrq := pRank_top_quot_center_eq hw.le hZ
  rcases hd with hL3 | hA6 | hU3
  · exfalso
    have := pRank_top_le_one_of_card_168 (hL32 _ hL3)
    omega
  · have hZb : Subgroup.center ↥(barM M L) = ⊥ := by
      obtain ⟨e⟩ := hA6
      exact tightCentreTrivial_of_atlas hU _ hX (Or.inl ⟨6, Or.inl rfl, ⟨e⟩⟩) hodd hZ'
    obtain ⟨e⟩ := hA6
    obtain ⟨e'⟩ := mulEquiv_of_center_eq_bot hZb e
    exact Or.inl ⟨e'⟩
  · have hZb : Subgroup.center ↥(barM M L) = ⊥ := by
      obtain ⟨d, hd, ⟨e⟩⟩ := hU3
      exact tightCentreTrivial_of_atlas hU _ hX (Or.inr ⟨d, hd, ⟨e⟩⟩) hodd hZ'
    exact Or.inr (IsUThreeThree.of_center_bot hZb hU3)

theorem isA6OrU33_of_swapped_nineThreeTwo (hGN : GlaubermanNilesInput)
    (hCov : KFactParabolicCoverDoubling) (hK : KFactStrongThreeSolv) (hU : U33Atlas)
    (hL32 : L32Atlas) {P : Sylow 3 G}
    {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) (hev : PairEvenIndex M H)
    (hXb : CFSG.AGLEmbeddingD2.NoXBlockFor G) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hk2 : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂)
    (t₁ : NineThreeTwo M (pCoreOf 2 H) L₁) (t₂ : NineThreeTwo M (pCoreOf 2 H) L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hZ₂ : ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hswap : ∃ g ∈ H ⊓ M, barM M (L₁.map (MulAut.conj g).toMonoidHom) = barM M L₂)
    (hm : 2 ≤ Open.pRank 3 L₁) :
    IsA6OrU33 ↥(barM M L₁) ∧ IsA6OrU33 ↥(barM M L₂) := by
  have hr : Open.pRank 3 L₂ = Open.pRank 3 L₁ := by
    obtain ⟨g, hgK, hg⟩ := hswap
    have hgM : g ∈ M := hgK.2
    have h1 : L₁.map (MulAut.conj g).toMonoidHom ≤ M := by
      rintro _ ⟨l, hl, rfl⟩
      exact M.mul_mem (M.mul_mem hgM (h₁.le hl)) (M.inv_mem hgM)
    have h2 := pRank_barM_eq Nat.prime_three (by norm_num) M _ h1
    have h3 := pRank_barM_eq Nat.prime_three (by norm_num) M L₂ h₂.le
    rw [hg] at h2
    rw [← h3, h2]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective L₁
  have hd := doubling_of_swapped_nineThreeTwo hGN hCov hK hctx hev hXb h₁ h₂ hne hk2 t₁ t₂ hZ₁ hZ₂
    h3₁ h3₂ hswap (by omega)
  exact ⟨isA6OrU33_of_doubling hU hL32 h₁ hZ₁ hm hd.1,
    isA6OrU33_of_doubling hU hL32 h₂ hZ₂ (hr ▸ hm) hd.2⟩

end CFSG.AGLEmbeddingD2.McLaughlin
