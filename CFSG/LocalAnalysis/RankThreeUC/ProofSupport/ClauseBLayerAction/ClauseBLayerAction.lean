module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosedPrimeCentralized.WeakClosedPrimeCentralized
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerSylowAtLeastTwo.LayerSylowAtLeastTwo
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessNormalizerContainment.WitnessNormalizerContainment
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ModelledSylowNormalizerAction.ModelledSylowNormalizerAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBLayerAction

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

private theorem pRank_bot_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  unfold CFSG.Open.pRank
  apply Nat.le_zero.mp
  apply csSup_le'
  rintro k ⟨E, hE, -, hc⟩
  have : E = ⊥ := le_bot_iff.mp hE
  subst this
  rw [Subgroup.card_bot] at hc
  have : p ^ k = p ^ 0 := by rw [← hc]; simp
  exact (Nat.pow_right_injective hp.two_le this).le

private theorem sylow_top {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) ⊤ := by
  have h1 : IsPGroup p ((P : Subgroup G).subgroupOf ⊤) := P.isPGroup'.comap_subtype
  have h2 : ¬ p ∣ ((P : Subgroup G).subgroupOf ⊤).index := by
    intro hd
    have h3 := (Subgroup.relIndex_dvd_index_of_le (le_top : (P : Subgroup G) ≤ ⊤))
    exact P.not_dvd_index (dvd_trans (show p ∣ (P : Subgroup G).relIndex ⊤ from hd) h3)
  refine ⟨h1.toSylow h2, ?_⟩
  simpa using Subgroup.map_subgroupOf_eq_of_le (le_top : (P : Subgroup G) ≤ ⊤)

theorem layer_action {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hpA : p ∈ rankThreeSigmaA G) (P : Sylow p G) (hw : IsWitness p P M)
    {P₀ : Subgroup G} (hle : P₀ ≤ (P : Subgroup G)) (hcard : Nat.card P₀ = p)
    (hweak : CFSG.Quasithin.IsWeaklyClosedIn P₀ (P : Subgroup G))
    (hp5 : 5 ≤ p) {n : ℕ} (hn : 1 < n)
    (hmodel : Nonempty (↥(rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p n))) :
    (P : Subgroup G) ≤ Subgroup.centralizer (P₀ : Set G) ∧
    CFSG.ABGLocalTools.IsSylowOf p
      ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)))
      (rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ∧
    (P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≠ ⊥ ∧
    1 < CFSG.Open.pRank p ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ∧
    Subgroup.normalizer
      (((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Subgroup G) :
        Set G) ≤ M ∧
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
      (M ⊓ Subgroup.normalizer
        (((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Subgroup G) :
          Set G))
      ((P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) := by
  have hprime : p.Prime := Fact.out
  have hTop := sylow_top P
  have hPC := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosedPrimeCentralized.centralizes hprime
    P.isPGroup' hle hcard hweak
  have hSyl := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerSylowAtLeastTwo.isSylow hprime hTop hPC
  have hrank := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerSylowAtLeastTwo.one_lt_rank (by omega) hTop hPC
    ⟨n, hn, hmodel⟩
  have hXP : (P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤
      (P : Subgroup G) := inf_le_left
  have hne : (P : Subgroup G) ⊓ rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≠ ⊥ := by
    intro h
    rw [h, pRank_bot_eq hprime] at hrank
    omega
  have hN := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessNormalizerContainment.normalizer_le_of_isWitness
    hw hXP hrank
  refine ⟨hPC, hSyl, hne, hrank, hN, ?_⟩
  exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ModelledSylowNormalizerAction.isIrreducibleUnder_inf_normalizer_of_psl2_of_le
    hp5 hn hmodel inf_le_right hSyl
    (fun x hx => hN hx.2)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBLayerAction
