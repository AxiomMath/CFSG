module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MSide
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Rank3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Rank2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Global
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Cent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Coprime
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Inputs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane SmallRankSylowTwo SmallRankCover
  smallRankR smallRankIsQ8D8)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem p65_plane65 (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    Plane65 p P M x z := by
  have hprime := hS.prime
  refine ⟨hprime, hS.p_ge,
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper M
      hx.ne_top, plane_of_central hS hx hz, hS.sylow_le, hz.centralizes, hS.four_le_pRank,
    hx.pRank_centralizer_le hS, hx.sylow, fun N _ hN => eq_top_of_isPGroup_quotient hS N hN⟩

private theorem p65_exists_isMax {B F : Subgroup G} {f : ℕ} (hF : IsFInvariantIn f B M F) :
    ∃ Fs : Subgroup G, F ≤ Fs ∧ IsMaxFInvariantIn f B M Fs := by
  classical
  obtain ⟨Fs, ⟨hFs, hFFs⟩, hmax⟩ := Set.exists_max_image
    {F' : Subgroup G | IsFInvariantIn f B M F' ∧ F ≤ F'} (fun F' => Nat.card F')
    (Set.toFinite _) ⟨F, hF, le_rfl⟩
  refine ⟨Fs, hFFs, hFs, fun F' hF' hle => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (hmax F' ⟨hF', hFFs.trans hle⟩)).symm

theorem s62Prop65_of_inputs (hKA : KFactP65Single) (hKB : KFactP65Multi)
    (hKC : KFactP65RankThree) (hKD : KFactP65RankTwo) (hKE : KFactP65Rank4)
    (hKF : P65CoprimeRankTwo) : S62Prop65 := by
  intro G _ _ p P M x z hS hx hz _h614 T hT _hcov hp5 hR F hF1 hFM hBF hcop hodd
  by_contra hFnot
  have hprime := hS.prime
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : zpowers x ⊔ zpowers z ≤ M := (hpl.isIsolatedPlane.1).trans hS.sylow_le
  obtain ⟨f₀, hf₀, hf₀2, hf₀p, F₁, hF₁p, hF₁F, hF₁1, hBF₁, hF₁not⟩ :=
    p65_exists_f_counterexample hF1 hodd hcop hBF hFnot
  obtain ⟨F, ⟨⟨f, hf, hf2, hfp, hFp⟩, hFM, hF1, hBF, hHM⟩, hmaxc⟩ := p65_exists_max
    (C := fun F' : Subgroup G => (∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ IsPGroup f F') ∧ F' ≤ M ∧
      F' ≠ ⊥ ∧ zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) ∧
      ¬ normalizer (F' : Set G) ≤ M)
    ⟨F₁, ⟨f₀, hf₀, hf₀2, hf₀p, hF₁p⟩, hF₁F.trans hFM, hF₁1, hBF₁, hF₁not⟩
  have hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → Nat.card F < Nat.card F' →
      normalizer (F' : Set G) ≤ M := by
    intro F' hF'M hF'p hF'1 hBF' hcard
    by_contra hnot
    exact absurd (hmaxc F' ⟨⟨f, hf, hf2, hfp, hF'p⟩, hF'M, hF'1, hBF', hnot⟩) (not_le.mpr hcard)
  obtain ⟨Fs, hFFs', hFsmax⟩ := p65_exists_isMax (M := M)
    (show IsFInvariantIn f (zpowers x ⊔ zpowers z) M F from ⟨hFM, hFp, hBF⟩)
  have hchar : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hS.toGlobal.d1Global.charTwo M hS.loc.maxLocal.1
  have hmS := fun {F' : Subgroup G} (hF' : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F') =>
    p65_mSide hKA hKB hS hx hz hT hp5 hR hf hf2 hfp hF'
  rcases hFFs'.eq_or_lt with heq | hFFs
  ·
    subst heq
    obtain ⟨hM1, hM2⟩ := hmS hFsmax
    exact p65_false_of_isMax hKC hS hx hz hf hf2 hfp hFsmax hF1 hHM hM1 hM2
  · obtain ⟨hFsM, hFsp, hBFs⟩ := hFsmax.1
    obtain ⟨hM1, -⟩ := hmS hFsmax
    have hR4' : 4 ≤ Open.pRank p (M ⊓ normalizer (Fs : Set G)) :=
      hS.four_le_pRank.trans hM1
    have hBle : zpowers x ⊔ zpowers z ≤ M ⊓ normalizer (Fs : Set G) := le_inf hBM hBFs
    obtain ⟨R, hBR, hRH, hRp, hRidx⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le_of_isPGroup hprime hBle hB3
    have hR4 : 4 ≤ Open.pRank p R := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow hprime hRH hRp hRidx]
      exact hR4'
    have hRM : R ≤ M := hRH.trans inf_le_left
    have hRFs : R ≤ normalizer (Fs : Set G) := hRH.trans inf_le_right
    have hrankH : Open.pRank p (normalizer (F : Set G)) ≤ 2 := by
      by_contra hr3
      push Not at hr3
      obtain ⟨E, hFE, hEp, hBE, hEO, hOM⟩ := p65_rank_three_enlarge hKC hS hx hz hf hf2 hfp hFp hF1
        hBF hHM hFsp hFsM hBFs hFFs (by omega)
      exact hHM (p65_normalizer_le_of_enlarged hprime hf hB3 hmax hBF hOM hFE hEp hBE hEO)
    have hcyc := p65_centralizer_cyclic hKD hS hx hz hf hf2 hfp hFp hF1 hBF hHM hFsp hFsM hBFs
      hFFs hmax hrankH hRp hRM hBR hRFs hR4
    have h4 : 4 ≤ Open.pRank f M :=
      hKE G p P M x z T f Fs R (p65_plane65 hS hx hz) hchar hp5 hT hR hf hf2 hfp hFsmax hBR hRH
        hRp hRidx hR4 hcyc
    have hFcyc := p65_cyclic_of_not_le hS hf hf2 h4 hFp hFM hHM
    obtain ⟨y, hyF, hyo⟩ : ∃ y ∈ F, orderOf y = f := by
      have : Fact f.Prime := ⟨hf⟩
      have hdvd : f ∣ Nat.card F :=
        hFp.card_eq_or_dvd.resolve_left fun h1 => hF1 (Subgroup.eq_bot_of_card_eq _ h1)
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' f hdvd
      exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
    have hApply : ∀ {W : Subgroup G}, W ≠ ⊥ → W ≤ M →
        zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → ¬ normalizer (W : Set G) ≤ M →
        ∀ {Q : Subgroup G}, Q ≤ normalizer (W : Set G) → IsPGroup p Q →
          ¬ p ∣ (Q.subgroupOf (normalizer (W : Set G))).index → zpowers x ⊔ zpowers z ≤ Q →
          3 ≤ Open.pRank p (normalizer (W : Set G)) →
          ∀ W' : Subgroup G, W' ≤ normalizer (W : Set G) →
            zpowers x ⊔ zpowers z ≤ normalizer (W' : Set G) →
            Nat.Coprime (Nat.card W') (2 * p) →
            W' ≤ rankThreePrimeCore p (normalizer (W : Set G)) :=
      fun {W} hW1 hWM hBW hHM' {Q} hQH hQ hQidx hBQ hrank =>
        (p65_rankThree_apply hKC hS hx hz hW1 hWM hBW hHM' hQH hQ hQidx hBQ hrank).2.1
    have hrk := p65_pRank_centralizer_le_two hS hx hz hApply hf hf2 hfp h4 hFp hF1 hFM hBF hHM
      hFcyc hyF hyo hFsp hFsM hBFs hFFs hmax hRp hRM hBR hRFs (by omega)
    have hflt := p65_f_lt_p hS hf hf2 hfp h4 hFp hF1 hFM hHM hyF hyo hrk
    exact p65_final_contradiction hKF hprime (by have := hS.p_ge; omega) hf hf2 hflt
      hpl.isElemAbelian hpl.card_eq hBR hRp hFp hFsp hFFs.le hFcyc hyF hyo hBF hBFs hRFs hrk hcyc

theorem s62Prop65_holds (hKA : KFactP65Single) (hKB : KFactP65Multi) (hKC : KFactP65RankThree)
    (hKD : KFactP65RankTwo) (hKE : KFactP65Rank4) : S62Prop65 :=
  s62Prop65_of_inputs hKA hKB hKC hKD hKE p65_coprime_rank_two

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
