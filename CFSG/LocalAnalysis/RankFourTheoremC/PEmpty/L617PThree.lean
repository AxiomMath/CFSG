module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Main
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.EscapeMaxTools
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.JZero
import CFSG.Goldschmidt.Steps.G74Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Transport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane)
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit

@[expose] def UniquePComponent {A : Type} [Group A] [Finite A] (p : ℕ) (X : Subgroup A) : Prop :=
  ∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧
    p ∣ Nat.card L ∧ ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
      IsComponentOf K ⊤ → p ∣ Nat.card K → K = L

@[expose] def KFactSingleComponentThreeRank : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65 p P X x z → ¬ HasPrimeConstraint (G := ↥X) p → UniquePComponent p X →
      2 ≤ Open.pRank 3 X

@[expose] def KFactP65Rank4AB : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A)
    (f : ℕ) (Fs R : Subgroup A), Plane65 p P X x z →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    (HasPrimeConstraint (G := ↥X) p ∨ ¬ UniquePComponent p X) →
    f.Prime → f ≠ 2 → f ≠ p →
    IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs →
    zpowers x ⊔ zpowers z ≤ R → R ≤ X ⊓ normalizer (Fs : Set A) → IsPGroup p R →
    ¬ p ∣ (R.subgroupOf (X ⊓ normalizer (Fs : Set A))).index → 4 ≤ Open.pRank p R →
    IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A) → 4 ≤ Open.pRank f X

@[expose] def StepP65OddAB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
      (HasPrimeConstraint (G := ↥M) p ∨ ¬ UniquePComponent p M) →
        ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M → Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane) in
theorem p65_covering_of_le_core' (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {f : ℕ} (hf : f.Prime) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) (hFD : F ≤ rankThreePrimeCore p M) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
      ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  set D : Subgroup G := rankThreePrimeCore p M with hDdef
  have hpl : SmallRankPlane p (P : Subgroup G) x z := plane_of_central hS hx hz
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : B ≤ M := (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hS.sylow_le
  obtain ⟨⟨hFM, hF2, hBF⟩, hmax⟩ := hF
  obtain ⟨hDM, hMD, hDp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hD3 : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp hDp
  have hBD : B ≤ normalizer (D : Set G) := hBM.trans hMD
  have hFsyl : fusionIsSylowIn f F D := by
    obtain ⟨R, hRsyl, hFR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      hprime hf hB3 hD3 hBD hFD hF2 hBF
    have hRF : R = F := hmax R ⟨hRsyl.1.trans hDM, hRsyl.2.1, hBR⟩ hFR
    rwa [← hRF]
  have hbotp : IsPGroup p (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  refine ⟨?_, fun m hm => ?_⟩
  ·
    have hbotf : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
    have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) := hS.sylow_le.trans hMD
    have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    obtain ⟨S, hSsyl, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      hprime hf P.isPGroup' hD3 hPD bot_le hbotf hPbot
    obtain ⟨c, hc, hFc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
      hprime hf hbotp hD3 bot_le hSsyl hFsyl bot_le bot_le
    have hcM : c ∈ M := hDM (mem_inf.mp hc).1
    have hle : (P : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ M ⊓ normalizer (F : Set G) := by
      refine le_inf ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact M.mul_mem (M.mul_mem hcM (hS.sylow_le ha)) (M.inv_mem hcM)
      · rw [hFc, ← Subgroup.map_equiv_normalizer_eq]
        exact map_mono hPS
    calc Open.pRank p (P : Subgroup G)
        = Open.pRank p ((P : Subgroup G).map (MulAut.conj c).toMonoidHom) :=
          (pRank_map_automorphism p hprime.one_lt _ _).symm
      _ ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) :=
          CFSG.SectionRank.pRank_mono hprime.one_lt hle
  ·
    have hFm := p65_fusionIsSylowIn_conj hFsyl (hMD hm)
    obtain ⟨c, hc, hFc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
      hprime hf hbotp hD3 bot_le hFsyl hFm bot_le bot_le
    have hcD : c ∈ D := (mem_inf.mp hc).1
    have hn := p65_mem_normalizer_of_map_eq hFc
    exact ⟨c, hcD, c⁻¹ * m, mem_inf.mpr ⟨M.mul_mem (M.inv_mem (hDM hcD)) hm, hn⟩,
      (mul_inv_cancel_left c m).symm⟩

theorem p65_exists_isMax' {B F : Subgroup G} {f : ℕ} (hF : IsFInvariantIn f B M F) :
    ∃ Fs : Subgroup G, F ≤ Fs ∧ IsMaxFInvariantIn f B M Fs := by
  classical
  obtain ⟨Fs, ⟨hFs, hFFs⟩, hmax⟩ := Set.exists_max_image
    {F' : Subgroup G | IsFInvariantIn f B M F' ∧ F ≤ F'} (fun F' => Nat.card F')
    (Set.toFinite _) ⟨F, hF, le_rfl⟩
  refine ⟨Fs, hFFs, hFs, fun F' hF' hle => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (hmax F' ⟨hF', hFFs.trans hle⟩)).symm

theorem p65_mSideAB (hKB : KFactP65Multi)
    (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    (hAB : HasPrimeConstraint (G := ↥M) p ∨ ¬ UniquePComponent p M)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
    ((∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n) ∨
     (∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ p →
        ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧
          ∀ g ∈ M ⊓ normalizer (E : Set G), g * a * g⁻¹ ∉ zpowers b)) := by
  have hprime := hS.prime
  have hpl := p65_plane65 hS hx hz
  by_cases hcon : HasPrimeConstraint (G := M) p
  · obtain ⟨h1, h2⟩ := p65_covering_of_le_core' hS hx hz hf hfp hF
      (fusionIsSylowIn_of_isMax hS hx hz hcon hf hfp hF).1
    exact ⟨h1, Or.inl h2⟩
  · have huniq : ¬ UniquePComponent p M := hAB.resolve_left hcon
    obtain ⟨L₀, hL₀, -, -, hL₀p, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component
      hS.toGlobal.d1Global.kProper M (fun h => hx.not_le (h ▸ le_top)) p hprime hcon
    obtain ⟨K, hK, hKp, hKL⟩ : ∃ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
        IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ K ≠ L₀ := by
      by_contra hno
      push Not at hno
      exact huniq ⟨L₀, hL₀, hL₀p, hno⟩
    obtain ⟨h1, h2⟩ := hKB G p P M x z hpl ⟨K, L₀, hK, hKp, hL₀, hL₀p, hKL⟩
    exact ⟨h1 f F hf hfp hF, Or.inr h2⟩

theorem stepP65OddAB_of_inputs (hKB : KFactP65Multi) (hKC : KFactP65RankThree)
    (hKD : KFactP65RankTwo) (hKE : KFactP65Rank4AB) (hKF : P65CoprimeRankTwo) :
    StepP65OddAB := by
  intro G _ _ p P M x z hS hx hz hAB F hF1 hFM hcop hodd hBF
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
  obtain ⟨Fs, hFFs', hFsmax⟩ := p65_exists_isMax' (M := M)
    (show IsFInvariantIn f (zpowers x ⊔ zpowers z) M F from ⟨hFM, hFp, hBF⟩)
  have hchar : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hS.toGlobal.d1Global.charTwo M hS.loc.maxLocal.1
  have hmS := fun {F' : Subgroup G} (hF' : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F') =>
    p65_mSideAB hKB hS hx hz hAB hf hf2 hfp hF'
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
      hKE G p P M x z f Fs R (p65_plane65 hS hx hz) hchar hAB hf hf2 hfp hFsmax hBR hRH
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

open CFSG.LocalAnalysis.RankThreeTheoremC in
theorem stronglyEmbedded_three_of_global (hG : Global G) (h313 : GL83NormalElementaryRankFour)
    {P₃ : Sylow 3 G} {M₃ : Subgroup G} (hloc : D1Local 3 P₃ M₃) : GLBStronglyEmbedded 3 M₃ := by
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hS := hG.d1Global
  have hFC := hG.fullCore
  by_cases hP : ∃ y : G, IsPElement 3 M₃ y
  ·
    have hA := (hG.thmC 3 P₃ M₃ hloc hP).1
    unfold CFSG.Open.GLBAlmostStrong at hA
    obtain ⟨-, hne, -, P', -, -, hcase⟩ := hA
    rcases hcase with h | h
    · exact ⟨hne, h.1, h.2⟩
    · omega
  ·
    have hPM : (P₃ : Subgroup G) ≤ M₃ := sylow_le_of_core hloc
    have hP4 := four_le_pRank_sylow hloc.beta P₃
    have hkey : ∀ x ∈ (P₃ : Subgroup G), x ≠ 1 → x ^ 3 = 1 →
        normalizer ((zpowers x : Subgroup G) : Set G) ≤ M₃ := by
      intro x hxP hx1 hx3
      have hC3 := three_le_pRank_inf_centralizer h313 P₃.isPGroup' hP4 hxP hx3
      have hCM : centralizer ({x} : Set G) ≤ M₃ := by
        by_contra hCM
        exact hP ⟨x, hPM hxP, orderOf_eq_prime hx3 hx1,
          hC3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 hprime
            (inf_le_inf_right _ hPM)), hCM⟩
      exact normalizer_zpowers_le_of_centralizer_le hFC hloc hCM (by omega)
    have hPn : ∀ X : Subgroup G, X ≤ P₃ → IsPGroup 3 X → X ≠ ⊥ →
        normalizer (X : Set G) ≤ M₃ := by
      intro X hXP hXp hX1
      by_cases h2 : 2 ≤ Open.pRank 3 X
      · exact normalizer_le_of_two_le_pRank hFC hloc hXp (hXP.trans hPM) h2
      · have hcyc : IsCyclic X := by
          by_contra hnc
          exact h2 (two_le_pRank_of_not_isCyclic hprime (by norm_num) hXp hnc)
        obtain ⟨n, hn⟩ := hXp.exists_card_eq
        have hn0 : n ≠ 0 := by
          rintro rfl
          exact hX1 ((Subgroup.card_eq_one).1 (by simpa using hn))
        obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by
          rw [hn]; exact dvd_pow_self 3 hn0)
        have h1 : 1 ≤ Open.pRank 3 X := by
          have hy3 : (y : G) ^ 3 = 1 := by
            have := pow_orderOf_eq_one y
            rw [hy] at this
            simpa using congrArg Subtype.val this
          have hy1 : (y : G) ≠ 1 := fun h => by
            have : y = 1 := Subtype.ext h
            rw [this, orderOf_one] at hy
            omega
          refine le_pRank_of_isElemAbelian hprime (Y := zpowers (y : G)) ?_ ?_ (k := 1) ?_
          · exact zpowers_le.2 y.2
          · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
              (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hy3)
          · rw [Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
            simp
        obtain ⟨x, hxX, hx1, hx3, hNX⟩ :=
          exists_pow_eq_one_normalizer_le_of_isCyclic hprime hXp hcyc h1
        exact hNX.trans (hkey x (hXP hxX) hx1 hx3)
    have hcard : 3 ∣ Nat.card M₃ :=
      (CFSG.LocalAnalysis.RankFourTheoremC.dvd_card_of_one_le_pRank hprime
        (by omega : 1 ≤ Open.pRank 3 (P₃ : Subgroup G))).trans (Subgroup.card_dvd_of_le hPM)
    have := hS.simple
    refine CFSG.RankThree.PartTwo.Sec21.glbStronglyEmbedded_of_normalizer_le
      (CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hloc.maxLocal.1) hcard ?_
    intro X hXM hXp hX1
    obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup 3 hprime P₃ M₃ hPM X hXp hXM
    have hXm : X.map (MulAut.conj (m : G)).toMonoidHom ≠ ⊥ := fun h =>
      hX1 ((map_eq_bot_iff_of_injective (f := (MulAut.conj (m : G)).toMonoidHom) X
        (MulAut.conj (m : G)).injective).mp h)
    have hN := hPn _ hm (hXp.map _) hXm
    have hmap : (normalizer (X : Set G)).map (MulAut.conj (m : G)).toMonoidHom ≤ M₃ := by
      rw [Subgroup.map_equiv_normalizer_eq]
      exact hN
    exact (conjugate_subgroup_le_iff_of_conjugator_mem _ M₃ (m : G) m.2).1 hmap

theorem le_of_stronglyEmbedded_of_ne_bot {M₃ R : Subgroup G} (hs : GLBStronglyEmbedded 3 M₃)
    (hR : IsPGroup 3 R) (hne : R ⊓ M₃ ≠ ⊥) : R ≤ M₃ :=
  CFSG.AGLEmbeddingD2.le_of_stronglyEmbedded_of_inf_ne_bot Nat.prime_three hs hR hne

theorem L617P.le_pRank_three {p : ℕ} (hp : p.Prime) {B N Y : Subgroup G} {z : G}
    (hzB : z ∈ B) (hzp : z ^ p = 1) (hBN : B ≤ normalizer (N : Set G))
    (hchar : IsCharacteristicP 2 ↥N) (hY : IsBlockOfInX N Y)
    (hq : ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hzY : z ∉ normalizer (Y : Set G))
    {T E : Subgroup G} (hTY : T ≤ Y) (hT3 : Nat.card T = 3)
    (hcjT : ∀ b ∈ B, L617P.cj T b ≤ E) (hEab : ∀ u ∈ E, ∀ v ∈ E, u * v = v * u) :
    p ≤ Open.pRank 3 E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzN : z ∈ normalizer (N : Set G) := hBN hzB
  obtain ⟨t, ht3, hTt⟩ := L617P.exists_zpowers_eq hT3
  have htT : t ∈ T := hTt ▸ mem_zpowers t
  have htY : t ∈ Y := hTY htT
  have htpow : t ^ 3 = 1 := by rw [← ht3]; exact pow_orderOf_eq_one t
  set a : ℕ → G := fun j => z ^ j * t * (z ^ j)⁻¹ with ha
  have haE : ∀ j, a j ∈ E := fun j =>
    hcjT (z ^ j) (Subgroup.pow_mem _ hzB j) (L617P.conj_mem_cj htT (z ^ j))
  have hcomm : ∀ j m, j < m → m < p → ∀ y ∈ Y,
      a j * (z ^ m * y * (z ^ m)⁻¹) = (z ^ m * y * (z ^ m)⁻¹) * a j := by
    intro j m hjm hmp y hy
    have h := conj_pow_commute hchar hp hzp hzN hY hzY (i := m - j) (by omega) (by omega) hy htY
    have hm : z ^ m = z ^ j * z ^ (m - j) := by rw [← pow_add]; congr 1; omega
    simp only [ha]
    rw [hm]
    calc z ^ j * t * (z ^ j)⁻¹ * (z ^ j * z ^ (m - j) * y * (z ^ j * z ^ (m - j))⁻¹)
        = z ^ j * (t * (z ^ (m - j) * y * (z ^ (m - j))⁻¹)) * (z ^ j)⁻¹ := by group
      _ = z ^ j * (z ^ (m - j) * y * (z ^ (m - j))⁻¹ * t) * (z ^ j)⁻¹ := by rw [h]
      _ = z ^ j * z ^ (m - j) * y * (z ^ j * z ^ (m - j))⁻¹ * (z ^ j * t * (z ^ j)⁻¹) := by
          group
  obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → Subgroup G, D 0 = ⊥ ∧ ∀ k, D (k + 1) = D k ⊔ zpowers (a k) :=
    ⟨fun k => Nat.rec ⊥ (fun j Dj => Dj ⊔ zpowers (a j)) k, rfl, fun _ => rfl⟩
  have hDE : ∀ k, D k ≤ E := by
    intro k
    induction k with
    | zero => rw [hD0]; exact bot_le
    | succ k ih => rw [hDs]; exact sup_le ih (zpowers_le.mpr (haE k))
  let S3 : Subgroup G :=
    { carrier := {x | x ∈ E ∧ x ^ 3 = 1}
      mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hEab x hx.1 y hy.1) 3), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨E.one_mem, one_pow 3⟩
      inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have haS : ∀ j, a j ∈ S3 := fun j => ⟨haE j, by
    show (z ^ j * t * (z ^ j)⁻¹) ^ 3 = 1
    rw [conj_pow, htpow, mul_one, mul_inv_cancel]⟩
  have hDS : ∀ k, D k ≤ S3 := by
    intro k
    induction k with
    | zero => rw [hD0]; exact bot_le
    | succ k ih => rw [hDs]; exact sup_le ih (zpowers_le.mpr (haS k))
  have hDC : ∀ k m, k ≤ m → m < p → ∀ y ∈ Y,
      D k ≤ centralizer ({z ^ m * y * (z ^ m)⁻¹} : Set G) := by
    intro k
    induction k with
    | zero => intro m _ _ y _; rw [hD0]; exact bot_le
    | succ k ih =>
      intro m hkm hmp y hy
      rw [hDs]
      refine sup_le (ih m (by omega) hmp y hy) (zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm k m (by omega) hmp y hy
  have hEc : IsMulCommutative E := ⟨⟨fun u v => Subtype.ext (hEab u u.2 v v.2)⟩⟩
  have hcard : ∀ k, k ≤ p → Nat.card (D k) = 3 ^ k := by
    intro k
    induction k with
    | zero => intro _; rw [hD0, Subgroup.card_bot]; rfl
    | succ k ih =>
      intro hkp
      have hak1 : a k ≠ 1 := by
        intro h
        have h' : z ^ k * t * (z ^ k)⁻¹ = 1 := h
        have ht1 : t = 1 := by
          calc t = (z ^ k)⁻¹ * (z ^ k * t * (z ^ k)⁻¹) * z ^ k := by group
            _ = 1 := by rw [h']; group
        rw [ht1, orderOf_one] at ht3
        omega
      have hak3 : orderOf (a k) = 3 := orderOf_eq_prime (haS k).2 hak1
      have hinf : D k ⊓ zpowers (a k) = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        obtain ⟨hgD, hgZ⟩ := Subgroup.mem_inf.mp hg
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hgZ
        by_contra hg1
        have hgs : a k ^ n = z ^ k * t ^ n * (z ^ k)⁻¹ := by
          simp only [ha]; exact conj_zpow
        have hs1 : t ^ n ≠ 1 := by
          intro h; apply hg1; rw [hgs, h]; group
        have hs3 : (t ^ n) ^ 3 = 1 := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htpow, one_zpow]
        have hsY : t ^ n ∈ Y := Subgroup.zpow_mem _ htY n
        obtain ⟨y, hyY, hsy⟩ :=
          L617P.exists_not_commute hY hq hsY (orderOf_eq_prime hs3 hs1)
        apply hsy
        have hc := Subgroup.mem_centralizer_singleton_iff.mp
          (hDC k k le_rfl (by omega) y hyY hgD)
        rw [hgs] at hc
        calc t ^ n * y = (z ^ k)⁻¹ * ((z ^ k * t ^ n * (z ^ k)⁻¹) * (z ^ k * y * (z ^ k)⁻¹))
              * z ^ k := by group
          _ = (z ^ k)⁻¹ * ((z ^ k * y * (z ^ k)⁻¹) * (z ^ k * t ^ n * (z ^ k)⁻¹)) * z ^ k := by
              rw [hc]
          _ = y * t ^ n := by group
      rw [hDs, CFSG.Goldschmidt.G74.card_sup_of_inf_eq_bot hEc (hDE k) (zpowers_le.mpr (haE k))
        hinf, ih (by omega), Nat.card_zpowers, hak3, pow_succ]
  have hDel : IsElemAbelian 3 (D p) :=
    ⟨⟨⟨fun u v => Subtype.ext (hEab u (hDE p u.2) v (hDE p v.2))⟩⟩, fun x hx => (hDS p hx).2⟩
  exact CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_of_isElemAbelian_of_pow_le Nat.prime_three
    (hDE p) hDel (by rw [hcard p le_rfl])

theorem three_mem_betaFour_of_twoLocal {H E : Subgroup G} (hH : IsTwoLocal H) (hEH : E ≤ H)
    (h4 : 4 ≤ Open.pRank 3 E) : 3 ∈ GLBBetaFour G := by
  refine ⟨Nat.prime_three, by norm_num, ?_, ?_⟩
  · exact (CFSG.LocalAnalysis.RankFourTheoremC.dvd_card_of_one_le_pRank Nat.prime_three
      (by omega : 1 ≤ Open.pRank 3 E)).trans (Subgroup.card_subgroup_dvd_card E)
  · have hEH' : Open.pRank 3 E ≤ Open.pRank 3 H :=
      CFSG.SectionRank.pRank_mono (by norm_num) hEH
    exact h4.trans (hEH'.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank
      3 Nat.prime_three H hH))

theorem L617P.exists_three_subgroup' {p : ℕ} (hp : p.Prime) {B N Y : Subgroup G} {z : G}
    (hBp : IsPGroup p B) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hzB : z ∈ B)
    (hzp : z ^ p = 1) (hBN : B ≤ normalizer (N : Set G)) (hNp : ¬ p ∣ Nat.card N)
    (hchar : IsCharacteristicP 2 ↥N) (hY : IsBlockOfInX N Y)
    (hq : ¬ CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hzY : z ∉ normalizer (Y : Set G)) :
    ∃ F E : Subgroup G, F ≠ ⊥ ∧ IsPGroup 3 F ∧ F ≤ E ∧ E ≤ N ∧ IsPGroup 3 E ∧
      p ≤ Open.pRank 3 E ∧ F ≤ centralizer ({z} : Set G) ∧ B ≤ normalizer (F : Set G) ∧
      ∀ M' : Subgroup G, pCoreOf 2 Y ≤ M' → normalizer (F : Set G) ≤ M' → Y ≤ M' := by
  open L617P in
  have hcopY : ¬ p ∣ Nat.card Y := fun h => hNp (h.trans (Subgroup.card_dvd_of_le hY.1))
  obtain ⟨a, ha⟩ := card_eq_three_mul (card_top_eq_three hY hq)
  obtain ⟨T, hTY, hT3, hST⟩ := exists_invariant_three hp (hBp.to_le inf_le_left) hcopY
    inf_le_right ha
  obtain ⟨E, hcjT, hEN, hEab, hcjE, hE3⟩ := exists_abelian_normalized hBN hchar hY hTY hT3 hST
  obtain ⟨t, ht3, hTt⟩ := exists_zpowers_eq hT3
  have htT : t ∈ T := hTt ▸ mem_zpowers t
  have htY : t ∈ Y := hTY htT
  have hzN : z ∈ normalizer (N : Set G) := hBN hzB
  have hTE : T ≤ E := by
    have := hcjT 1 B.one_mem
    rwa [cj_one] at this
  set F : Subgroup G := E ⊓ centralizer ({z} : Set G)
  have hcjF : ∀ β ∈ B, cj F β ≤ F := by
    intro β hβ u hu
    have huE : u ∈ E := hcjE β hβ (cj_mono inf_le_left β hu)
    refine Subgroup.mem_inf.mpr ⟨huE, ?_⟩
    rw [mem_cj] at hu
    have hf : (β⁻¹ * u * β) * z = z * (β⁻¹ * u * β) :=
      Subgroup.mem_centralizer_singleton_iff.mp hu.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hβz : β * z = z * β := hBab β hβ z hzB
    have hβz' : β⁻¹ * z = z * β⁻¹ := hBab β⁻¹ (Subgroup.inv_mem _ hβ) z hzB
    calc u * z = β * (β⁻¹ * u * β) * (β⁻¹ * z) := by group
      _ = β * (β⁻¹ * u * β) * (z * β⁻¹) := by rw [hβz']
      _ = β * ((β⁻¹ * u * β) * z) * β⁻¹ := by group
      _ = β * (z * (β⁻¹ * u * β)) * β⁻¹ := by rw [hf]
      _ = (β * z) * (β⁻¹ * u * β) * β⁻¹ := by group
      _ = (z * β) * (β⁻¹ * u * β) * β⁻¹ := by rw [hβz]
      _ = z * u := by group
  have hBF : B ≤ normalizer (F : Set G) := fun β hβ =>
    mem_normalizer_of_cj_le (hcjF β hβ) (hcjF β⁻¹ (Subgroup.inv_mem _ hβ))
  have hFne : F ≠ ⊥ := by
    obtain ⟨d, hdF, hdact⟩ := exists_diagonal_of_mem (Y := Y) (E := E) hp.pos hzp
      (fun i _ hip x hx t' ht' => conj_pow_commute hchar hp hzp hzN hY hzY ‹_› hip hx ht')
      htY (fun i => hcjT (z ^ i) (Subgroup.pow_mem _ hzB i) (conj_mem_cj htT (z ^ i)))
    intro hbot
    have hdF' : d ∈ F := hdF
    rw [hbot, Subgroup.mem_bot] at hdF'
    obtain ⟨y, hyY, hy⟩ := exists_not_commute hY hq htY ht3
    apply hy
    have h := hdact y hyY
    rw [hdF'] at h
    have h2 : y = t * y * t⁻¹ := by simpa using h
    calc t * y = (t * y * t⁻¹) * t := by group
      _ = y * t := by rw [← h2]
  have hrk := L617P.le_pRank_three hp hzB hzp hBN hchar hY hq hzY hTY hT3 hcjT hEab
  refine ⟨F, E, hFne, hE3.to_le inf_le_left, inf_le_left, hEN, hE3, hrk, inf_le_right, hBF, ?_⟩
  intro M' hcore hnorm g hg
  obtain ⟨c, hc, k, rfl⟩ := exists_decomp_block hY hq htY ht3 hg
  refine M'.mul_mem (hcore hc) (Subgroup.zpow_mem _ ?_ k)
  exact hnorm (mem_normalizer_of_commute inf_le_left hEab (hTE htT))

theorem exists_threeCore (hG : D1Global G) (h3 : 3 ∈ GLBBetaFour G) {E : Subgroup G}
    (hE : IsPGroup 3 E) : ∃ (P₃ : Sylow 3 G) (M₃ : Subgroup G), D1Local 3 P₃ M₃ ∧
      E ≤ (P₃ : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₃, hEP₃⟩ := hE.exists_le_sylow
  obtain ⟨Y, hY, hWY⟩ := (hG.pre 3 h3).2 P₃
  obtain ⟨L, hYL, hL⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hY
  exact ⟨P₃, L, ⟨h3, hL, hWY.trans hYL⟩, hEP₃⟩

theorem exists_three_through {M F : Subgroup G} (hF : IsPGroup 3 F) (hFM : F ≤ M) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ R ≤ M ∧ F ≤ R ∧ Open.pRank 3 M ≤ Open.pRank 3 R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := (hF.comap_subtype (K := M)).exists_le_sylow
  refine ⟨(Q : Subgroup M).map M.subtype, Q.isPGroup'.map _, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro f hf
    exact ⟨⟨f, hFM hf⟩, hQ (by simpa [Subgroup.mem_subgroupOf] using hf), rfl⟩
  · rw [pRank_map_subtype (by norm_num), (CFSG.SectionRank.pRank_sylow Q).1,
      ← pRank_map_subtype (by norm_num), ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem stepL617PrimeTop_of_three (h313 : GL83NormalElementaryRankFour)
    (h1 : KFactSingleComponentThreeRank) (h65 : StepP65OddAB) : StepL617PrimeTop := by
  intro G _ _ p P M x z hS hx hz H S hopt hEq Y hY hq hzY
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hSHM : S ≤ H ⊓ M := hopt.ext.pair.isMax.1.1
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hSM : S ≤ M := hSHM.trans inf_le_right
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hopt.maxInv
  have hOH : GLBPrimeCore p H ≤ H := CFSG.AGLEmbedding.glbPrimeCore_le p H
  have hHO : H ≤ normalizer (GLBPrimeCore p H : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H
  have hOcop : Nat.Coprime p (Nat.card (GLBPrimeCore p H)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p H
  set N : Subgroup G := GLBPrimeCore p H ⊔ S
  have hNH : N ≤ H := sup_le hOH hSH
  have hNp : ¬ p ∣ Nat.card N :=
    not_dvd_card_sup hprime hS.ne_two hOH hSH hHO hOcop hS2
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer (N : Set G) := fun b hb =>
    mem_normalizer_sup (hHO (hBH hb)) (hBS hb)
  have hSsylow : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    obtain ⟨S₁, hS₁, hSS₁, hBS₁⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      hprime Nat.prime_two hB3 hNp hBN le_sup_right hS2 hBS
    have hS₁S : S₁ = S := hSmax S₁ ⟨hS₁.1.trans hNH, hS₁.2.1, hBS₁⟩ hSS₁
    rw [hS₁S] at hS₁
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₁
    have hsub : S.subgroupOf N = (P2 : Subgroup N) := by
      rw [← hP2]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    exact ⟨hS₁.1, hS2, by have h := P2.not_dvd_index; rwa [← hsub] at h⟩
  have hchar : CFSG.QuasithinUnique.CharTwo N := by
    have hH := hS.toGlobal.d1Global.charTwo H hopt.ext.pair.isTwoLocal
    have hQ := pCoreOf_le_pCoreOf hNH (hopt.core_le.trans le_sup_right)
    intro g hg
    obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.mp hg
    exact hQ (hH (Subgroup.mem_inf.mpr ⟨hNH hgN, Subgroup.centralizer_le hQ hgC⟩))
  have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hBab : ∀ a ∈ zpowers x ⊔ zpowers z, ∀ b ∈ zpowers x ⊔ zpowers z, a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val (hpl.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨F, E, hFne, hF3, hFE, hEN, hE3, hEp, hFz, hBF, hFY⟩ :=
    L617P.exists_three_subgroup' hprime hB3 hBab hzB hz.pow_eq_one hBN hNp
      (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hchar) hY hq hzY
  have hY2M : pCoreOf 2 Y ≤ M := (pCoreOf_block_le hSsylow hY).trans hSM
  have hFM : F ≤ M := hFz.trans (centralizer_singleton_le hS hz)
  have hp5 := hS.p_ge
  have hEH : E ≤ H := hEN.trans hNH
  have h3 : 3 ∈ GLBBetaFour G :=
    three_mem_betaFour_of_twoLocal hopt.ext.pair.isTwoLocal hEH (by omega)
  obtain ⟨P₃, M₃, hloc₃, hEP₃⟩ :=
    exists_threeCore hS.toGlobal.d1Global h3 hE3
  have hs₃ := stronglyEmbedded_three_of_global hS.toGlobal h313 hloc₃
  have hEM₃ : E ≤ M₃ := hEP₃.trans (CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hloc₃)
  have hHM₃ : H ≤ M₃ :=
    hS.toGlobal.d1 3 h3 P₃ M₃ hloc₃.maxLocal hloc₃.core H hopt.ext.pair.isTwoLocal
      (le_trans (le_trans (by omega) hEp)
        (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hEH hEM₃)))
  by_cases h2 : 2 ≤ Open.pRank 3 M
  ·
    exfalso
    obtain ⟨R, hR3, hRM, hFR, hR2⟩ := exists_three_through hF3 hFM
    have hRne : R ⊓ M₃ ≠ ⊥ := fun h => hFne (eq_bot_iff.mpr (h ▸ le_inf hFR (hFE.trans hEM₃)))
    have hRM₃ := le_of_stronglyEmbedded_of_ne_bot hs₃ hR3 hRne
    have hMM₃ : M ≤ M₃ :=
      CFSG.LocalAnalysis.RankFourTheoremC.le_of_stronglyEmbedded hS.toGlobal.d2 h3 P₃
        hloc₃.maxLocal (hS.toGlobal.fullCore 3 P₃ M₃ hloc₃) hs₃ hS.loc.maxLocal.1
        (h2.trans (hR2.trans (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hRM hRM₃))))
    have hMeq : M₃ = M := hS.loc.maxLocal.2 M₃ hloc₃.maxLocal.1 hMM₃
    exact hopt.ext.pair.not_le (hMeq ▸ hHM₃)
  ·
    have hAB : HasPrimeConstraint (G := ↥M) p ∨ ¬ UniquePComponent p M := by
      by_cases hc : HasPrimeConstraint (G := ↥M) p
      · exact Or.inl hc
      · exact Or.inr fun hu => h2 (h1 G p P M x z (p65_plane65 hS hx hz) hc hu)
    obtain ⟨k, hk⟩ := hF3.exists_card_eq
    have hcop : Nat.Coprime p (Nat.card F) := by
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime Nat.prime_three).mpr (by omega))
    have hodd : Odd (Nat.card F) := by
      rw [hk]
      exact Odd.pow (by decide)
    exact hFY M hY2M (h65 G p P M x z hS hx hz hAB F hFne hFM hcop hodd hBF)

theorem stepL617_of_three
    (h313 : GL83NormalElementaryRankFour) (h1 : KFactSingleComponentThreeRank)
    (h65 : StepP65OddAB) : StepL617 :=
  stepL617_of_kfact' kFactBlocksInSylowCentralizerQS_holds
    (stepL617PrimeTop_of_three h313 h1 h65)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
