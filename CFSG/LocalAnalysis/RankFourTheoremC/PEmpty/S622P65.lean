module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Rank3
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Rank2
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Global
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Cent
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Coprime
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

@[expose] def S622KFactP65Single : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65 p P X x z → normalizer ((zpowers x ⊔ zpowers z : Subgroup A) : Set A) ≤ X →
    ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set A)) →
    (∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧
      p ∣ Nat.card L ∧ ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
        IsComponentOf K ⊤ → p ∣ Nat.card K → K = L) →
    ∀ W : Subgroup A, W ≤ X → Nat.Coprime p (Nat.card W) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set A) → W ≤ rankThreePrimeCore p X

@[expose] def S622KFactP65Rank4 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A)
    (f : ℕ) (Fs R : Subgroup A), Plane65 p P X x z →
    normalizer ((zpowers x ⊔ zpowers z : Subgroup A) : Set A) ≤ X →
    ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set A)) →
    f.Prime → f ≠ 2 → f ≠ p →
    IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs →
    zpowers x ⊔ zpowers z ≤ R → R ≤ X ⊓ normalizer (Fs : Set A) → IsPGroup p R →
    ¬ p ∣ (R.subgroupOf (X ⊓ normalizer (Fs : Set A))).index → 4 ≤ Open.pRank p R →
    IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A) → 4 ≤ Open.pRank f X

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem s622p65_plane65 (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) : Plane65 p P M x z where
  prime := hS.prime
  five_le := hS.p_ge
  catalog := catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper M
    (fun h => hx.not_le (h ▸ le_top))
  plane := plane_of_central hS hx hz
  sylow_le := hS.sylow_le
  z_central := hz.centralizes
  four_le := hS.four_le_pRank
  rank_centralizer := hx.pRank_centralizer_le hS
  sylow_centralizer := hx.sylow
  perfect := fun N _ hN => eq_top_of_isPGroup_quotient hS N hN

private theorem s622p65_covering_of_le_core (hS : Situation G p P M) (hx : Point P M x)
    (hz : Central P z) {f : ℕ} (hf : f.Prime) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) (hFD : F ≤ rankThreePrimeCore p M) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
      ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  set D : Subgroup G := rankThreePrimeCore p M with hDdef
  have hpl : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPlane p (P : Subgroup G) x z :=
    plane_of_central hS hx hz
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

theorem s622_mSide (hKA : S622KFactP65Single) (hKB : KFactP65Multi)
    (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z)
    (hnc : ¬ CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G)))
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
    ((∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n) ∨
     (∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ p →
        ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧
          ∀ g ∈ M ⊓ normalizer (E : Set G), g * a * g⁻¹ ∉ zpowers b)) := by
  have hprime := hS.prime
  have hpl := s622p65_plane65 hS hx hz
  by_cases hcon : HasPrimeConstraint (G := M) p
  ·
    obtain ⟨h1, h2⟩ := s622p65_covering_of_le_core hS hx hz hf hfp hF
      (fusionIsSylowIn_of_isMax hS hx hz hcon hf hfp hF).1
    exact ⟨h1, Or.inl h2⟩
  · obtain ⟨L₀, hL₀, -, -, hL₀p, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component
      hS.toGlobal.d1Global.kProper M (fun h => hx.not_le (h ▸ le_top)) p hprime hcon
    by_cases huniq : ∃ L : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf L ⊤ ∧
        p ∣ Nat.card L ∧ ∀ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
          IsComponentOf K ⊤ → p ∣ Nat.card K → K = L
    ·
      have hcop : Nat.Coprime p (Nat.card F) := by
        haveI : Fact f.Prime := ⟨hf⟩
        obtain ⟨k, hk⟩ := hF.1.2.1.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime hf).mpr hfp.symm)
      have hFD : F ≤ rankThreePrimeCore p M :=
        hKA G p P M x z hpl (normalizer_plane_le hS hx hz) hnc huniq F hF.1.1 hcop hF.1.2.2
      obtain ⟨h1, h2⟩ := s622p65_covering_of_le_core hS hx hz hf hfp hF hFD
      exact ⟨h1, Or.inl h2⟩
    ·
      obtain ⟨K, hK, hKp, hKL⟩ : ∃ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
          IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ K ≠ L₀ := by
        by_contra hno
        push Not at hno
        exact huniq ⟨L₀, hL₀, hL₀p, hno⟩
      obtain ⟨h1, h2⟩ := hKB G p P M x z hpl ⟨K, L₀, hK, hKp, hL₀, hL₀p, hKL⟩
      exact ⟨h1 f F hf hfp hF, Or.inr h2⟩

theorem s622Prop65_of_kfacts (hKA : S622KFactP65Single) (hKB : KFactP65Multi)
    (hKC : KFactP65RankThree) (hKD : KFactP65RankTwo) (hKE : S622KFactP65Rank4) :
    S622Prop65 := by
  intro G _ _ p P M x z hS hx hz hnc F hF1 hFM hcop hodd hBF
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
  obtain ⟨Fs, hFFs', hFsmax⟩ : ∃ Fs : Subgroup G, F ≤ Fs ∧
      IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M Fs := by
    classical
    obtain ⟨Fs, ⟨hFs, hFFs⟩, hmax'⟩ := Set.exists_max_image
      {F' : Subgroup G | IsFInvariantIn f (zpowers x ⊔ zpowers z) M F' ∧ F ≤ F'}
      (fun F' => Nat.card F') (Set.toFinite _)
      ⟨F, (show IsFInvariantIn f (zpowers x ⊔ zpowers z) M F from ⟨hFM, hFp, hBF⟩), le_rfl⟩
    refine ⟨Fs, hFFs, hFs, fun F' hF' hle => ?_⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (hmax' F' ⟨hF', hFFs.trans hle⟩)).symm
  have hN : normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤ M :=
    normalizer_plane_le hS hx hz
  have hmS := fun {F' : Subgroup G} (hF' : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F') =>
    s622_mSide hKA hKB hS hx hz hnc hf hf2 hfp hF'
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
      obtain ⟨E, hFE, hEp, hBE, hEO, hOM⟩ := p65_rank_three_enlarge hKC hS hx hz hf hf2 hfp hFp
        hF1 hBF hHM hFsp hFsM hBFs hFFs (by omega)
      exact hHM (p65_normalizer_le_of_enlarged hprime hf hB3 hmax hBF hOM hFE hEp hBE hEO)
    have hcyc := p65_centralizer_cyclic hKD hS hx hz hf hf2 hfp hFp hF1 hBF hHM hFsp hFsM hBFs
      hFFs hmax hrankH hRp hRM hBR hRFs hR4
    have h4 : 4 ≤ Open.pRank f M :=
      hKE G p P M x z f Fs R (s622p65_plane65 hS hx hz) hN hnc hf hf2 hfp hFsmax hBR hRH
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
    exact p65_final_contradiction p65_coprime_rank_two hprime (by have := hS.p_ge; omega) hf hf2
      hflt hpl.isElemAbelian hpl.card_eq hBR hRp hFp hFsp hFFs.le hFcyc hyF hyo hBF hBFs hRFs hrk
      hcyc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
