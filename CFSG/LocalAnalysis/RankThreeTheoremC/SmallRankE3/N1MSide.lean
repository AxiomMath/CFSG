module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (IsMaxFInvariantIn IsFInvariantIn
  p65_fusionIsSylowIn_conj p65_mem_normalizer_of_map_eq)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem fusionIsSylowIn_of_isMax (hS : Sit G p P M) (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (hcon : HasPrimeConstraint (G := M) p) {f : ℕ} (hf : f.Prime) (hfp : f ≠ p)
    {F : Subgroup G} (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    fusionIsSylowIn f F (GLBPrimeCore p M) := by
  have hprime := hS.prime
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore p M
  have hpl : SmallRankPlane p (P : Subgroup G) x z := hS.plane hx hz
  have hB3 : IsPGroup p B := IsPGroup.of_card (n := 2) hpl.card_eq
  have hBM : B ≤ M := (sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)).trans hS.sylow_le
  obtain ⟨⟨hFM, hF2, hBF⟩, hmax⟩ := hF
  have hF3 : Nat.Coprime p (Nat.card F) := by
    obtain ⟨k, hk⟩ := hF2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime hf).mpr hfp.symm)
  have hFD : F ≤ D :=
    CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hS.ne_two hcon hB3 hBM
      (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
        rw [← hord]
        exact pow_orderOf_eq_one y)) hFM hF3 hBF
  have hD3 : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hprime).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime p M)
  have hBD : B ≤ normalizer (D : Set G) :=
    hBM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M)
  obtain ⟨R, hRsyl, hFR, hBR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hprime hf hB3 hD3 hBD hFD hF2 hBF
  have hRF : R = F :=
    hmax R ⟨hRsyl.1.trans (CFSG.AGLEmbedding.glbPrimeCore_le p M), hRsyl.2.1, hBR⟩ hFR
  rwa [← hRF]

theorem p65_covering_of_le_core (hS : Sit G p P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {f : ℕ} (hf : f.Prime) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) (hFD : F ≤ rankThreePrimeCore p M) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
      ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  set D : Subgroup G := rankThreePrimeCore p M with hDdef
  have hpl : SmallRankPlane p (P : Subgroup G) x z := hS.plane hx hz
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

theorem p65_mSide (hKA : KFactP65SingleAt p) (hmulti : NoTwoComponentsAt p)
    (hS : Sit G p P M) (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
      ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n := by
  have hprime := hS.prime
  have hpl := hS.plane65E3 hx hz
  have hchar := hS.charTwo
  by_cases hcon : HasPrimeConstraint (G := M) p
  ·
    exact p65_covering_of_le_core hS hx hz hf hfp hF
      (fusionIsSylowIn_of_isMax hS hx hz hcon hf hfp hF).1
  · obtain ⟨L₀, hL₀, -, -, hL₀p, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component
      hS.setting.kProper M (fun h => hx.not_centralizer_le (h ▸ le_top)) p hprime hcon
    by_cases huniq : ∃ L : Subgroup (M ⧸ primeComplementCore (G := M) p), IsComponentOf L ⊤ ∧
        p ∣ Nat.card L ∧ ∀ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
          IsComponentOf K ⊤ → p ∣ Nat.card K → K = L
    ·
      have hcop : Nat.Coprime (Nat.card F) (2 * p) := by
        haveI : Fact f.Prime := ⟨hf⟩
        obtain ⟨k, hk⟩ := hF.1.2.1.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right
          ((Nat.coprime_primes hf Nat.prime_two).2 hf2) ((Nat.coprime_primes hf hprime).2 hfp))
      have hFD : F ≤ rankThreePrimeCore p M :=
        hKA G P M x z hpl hchar (fun Q hQX hQ1 hQ2 => hS.three_rank_le Q hQX hQ1 hQ2) huniq F hF.1.1 hcop hF.1.2.2
      exact p65_covering_of_le_core hS hx hz hf hfp hF hFD
    ·
      exfalso
      obtain ⟨K, hK, hKp, hKL⟩ : ∃ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
          IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ K ≠ L₀ := by
        by_contra hno
        push Not at hno
        exact huniq ⟨L₀, hL₀, hL₀p, hno⟩
      exact hmulti hS.p_ge G hS.setting P M hS.situation x z hx hz ⟨K, L₀, hK, hKp, hL₀, hL₀p, hKL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
