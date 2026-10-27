module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Perfect
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane SmallRankSylowTwo smallRankR
  smallRankIsQ8D8)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem p65_plane65 (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) :
    Plane65 p P M x z where
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

private theorem p65_covering_of_le_core (hS : Situation G p P M) (hx : Point P M x)
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

theorem p65_mSide (hKA : KFactP65Single) (hKB : KFactP65Multi)
    (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) {T : Subgroup G}
    (hT : SmallRankSylowTwo P M T) (hp5 : p = 5) (hR : smallRankIsQ8D8 (smallRankR x z T))
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p) {F : Subgroup G}
    (hF : IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) M F) :
    Open.pRank p (P : Subgroup G) ≤ Open.pRank p (M ⊓ normalizer (F : Set G)) ∧
    ((∀ m ∈ M, ∃ d ∈ rankThreePrimeCore p M, ∃ n ∈ M ⊓ normalizer (F : Set G), m = d * n) ∨
     (∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ p →
        ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧
          ∀ g ∈ M ⊓ normalizer (E : Set G), g * a * g⁻¹ ∉ zpowers b)) := by
  have hprime := hS.prime
  have hpl := p65_plane65 hS hx hz
  have hchar : M ⊓ centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hS.toGlobal.d1Global.charTwo M hS.loc.maxLocal.1
  by_cases hcon : HasPrimeConstraint (G := M) p
  ·
    obtain ⟨h1, h2⟩ := p65_covering_of_le_core hS hx hz hf hfp hF
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
        hKA G p P M x z T hpl hchar hp5 hT hR huniq F hF.1.1 hcop hF.1.2.2
      obtain ⟨h1, h2⟩ := p65_covering_of_le_core hS hx hz hf hfp hF hFD
      exact ⟨h1, Or.inl h2⟩
    ·
      obtain ⟨K, hK, hKp, hKL⟩ : ∃ K : Subgroup (M ⧸ primeComplementCore (G := M) p),
          IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ K ≠ L₀ := by
        by_contra hno
        push Not at hno
        exact huniq ⟨L₀, hL₀, hL₀p, hno⟩
      obtain ⟨h1, h2⟩ := hKB G p P M x z hpl ⟨K, L₀, hK, hKp, hL₀, hL₀p, hKL⟩
      exact ⟨h1 f F hf hfp hF, Or.inr h2⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
