module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.ZNCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.d1LiftX_le_nclIn_of_unique (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)))
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hL₁X₀ : ¬ L₁ ≤ d1X0 p M H) (hL₂X₀ : L₂ ≤ d1X0 p M H)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥) :
    d1LiftX p H R L₂ ≤
      nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have hp := h3.prime
  have : Fact p.Prime := ⟨hp⟩
  set J₁ := nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) with hJ₁
  have hNJ : ⁅GLBPrimeCore p H, J₁⁆ ≤ pCoreOf 2 H :=
    CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans (d1LiftX_le_H p H R _))
      (le_normalizer_glbPrimeCore p H) (localGroup_le_normalizer_pCoreOf 2 H)
      (((Subgroup.commutator_mono le_rfl inf_le_left).trans
        (h3.commutator_pCorePreimage_le h84 hD2)).trans (h3.twoCore_M_le h3.twoCore_inf))
  set C' := nclIn M ⁅GLBPrimeCore p H, J₁⁆
  have hMC' : M ≤ Subgroup.normalizer (C' : Set G) := le_normalizer_nclIn M _
  have hNJC' : ⁅GLBPrimeCore p H, J₁⁆ ≤ C' := le_nclIn (hNJ.trans h3.twoCore_le)
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  set E := (C' ⊔ pCoreOf 2 M) ⊓ pCoreCentralizerPreimage p M
  have hME : M ≤ Subgroup.normalizer (E : Set G) :=
    (le_inf ((le_inf hMC' hMQ).trans (Subgroup.inf_normalizer_le_normalizer_sup C' _))
      hMD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hEC' : ∀ x : G, IsPGroup p (Subgroup.zpowers x) → x ∈ E → x ∈ C' := by
    intro x hx hxE
    have hxCQ : x ∈ ((C' ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hxE.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C' _ (hQM.trans hMC')] at hxCQ
    obtain ⟨c, hc, q, hq, hcq⟩ := hxCQ
    have hQcop : (Nat.card (pCoreOf 2 M)).Coprime p := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h3.ne_two))
    have hxq : x * q⁻¹ ∈ C' := by
      rw [← hcq, mul_inv_cancel_right]
      exact hc
    exact mem_of_mul_mem_of_coprime hx hQcop (hQM.trans hMC') ((pCoreOf 2 M).inv_mem hq) hxq
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set C := Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))
  set W := ((E ⊓ H).subgroupOf H).map π
  have hL₁n : L₁.Normal := (hd.cfg.red.normal_of_two_components hd.cyclic hL₁ hL₂ hL₁X₀ hL₂X₀).1
  have hCX₀ : C ≤ d1X0 p M H :=
    hd.cfg.red.centralizer_le_of_not_le hd.cyclic hL₁ hL₂ hL₁X₀ hL₂X₀
  have hiso := hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
      hd.cfg.catalog) hS hd.cyclic hd.rank hL₁
    hL₁X₀
  have hX₀W : d1X0 p M H ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) :=
    map_le_normalizer_map π inf_le_right ((le_inf (inf_le_right.trans hME)
      (inf_le_left.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf)
  obtain ⟨t, ⟨htV, htR, htL⟩, htp, -⟩ := exists_mem_centralizer_orderOf_eq
    (Rbar.isPGroup'.to_le (inf_le_right.trans inf_le_left)) hmeet
  have hWRC : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊔ C := by
    rintro _ ⟨x, hx, rfl⟩
    refine hd.cfg.red.centralizer_le_sup_of_caseTwo hKL hL₁ hiso (hd.cyclic L₁ hL₁) ⟨htR, htL⟩
      htp (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htV) ?_)
    exact mk_mem_centralizer_d1MapPCore h3.twoCore_M_le_glbPrimeCore hx.1.2 x.2
  by_cases hV : W ⊓ C = ⊥
  ·
    exfalso
    have hWp : IsPGroup p W := by
      intro w
      have hw : (w : H ⧸ primeComplementCore (G := H) p) ∈
          (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊔ C :
            Subgroup (H ⧸ primeComplementCore (G := H) p)) :
              Set (H ⧸ primeComplementCore (G := H) p)) := hWRC w.2
      rw [Subgroup.mul_normal] at hw
      obtain ⟨r, hrR, c, hcC, hrc⟩ := hw
      obtain ⟨k, hk⟩ := Rbar.isPGroup' ⟨r, hrR⟩
      have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hwC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ C := by
        have hc1 : QuotientGroup.mk' C c = 1 := by
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
          exact hcC
        have h1 : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈
            (QuotientGroup.mk' C).ker := by
          rw [MonoidHom.mem_ker, map_pow, ← hrc, map_mul, hc1, mul_one, ← map_pow, hk', map_one]
        rwa [QuotientGroup.ker_mk'] at h1
      have hwWC : (w : H ⧸ primeComplementCore (G := H) p) ^ p ^ k ∈ W ⊓ C :=
        ⟨W.pow_mem w.2 _, hwC⟩
      rw [hV, Subgroup.mem_bot] at hwWC
      exact ⟨k, Subtype.ext hwWC⟩
    have hRX₀ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ d1X0 p M H := by
      rw [hd.cfg.rbar]
      exact Subgroup.map_mono (Subgroup.comap_mono h3.le_inf)
    have hWR : W ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
      have h2 : IsPGroup p (W ⊔ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
        IsPGroup.to_sup_of_normal_left' hWp Rbar.isPGroup' (hRX₀.trans hX₀W)
      exact le_sup_left.trans (Rbar.is_maximal' h2 le_sup_right).le
    have hEH : E ⊓ H ≤ R ⊔ GLBPrimeCore p H := by
      rintro x ⟨hxE, hxH⟩
      have hxW : π ⟨x, hxH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
        hWR ⟨⟨x, hxH⟩, ⟨hxE, hxH⟩, rfl⟩
      rw [hd.cfg.rbar] at hxW
      obtain ⟨r, hr, hrx⟩ := hxW
      have hn : (r : G)⁻¹ * x ∈ GLBPrimeCore p H :=
        (mk'_primeComplementCore_eq_one_iff p (r⁻¹ * ⟨x, hxH⟩)).mp
          (by rw [map_mul, map_inv, hrx, inv_mul_cancel])
      have e : x = r * ((r : G)⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hr hn
    have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := pCoreOf_le_glbPrimeCore Nat.prime_two
      ((Nat.coprime_primes hp Nat.prime_two).mpr h3.ne_two) H
    exact h3.false_of_normal_of_commutator_le (inf_le_right.trans hDM) hME
      (le_inf le_sup_right hQD)
      (le_inf (hNJC'.trans le_sup_left)
        ((hNJ.trans hSN).trans (h3.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2))) hNJ hEH
      huniq hCGT hD2
  have hCV : C ≤ Subgroup.normalizer ((W ⊓ C : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p)) :=
    (le_inf (hCX₀.trans hX₀W) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hL₂W : L₂ ≤ W := (hd.cfg.red.le_of_le_centralizer hd.cyclic hL₁ hL₂ hL₁X₀ hL₂X₀
    inf_le_right hV hCV).trans inf_le_left
  rintro _ ⟨r, ⟨hrR, hrL⟩, rfl⟩
  obtain ⟨e, ⟨heE, -⟩, her⟩ := hL₂W hrL
  have hn : (e : G)⁻¹ * r ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (e⁻¹ * r)).mp
      (by rw [map_mul, map_inv, her, inv_mul_cancel])
  have hrp : IsPGroup p (Subgroup.zpowers (r : G)) :=
    hd.cfg.ext.isPGroup.to_le (Subgroup.zpowers_le.mpr hrR)
  have hre : (r : G) * ((e : G)⁻¹ * r)⁻¹ ∈ E := by
    rw [show (r : G) * ((e : G)⁻¹ * r)⁻¹ = e by group]
    exact heE
  exact hEC' r hrp (mem_of_mul_mem_of_coprime hrp (glbPrimeCore_coprime p H).symm
    (h3.primeCore_le.trans hME) ((GLBPrimeCore p H).inv_mem hn) hre)

theorem D1CaseTwoData.d1LiftX_le_nclIn_of_unique (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hd : D1CaseTwoData p P M H R Rbar)
    (huniq : D1UniqueOver H R (nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)))
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hL₁X₀ : ¬ L₁ ≤ d1X0 p M H) (hL₂X₀ : L₂ ≤ d1X0 p M H)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥) :
    d1LiftX p H R L₂ ≤
      nclIn M ⁅GLBPrimeCore p H, nclIn H (pCorePreimage p M ⊓ d1LayerX p H R)⁆ :=
  D1CaseTwoDataAt.d1LiftX_le_nclIn_of_unique (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS)
    (hKL := hKL) (h84 := h84) (hCGT := hCGT) (hD2 := hD2) (hd := hd.toAt) (huniq := huniq)
    (hL₁ := hL₁) (hL₂ := hL₂) (hL₁X₀ := hL₁X₀) (hL₂X₀ := hL₂X₀) (hmeet := hmeet)

end Data

end CFSG.AGLEmbedding
