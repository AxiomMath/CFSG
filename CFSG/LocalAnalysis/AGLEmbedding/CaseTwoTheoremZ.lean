module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieOpMbar
import CFSG.LocalAnalysis.AGLEmbedding.ZNCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.commutator_nclIn_le (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥) :
    ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ ≤ pCoreOf 2 H := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have hJ : nclIn H (d1LayerX p H R) = nclIn H (pCorePreimage p M ⊓ d1LayerX p H R) :=
    le_antisymm (nclIn_le (hd.d1LayerX_le_nclIn hAut hS hKL h84 hD2 hmeet) (nclIn_le_self H _)
        (le_normalizer_nclIn H _))
      (nclIn_le (inf_le_right.trans (le_nclIn (d1LiftX_le_H p H R _))) (nclIn_le_self H _)
        (le_normalizer_nclIn H _))
  rw [hJ]
  exact CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans (d1LiftX_le_H p H R _))
    (le_normalizer_glbPrimeCore p H) (localGroup_le_normalizer_pCoreOf 2 H)
    (((Subgroup.commutator_mono le_rfl inf_le_left).trans
      (h3.commutator_pCorePreimage_le h84 hD2)).trans (h3.twoCore_M_le h3.twoCore_inf))

theorem D1CaseTwoDataAt.false_of_centralizer_le (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (huniq : D1UniqueOver H R (nclIn H (d1LayerX p H R)))
    (hmeet : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) ≠ ⊥)
    (hCV : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) : False := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have hXQ : (((R ⊓ pCorePreimage p M) ⊔ pCoreOf 2 M).subgroupOf M).Normal := by
    rw [h3.inf_sup_twoCore_eq h84 hD2]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (pCorePreimage_le p M)).mpr
      (le_normalizer_pCorePreimage p M)
  have hNX : ⁅GLBPrimeCore p H, R ⊓ pCorePreimage p M⁆ ≤ pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans (h3.commutator_pCorePreimage_le h84 hD2)
  have hCX : (H ⊓ M) ⊓ Subgroup.centralizer ((R ⊓ pCorePreimage p M : Subgroup G) : Set G) ≤
      R ⊔ GLBPrimeCore p H := by
    rintro g ⟨⟨hgH, -⟩, hgC⟩
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨g, hgH⟩ ∈
        Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [h3.d1MapPCore_eq h84 hD2, Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have hc : y * (⟨g, hgH⟩ : H) = ⟨g, hgH⟩ * y :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC (y : G) hy)
      rw [← map_mul, ← map_mul, hc]
    have hR := hCV hmem
    rw [hd.cfg.rbar] at hR
    obtain ⟨r, hr, hrg⟩ := hR
    have hn : (r : G)⁻¹ * g ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (r⁻¹ * ⟨g, hgH⟩)).mp
        (by rw [map_mul, map_inv, hrg, inv_mul_cancel])
    have e : g = r * ((r : G)⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hr hn
  exact h3.false_of_unique_over' inf_le_left le_rfl hXQ hNX hCX
    (hd.commutator_nclIn_le hAut hS hKL h84 hD2 hmeet) huniq hCGT hD2

theorem D1CaseTwoDataAt.mem_nclIn_of_unique (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (huniq : D1UniqueOver H R (nclIn H (d1LayerX p H R)))
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁)
    (hmeet : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥)
    {z : H} (hzR : (z : G) ∈ R) (hzp : orderOf z = p)
    (hzO : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)) :
    (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ := by
  have h3 := hd.toPhaseThree hAut hS hKL
  have : Fact p.Prime := ⟨h3.prime⟩
  have hNJ := hd.commutator_nclIn_le hAut hS hKL h84 hD2 fun L hL => huL L hL ▸ hmeet
  by_contra hzC'
  set C' := nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆
  have hMC' : M ≤ Subgroup.normalizer (C' : Set G) := le_normalizer_nclIn M _
  have hNJC' : ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ ≤ C' :=
    le_nclIn (hNJ.trans h3.twoCore_le)
  obtain ⟨hDM, hMD, hQD, -⟩ := pCoreCentralizerPreimage_facts p M
  have hQM : pCoreOf 2 M ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hME : M ≤ Subgroup.normalizer (((C' ⊔ pCoreOf 2 M) ⊓ pCoreCentralizerPreimage p M :
      Subgroup G) : Set G) :=
    (le_inf ((le_inf hMC' hMQ).trans (Subgroup.inf_normalizer_le_normalizer_sup C' _))
      hMD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hzE : (z : G) ∉ (C' ⊔ pCoreOf 2 M) ⊓ pCoreCentralizerPreimage p M := by
    intro hz
    have hzCQ : (z : G) ∈ ((C' ⊔ pCoreOf 2 M : Subgroup G) : Set G) := hz.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C' _ (hQM.trans hMC')] at hzCQ
    obtain ⟨c, hc, q, hq, hcq⟩ := hzCQ
    have hQcop : (Nat.card (pCoreOf 2 M)).Coprime p := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      rw [hk]
      exact Nat.Coprime.pow_left k
        ((Nat.coprime_primes Nat.prime_two h3.prime).mpr (Ne.symm h3.ne_two))
    have hzq : (z : G) * q⁻¹ ∈ C' := by
      rw [← hcq, mul_inv_cancel_right]
      exact hc
    exact hzC' (mem_of_mul_mem_of_coprime
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzp, pow_one]))
      hQcop (hQM.trans hMC') ((pCoreOf 2 M).inv_mem hq) hzq)
  have hSN : pCoreOf 2 H ≤ GLBPrimeCore p H := pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes h3.prime Nat.prime_two).mpr h3.ne_two) H
  exact h3.false_of_normal_of_commutator_le (inf_le_right.trans hDM) hME
    (le_inf le_sup_right hQD)
    (le_inf (hNJC'.trans le_sup_left)
      ((hNJ.trans hSN).trans (h3.glbPrimeCore_le_pCoreCentralizerPreimage h84 hD2))) hNJ
    (hd.inf_le_sup_of_not_mem hAut hS hKL hL₁ huL hmeet inf_le_right hME hzR hzp hzO hzE) huniq
    hCGT hD2

theorem D1CaseTwoDataAt.exists_mem_pCore (hAut : KFactCycAut) (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₁ : IsComponentOf L₁ ⊤)
    (huL : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) :
    ∃ z : H, (z : G) ∈ R ∧ orderOf z = p ∧ QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)).Normal := CFSG.pCore_normal
  have hO := hd.cfg.red.pCore_ne_bot_of_unique_of_aut (hAut _ _ _ _ hd.cfg.red hd.cfg.catalog)
      hd.cyclic hd.rank hL₁ huL
  obtain ⟨zb, hzbO, hzbp, -⟩ := exists_mem_centralizer_orderOf_eq CFSG.pCore_isPGroup hO
  have hzbR : zb ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal Rbar hzbO
  rw [hd.cfg.rbar] at hzbR
  obtain ⟨r, hr, hrz⟩ := hzbR
  refine ⟨r, hr, ?_, hrz ▸ hzbO⟩
  have hrN : ((r ^ p : H) : G) ∈ GLBPrimeCore p H := by
    refine (mk'_primeComplementCore_eq_one_iff p (r ^ p)).mp ?_
    rw [map_pow, hrz]
    have h1 := pow_orderOf_eq_one zb
    rwa [hzbp] at h1
  have hrR : ((r ^ p : H) : G) ∈ R := by
    rw [Subgroup.coe_pow]
    exact R.pow_mem hr p
  have hRN : ∀ x : G, x ∈ R → x ∈ GLBPrimeCore p H → x = 1 := by
    intro x hxR hxN
    obtain ⟨k, hk⟩ := (hd.cfg.ext.isPGroup) ⟨x, hxR⟩
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (GLBPrimeCore p H) := Subgroup.orderOf_dvd_natCard _ hxN
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((glbPrimeCore_coprime p H).pow_left k) h1 h2)
  have hrp : r ^ p = 1 := Subtype.ext (by simpa using hRN _ hrR hrN)
  refine orderOf_eq_prime hrp ?_
  intro hr1
  rw [hr1, map_one] at hrz
  rw [← hrz, orderOf_one] at hzbp
  exact hp.one_lt.ne hzbp

end Data

end CFSG.AGLEmbedding
