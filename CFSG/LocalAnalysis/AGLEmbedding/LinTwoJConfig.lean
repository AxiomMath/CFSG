module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStar
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoConfig
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.PairPrimeCoreCommutator

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section GLevel

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R X : Subgroup G}

theorem D1PhaseThree.commutator_glbPrimeCore_le_twoCore (h : D1PhaseThree p P M H R)
    (hXR : X ≤ R) (hXQ : ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal) :
    ⁅GLBPrimeCore p H, X⁆ ≤ pCoreOf 2 M :=
  h.toPair.commutator_primeCore_le_twoCore hXR hXQ

theorem inf_centralizer_le_sup_glbPrimeCore
    (hC : Subgroup.centralizer (((X.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    H ⊓ Subgroup.centralizer (X : Set G) ≤ X ⊔ GLBPrimeCore p H := by
  rintro k ⟨hkH, hkC⟩
  have hk : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hkH⟩ ∈
      Subgroup.centralizer (((X.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxk : (x : G) * k = k * x :=
      Subgroup.mem_centralizer_iff.mp hkC x (Subgroup.mem_subgroupOf.mp hx)
    rw [← map_mul, ← map_mul, show x * ⟨k, hkH⟩ = ⟨k, hkH⟩ * x from Subtype.ext hxk]
  obtain ⟨x, hx, hxk⟩ := hC hk
  obtain ⟨z, hz, hxz⟩ := (QuotientGroup.mk'_eq_mk' _).mp hxk
  have hzN : (z : G) ∈ GLBPrimeCore p H := by
    rw [glbPrimeCore_eq_primeComplementCoreOf]
    exact Subgroup.mem_map_of_mem H.subtype hz
  have hk' : k = (x : G) * z := by
    rw [← Subgroup.coe_mul, hxz]
  rw [hk']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx) hzN

end GLevel

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X : Subgroup G}

theorem D1L2Config.toD1JConfig (h : D1L2Config p n P M H R X) : D1JConfig p P M H R X := by
  have hp : p.Prime := Fact.out
  have hn : 1 ≤ n := by have := h.three_le; omega
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.toD1Escape.reducedNongeneration
  obtain ⟨K, hKn, hKe, hC, hXK⟩ := h.socle
  have h3 : D1PhaseThree p P M H R := h.ext.toPhaseThreeU h.glob
    (h.ext.primeCore_inf_eq_iff.mpr (primeComplementCore_eq_bot_of_psl2GF
      kFactL2UnipotentCentralizer Rbar _ hred h.three_le hKn hKe hC))
  have hXmap : (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
    rw [hXK, hRbar]
  have hne : X ≠ ⊥ := by
    rintro rfl
    have : K.Normal := hKn
    obtain ⟨e⟩ := hKe
    have hcard := (isElemAbelian_sylow_inf_of_psl2GF hn e Rbar).2
    rw [← hXmap, Subgroup.bot_subgroupOf, Subgroup.map_bot, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by omega : n ≠ 0) hp.one_lt
    omega
  have hCX : Subgroup.centralizer (((X.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :
          Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [hXmap]
    exact centralizer_sylow_inf_le_of_psl2GF kFactL2UnipotentCentralizer h.ext.ne_two hn hKn
      hKe hC Rbar
  exact ⟨h3, h.le_R, hne, h.normal_sup, h3.commutator_glbPrimeCore_le_twoCore h.le_R h.normal_sup,
    (inf_le_inf_right _ inf_le_left).trans (inf_centralizer_le_sup_glbPrimeCore hCX)⟩

end Config

theorem stmtToD1JConfig :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
      {M H R X : Subgroup G}, D1L2Config p n P M H R X → D1JConfig p P M H R X :=
  fun h => h.toD1JConfig

end CFSG.AGLEmbedding
