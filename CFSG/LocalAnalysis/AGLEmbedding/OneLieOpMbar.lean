module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem commutator_mem_of_mem_pCoreCentralizerPreimage {M : Subgroup G} {d y : G}
    (hd : d ∈ pCoreCentralizerPreimage p M) (hy : y ∈ pCorePreimage p M) :
    d * y * d⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨m, hm, rfl⟩ := hd
  obtain ⟨m', hm', rfl⟩ := hy
  have hc := Subgroup.mem_centralizer_iff.mp hm _ hm'
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (m * m' * m⁻¹ * m'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  exact coe_mem_pCoreOf_two_of_mk_eq_one _ h1

theorem mk_mem_centralizer_d1MapPCore {M H : Subgroup G}
    (hQN : pCoreOf 2 M ≤ GLBPrimeCore p H) {d : G} (hdD : d ∈ pCoreCentralizerPreimage p M)
    (hdH : d ∈ H) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨d, hdH⟩ ∈
      Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h1 := (mk'_primeComplementCore_eq_one_iff p (⟨d, hdH⟩ * y * ⟨d, hdH⟩⁻¹ * y⁻¹)).mpr
    (hQN (commutator_mem_of_mem_pCoreCentralizerPreimage hdD hy))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end General

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1CompCore.commutator_nclIn_le (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1CompCore p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) :
    ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H := by
  rw [← hd.nclIn_eq inf_le_right hY]
  exact CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans (d1LiftX_le_H p H R K))
    (le_normalizer_glbPrimeCore p H) (localGroup_le_normalizer_pCoreOf 2 H)
    (((Subgroup.commutator_mono le_rfl inf_le_left).trans
      (h3.commutator_pCorePreimage_le h84 hD2)).trans (h3.twoCore_M_le h3.twoCore_inf))

theorem D1OneLieData.commutator_nclIn_le (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) :
    ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H :=
  hd.toCore.commutator_nclIn_le (hd.toPhaseThree hK) h84 hD2 hY

theorem D1PhaseThree.d1MapPCore_eq (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) :
    d1MapPCore p M H = ((R ⊓ pCorePreimage p M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hYH : pCorePreimage p M ≤ H := (h.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  have hQN := h.twoCore_M_le_glbPrimeCore
  have hQ : ((pCoreOf 2 M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', ← glbPrimeCore_subgroupOf]
    exact Subgroup.comap_mono hQN
  calc d1MapPCore p M H = ((R ⊓ pCorePreimage p M ⊔ pCoreOf 2 M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
          rw [h.inf_sup_twoCore_eq h84 hD2]
          rfl
    _ = ((R ⊓ pCorePreimage p M).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊔
        ((pCoreOf 2 M).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
          rw [Subgroup.subgroupOf_sup (inf_le_right.trans hYH) (hQN.trans (glbPrimeCore_le p H)),
            Subgroup.map_sup]
    _ = _ := by rw [hQ, sup_bot_eq]

theorem D1CompCore.d1MapPCore_facts (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1CompCore p P M H R Rbar K) :
    IsPGroup p (d1MapPCore p M H) ∧
      d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∧
      K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      (pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ ↔
        d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥) := by
  have hYH : pCorePreimage p M ≤ H := (h3.pCorePreimage_le_inf h84 hD2).trans inf_le_left
  have heq := h3.d1MapPCore_eq h84 hD2
  have hRp : IsPGroup p R := hd.esc.isPGroup
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  have hX₀ : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) :=
    map_le_normalizer_map _ hYH (inf_le_right.trans (le_normalizer_pCorePreimage p M))
  refine ⟨?_, ?_, inf_le_right.trans
    ((hd.red.normalizer_inf_le_of_rankOne hd.noncyclic hzR hzK hzp hzc).trans hX₀),
    (hd.red.centralizer_le_of_rankOne hd.noncyclic hzR hzK hzp hzc).trans hX₀, ?_, ?_⟩
  · have hRY : IsPGroup p ((R ⊓ pCorePreimage p M).subgroupOf H) :=
      (hRp.to_le inf_le_left).comap_subtype
    rw [heq]
    exact hRY.map _
  · rw [heq, hd.rbar]
    exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  · intro hne
    exact ne_bot_of_le_ne_bot (map_mk_ne_bot_of_isPGroup h3.prime
      (inf_le_right.trans (d1LiftX_le_H p H R K))
      (hRp.to_le (inf_le_right.trans (d1LiftX_le p H R K))) hne)
      (le_inf (Subgroup.map_mono (Subgroup.comap_mono inf_le_left))
        ((Subgroup.map_mono (Subgroup.comap_mono inf_le_right)).trans
          hd.map_d1LiftX_eq_inf.le))
  · intro hne hbot
    apply hne
    rw [eq_bot_iff]
    rintro w ⟨hwY, -, hwK⟩
    rw [heq] at hwY
    obtain ⟨r, ⟨hrR, hrY⟩, rfl⟩ := hwY
    have hr : (r : G) ∈ pCorePreimage p M ⊓ d1LiftX p H R K := ⟨hrY, ⟨r, ⟨hrR, hwK⟩, rfl⟩⟩
    rw [hbot, Subgroup.mem_bot] at hr
    rw [Subgroup.mem_bot, show r = 1 from Subtype.ext hr, map_one]

theorem D1OneLieData.d1MapPCore_facts (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K) :
    IsPGroup p (d1MapPCore p M H) ∧
      d1MapPCore p M H ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∧
      K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      (pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ ↔
        d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥) :=
  hd.toCore.d1MapPCore_facts (hd.toPhaseThree hK) h84 hD2

theorem D1CompCore.inf_le_sup_glbPrimeCore (h3 : D1PhaseThree p P M H R)
    (hd : D1CompCore p P M H R Rbar K)
    (hC : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    pCoreCentralizerPreimage p M ⊓ H ≤ R ⊔ GLBPrimeCore p H := by
  rintro d ⟨hdD, hdH⟩
  have hcR := hC (mk_mem_centralizer_d1MapPCore h3.twoCore_M_le_glbPrimeCore hdD hdH)
  rw [hd.rbar] at hcR
  obtain ⟨r, hr, hrd⟩ := hcR
  have hn : (r : G)⁻¹ * d ∈ GLBPrimeCore p H :=
    (mk'_primeComplementCore_eq_one_iff p (r⁻¹ * ⟨d, hdH⟩)).mp
      (by rw [map_mul, map_inv, hrd, inv_mul_cancel])
  have e : d = r * ((r : G)⁻¹ * d) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hr hn

theorem D1OneLieData.inf_le_sup_glbPrimeCore (hK : KFactOneLie)
    (hd : D1OneLieData p P M H R Rbar K)
    (hC : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) :
    pCoreCentralizerPreimage p M ⊓ H ≤ R ⊔ GLBPrimeCore p H :=
  hd.toCore.inf_le_sup_glbPrimeCore (hd.toPhaseThree hK) hC

theorem D1OneLieData.inf_le_sup_d1PlusCore (hK : KFactOneLie)
    (hd : D1OneLieData p P M H R Rbar K)
    (hC : Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) :
    pCoreCentralizerPreimage p M ⊓ H ≤ R ⊔ d1PlusCore p H K := by
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  rintro d ⟨hdD, hdH⟩
  have hc := hC (mk_mem_centralizer_d1MapPCore (hd.toPhaseThree hK).twoCore_M_le_glbPrimeCore
    hdD hdH)
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
  obtain ⟨t, ⟨htR, -⟩, c, hcC, htc⟩ := hc
  rw [hd.cfg.rbar] at htR
  obtain ⟨r, hr, rfl⟩ := htR
  have hn : (r : G)⁻¹ * d ∈ d1PlusCore p H K := by
    refine ⟨r⁻¹ * ⟨d, hdH⟩, ?_, rfl⟩
    show QuotientGroup.mk' (primeComplementCore (G := H) p) (r⁻¹ * ⟨d, hdH⟩) ∈
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
    rw [map_mul, map_inv, ← htc, inv_mul_cancel_left]
    exact hcC
  have e : d = r * ((r : G)⁻¹ * d) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hr hn

theorem D1CompCore.d1PlusCore_le_and_commutator (h3 : D1PhaseThree p P M H R)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hd : D1CompCore p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K) :
    d1PlusCore p H K ≤ pCoreCentralizerPreimage p M ∧
      ⁅d1PlusCore p H K, nclIn H (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H := by
  have hYK := h3.pCorePreimage_le_inf h84 hD2
  obtain ⟨hNHM, hHN, -⟩ := hd.d1PlusCore_facts
  have key : ∀ n ∈ d1PlusCore p H K, ∀ y ∈ pCorePreimage p M,
      n * y * n⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
    intro n hn y hy
    have hyH : y ∈ H := (hYK hy).1
    have h1 : n * y * n⁻¹ * y⁻¹ ∈ pCorePreimage p M :=
      (pCorePreimage p M).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCorePreimage p M (hNHM hn).2) y).mp hy) ((pCorePreimage p M).inv_mem hy)
    obtain ⟨n', hn', rfl⟩ := hn
    have hyK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨y, hyH⟩ ∈ K :=
      hWK ⟨⟨y, hyH⟩, hy, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hn' _ hyK
    have h2 : (n' : G) * y * (n' : G)⁻¹ * y⁻¹ ∈ GLBPrimeCore p H :=
      (mk'_primeComplementCore_eq_one_iff p (n' * ⟨y, hyH⟩ * n'⁻¹ * ⟨y, hyH⟩⁻¹)).mp
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]; group)
    exact h3.pCorePreimage_inf_le ⟨h1, h2⟩
  refine ⟨fun n hn => (pCoreCentralizerPreimage_facts p M).2.2.2 n (hNHM hn).2 (key n hn), ?_⟩
  rw [← hd.nclIn_eq inf_le_right hY]
  refine CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans (d1LiftX_le_H p H R K)) hHN
    (localGroup_le_normalizer_pCoreOf 2 H) ?_
  rw [Subgroup.commutator_le]
  intro n hn y hy
  rw [commutatorElement_def]
  exact h3.twoCore_M_le h3.twoCore_inf (key n hn y hy.1)

theorem D1OneLieData.d1PlusCore_le_and_commutator (hK : KFactOneLie) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneLieData p P M H R Rbar K)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K) :
    d1PlusCore p H K ≤ pCoreCentralizerPreimage p M ∧
      ⁅d1PlusCore p H K, nclIn H (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H :=
  hd.toCore.d1PlusCore_le_and_commutator (hd.toPhaseThree hK) h84 hD2 hY hWK

end Config

end CFSG.AGLEmbedding
