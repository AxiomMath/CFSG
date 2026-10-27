module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZK0Phase
import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

namespace D1OneLieKZeroData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {P' : Sylow p G} {H₁ S : Subgroup G}

theorem plusCore_facts (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)} (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) :
    d1PlusCore p H₁ L ≤ H₁ ⊓ M ∧ H₁ ≤ Subgroup.normalizer (d1PlusCore p H₁ L : Set G) ∧
      GLBPrimeCore p H₁ ≤ d1PlusCore p H₁ L := by
  have : L.Normal := hLn
  have hCY₀ := hc.centralizer_le hLn hJL hZ
  have hOM : primeComplementCore (G := H₁) p ≤ (H₁ ⊓ M).subgroupOf H₁ := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hc.escape.primeCore_le
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨m, hm, hmh⟩ := hCY₀ hh
    have hker : m⁻¹ * h ∈ primeComplementCore (G := H₁) p := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H₁) p), MonoidHom.mem_ker, map_mul,
        map_inv, hmh, inv_mul_cancel]
    have hmem := ((H₁ ⊓ M).subgroupOf H₁).mul_mem hm (hOM hker)
    rw [mul_inv_cancel_left] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · have hsub : (d1PlusCore p H₁ L).subgroupOf H₁ = (Subgroup.centralizer
        (L : Set (H₁ ⧸ primeComplementCore (G := H₁) p))).comap
          (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) :=
      Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective _
    have : ((d1PlusCore p H₁ L).subgroupOf H₁).Normal := by
      rw [hsub]
      exact Subgroup.Normal.comap inferInstance _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp this
  · intro n hn
    have hk : (⟨n, glbPrimeCore_le p H₁ hn⟩ : H₁) ∈ primeComplementCore (G := H₁) p := by
      rw [← glbPrimeCore_subgroupOf]
      exact Subgroup.mem_subgroupOf.mpr hn
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H₁) p)
        ⟨n, glbPrimeCore_le p H₁ hn⟩ = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hk
    refine ⟨⟨n, glbPrimeCore_le p H₁ hn⟩, ?_, rfl⟩
    change QuotientGroup.mk' _ _ ∈ Subgroup.centralizer _
    rw [h1]
    exact Subgroup.one_mem _

theorem d1MapPCore_le (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S) (hK : KFactOneLie)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hWK : d1MapPCore p M H ≤ K)
    (h3₁ : D1PhaseThree p P' M H₁ S) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) :
    d1MapPCore p M H₁ ≤ L := by
  have hd := hc.data
  have h3 := hd.toPhaseThree hK
  have hRY : R ⊓ pCorePreimage p M ≤ d1LiftX p H R K := by
    rintro r ⟨hrR, hrY⟩
    have hrH : r ∈ H := hd.cfg.ext.le_H hrR
    have hrK : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hrH⟩ ∈ K :=
      hWK ⟨⟨r, hrH⟩, hrY, rfl⟩
    exact ⟨⟨r, hrH⟩, ⟨hrR, hrK⟩, rfl⟩
  have hle : R ⊓ pCorePreimage p M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    (inf_le_right.trans (pCorePreimage_le p M)).trans (localGroup_le_normalizer_pCoreOf 2 M)
  rintro _ ⟨⟨y, hyH₁⟩, hyY, rfl⟩
  have hyY' : y ∈ ((R ⊓ pCorePreimage p M ⊔ pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [h3.inf_sup_twoCore_eq h84 hD2]
    exact hyY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hyY'
  obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hyY'
  have haX : a ∈ d1LiftX p H R K := hRY ha
  have haH₁ : a ∈ H₁ := hc.liftX_le_H₁ haX
  have hqN : q ∈ GLBPrimeCore p H₁ := h3₁.twoCore_M_le_glbPrimeCore hq
  have hqH₁ : q ∈ H₁ := glbPrimeCore_le p H₁ hqN
  have hsplit : (⟨a * q, hyH₁⟩ : H₁) = ⟨a, haH₁⟩ * ⟨q, hqH₁⟩ := rfl
  have hq1 : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨q, hqH₁⟩ = 1 :=
    (mk'_primeComplementCore_eq_one_iff p ⟨q, hqH₁⟩).mpr hqN
  rw [hsplit, map_mul, hq1, mul_one, ← hJL]
  exact ⟨⟨a, haH₁⟩, Subgroup.mem_subgroupOf.mpr (le_nclIn (d1LiftX_le_H p H R K) haX), rfl⟩

theorem plusCore_le_and_commutator (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (h3₁ : D1PhaseThree p P' M H₁ S) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hL : IsComponentOf L ⊤) (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L)
    (hZ : Subgroup.center L = ⊥) :
    d1PlusCore p H₁ L ≤ pCoreCentralizerPreimage p M ∧
      ⁅d1PlusCore p H₁ L, nclIn H₁ (d1LiftX p H R K)⁆ ≤ pCoreOf 2 H₁ := by
  have hYK := h3₁.pCorePreimage_le_inf h84 hD2
  obtain ⟨hNHM, hHN, -⟩ := hc.plusCore_facts hLn hJL hZ
  have hWL := hc.d1MapPCore_le hK h84 hD2 hWK h3₁ hJL
  have key : ∀ n ∈ d1PlusCore p H₁ L, ∀ y ∈ pCorePreimage p M,
      n * y * n⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
    intro n hn y hy
    have hyH : y ∈ H₁ := (hYK hy).1
    have h1 : n * y * n⁻¹ * y⁻¹ ∈ pCorePreimage p M :=
      (pCorePreimage p M).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCorePreimage p M (hNHM hn).2) y).mp hy) ((pCorePreimage p M).inv_mem hy)
    obtain ⟨n', hn', rfl⟩ := hn
    have hyL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨y, hyH⟩ ∈ L :=
      hWL ⟨⟨y, hyH⟩, hy, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hn' _ hyL
    have h2 : (n' : G) * y * (n' : G)⁻¹ * y⁻¹ ∈ GLBPrimeCore p H₁ :=
      (mk'_primeComplementCore_eq_one_iff p (n' * ⟨y, hyH⟩ * n'⁻¹ * ⟨y, hyH⟩⁻¹)).mp
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]; group)
    exact h3₁.pCorePreimage_inf_le ⟨h1, h2⟩
  refine ⟨fun n hn => (pCoreCentralizerPreimage_facts p M).2.2.2 n (hNHM hn).2 (key n hn), ?_⟩
  rw [← hc.nclIn_eq_of_le hL hLn hJL hZ inf_le_right hY]
  refine CFSG.AGLEmbedding.commutator_nclIn_le (inf_le_right.trans hc.liftX_le_H₁) hHN
    (localGroup_le_normalizer_pCoreOf 2 H₁) ?_
  rw [Subgroup.commutator_le]
  intro n hn y hy
  rw [commutatorElement_def]
  exact h3₁.twoCore_M_le h3₁.twoCore_inf (key n hn y hy.1)

theorem pCoreCentralizer_inf_le (hc : D1OneLieKZeroData p P M H R Rbar K P' H₁ S)
    (hK : KFactOneLie) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥) (hWK : d1MapPCore p M H ≤ K)
    (hU3 : ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)))
    (h3₁ : D1PhaseThree p P' M H₁ S) {L : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)}
    (hLn : L.Normal)
    (hJL : ((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) = L) (ψ : L ≃* K)
    (hψ : ∀ (j : G) (hj : j ∈ nclIn H (d1LiftX p H R K))
      (hjL : QuotientGroup.mk' (primeComplementCore (G := H₁) p) ⟨j, hc.nclIn_le hj⟩ ∈ L),
      ((ψ ⟨_, hjL⟩ : K) : H ⧸ primeComplementCore (G := H) p) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨j, nclIn_le_self H _ hj⟩) :
    pCoreCentralizerPreimage p M ⊓ H₁ ≤ d1LiftX p H R K ⊔ d1PlusCore p H₁ L :=
  hc.toEsc.pCoreCentralizer_inf_le hK h84 hD2 hY hWK hU3 h3₁ hLn hJL ψ hψ

end D1OneLieKZeroData

end CFSG.AGLEmbedding
