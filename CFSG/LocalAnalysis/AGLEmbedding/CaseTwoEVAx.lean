module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVAxis

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Cand

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.inf_centralizer_le (hd : D1CaseTwoDataAt p P M H R Rbar) {z : G}
    (hB0 : D1CzB0 p R z) :
    (P : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G) ≤ R := by
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  obtain ⟨S₀, hT⟩ := hB0
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.le_P
  rintro x ⟨hxP, hxC⟩
  have hTeq : (S₀ : Subgroup C) = (P : Subgroup G).subgroupOf C :=
    (S₀.is_maximal' P.isPGroup'.comap_subtype fun s hs => hRP (hT ▸ ⟨s, hs, rfl⟩)).symm
  have hx : (⟨x, hxC⟩ : C) ∈ (S₀ : Subgroup C) := by
    rw [hTeq]
    exact hxP
  rw [← hT]
  exact ⟨_, hx, rfl⟩

theorem D1CaseTwoDataAt.mem_pCorePreimage_of_axis (hd : D1CaseTwoDataAt p P M H R Rbar) {z w : G}
    (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) (hwR : w ∈ R) (hwp : orderOf w = p)
    (hΩP : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w)
    (hY : pCorePreimage p M ⊓ (P : Subgroup G) ≠ ⊥) :
    w ∈ pCorePreimage p M ∧ ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)),
      w * o * w⁻¹ * o⁻¹ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  have hwY : w ∈ pCorePreimage p M :=
    mem_of_inf_ne_bot P.isPGroup' (hd.cfg.ext.sylow_le.trans (le_normalizer_pCorePreimage p M))
      hY hwp hΩP
  refine ⟨hwY, fun o ho => ?_⟩
  have hOM : GLBPrimeCore p C ≤ M :=
    intersecting_local_primeCore_le p hp P hd.cfg.ext.sylow_le hd.cfg.ext.weakCore_le
      (hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRz hd.cfg.ext.le_M)))
  have hcO : w * o * w⁻¹ * o⁻¹ ∈ GLBPrimeCore p C := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ho)
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_glbPrimeCore p C (hRz hwR)) o).mp ho
  have hcY : w * o * w⁻¹ * o⁻¹ ∈ pCorePreimage p M := by
    have h1 : o * w⁻¹ * o⁻¹ ∈ pCorePreimage p M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCorePreimage p M (hOM ho)) _).mp
        (Subgroup.inv_mem _ hwY)
    have h2 : w * o * w⁻¹ * o⁻¹ = w * (o * w⁻¹ * o⁻¹) := by group
    rw [h2]
    exact Subgroup.mul_mem _ hwY h1
  exact ⟨pCorePreimage_inf_le_of_coprime (glbPrimeCore_coprime p C) ⟨hcY, hcO⟩,
    glbPrimeCore_le p C hcO⟩

end Cand

end CFSG.AGLEmbedding
