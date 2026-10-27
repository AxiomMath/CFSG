module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointStructure

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC (perfectCore perfectCore_le le_perfectCore
  commutator_perfectCore exists_perfect_le_map_eq commutator_map_subtype
  rankThreePrimeCore_map_subtype)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

@[expose] noncomputable def ptPre (p : ℕ) (x : G) (K : Subgroup (RedCent p x)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))).map
    (centralizer ({x} : Set G)).subtype

@[expose] noncomputable def ptKx (p : ℕ) (x : G) (K : Subgroup (RedCent p x)) : Subgroup G :=
  perfectCore (ptPre p x K)

private theorem ptPre_mem_iff {K : Subgroup (RedCent p x)} {g : G}
    (hg : g ∈ centralizer ({x} : Set G)) :
    g ∈ ptPre p x K ↔
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p) ⟨g, hg⟩ ∈ K := by
  constructor
  · intro h
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp h
    obtain rfl : c = ⟨g, hg⟩ := Subtype.ext hcg
    exact hc
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, h, rfl⟩

private theorem perfectCore_conj_mem {N : Subgroup G} {g : G} (hg : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    {n : G} (hn : n ∈ perfectCore N) : g * n * g⁻¹ ∈ perfectCore N := by
  have hmap : (perfectCore N).map (MulAut.conj g).toMonoidHom ≤ perfectCore N := by
    refine le_perfectCore ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hg k (perfectCore_le N hk)
    · rw [← Subgroup.map_commutator, commutator_perfectCore N]
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn)

theorem ptKx_le_centralizer (p : ℕ) (x : G) (K : Subgroup (RedCent p x)) :
    ptKx p x K ≤ centralizer ({x} : Set G) :=
  (perfectCore_le (ptPre p x K)).trans (Subgroup.map_subtype_le _)

theorem ptKx_perfect (p : ℕ) (x : G) (K : Subgroup (RedCent p x)) :
    ⁅ptKx p x K, ptKx p x K⁆ = ptKx p x K :=
  commutator_perfectCore (ptPre p x K)

theorem ptKx_normal (p : ℕ) (x : G) {K : Subgroup (RedCent p x)} (hK : K.Normal) :
    centralizer ({x} : Set G) ≤ normalizer ((ptKx p x K : Subgroup G) : Set G) := by
  have hPreC : ptPre p x K ≤ centralizer ({x} : Set G) := Subgroup.map_subtype_le _
  have hN : ∀ d ∈ centralizer ({x} : Set G), ∀ m ∈ ptPre p x K, d * m * d⁻¹ ∈ ptPre p x K := by
    intro d hd m hm
    have hmC : m ∈ centralizer ({x} : Set G) := hPreC hm
    have hdm : d * m * d⁻¹ ∈ centralizer ({x} : Set G) :=
      (centralizer ({x} : Set G)).mul_mem ((centralizer ({x} : Set G)).mul_mem hd hmC)
        ((centralizer ({x} : Set G)).inv_mem hd)
    rw [ptPre_mem_iff hdm]
    have hm' := (ptPre_mem_iff hmC).mp hm
    have heq : (⟨d * m * d⁻¹, hdm⟩ : centralizer ({x} : Set G)) =
        (⟨d, hd⟩ : centralizer ({x} : Set G)) * (⟨m, hmC⟩ : centralizer ({x} : Set G)) *
          (⟨d, hd⟩ : centralizer ({x} : Set G))⁻¹ := Subtype.ext (by simp)
    rw [heq, map_mul, map_mul, map_inv]
    exact hK.conj_mem _ hm' _
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact perfectCore_conj_mem (hN c hc) hn
  · intro hn
    have hc' : c⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hc
    have h := perfectCore_conj_mem (hN c⁻¹ hc') hn
    have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
    rwa [e] at h

theorem ptKx_map (p : ℕ) (x : G) {K : Subgroup (RedCent p x)} (hK : ⁅K, K⁆ = K) :
    ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) = K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact (ptPre_mem_iff c.2).mp (perfectCore_le (ptPre p x K) (Subgroup.mem_subgroupOf.mp hc))
  · obtain ⟨A, hAK, hAmap, hAperf⟩ := exists_perfect_le_map_eq
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))
      (K := K.comap (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)))
      (J := K)
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K).ge hK
    have hAle : A ≤ (ptKx p x K).subgroupOf (centralizer ({x} : Set G)) := by
      intro a ha
      rw [Subgroup.mem_subgroupOf]
      have hA1 : A.map (centralizer ({x} : Set G)).subtype ≤ ptPre p x K := Subgroup.map_mono hAK
      have hA2 : A.map (centralizer ({x} : Set G)).subtype ≤ ptKx p x K :=
        le_perfectCore hA1 (commutator_map_subtype A hAperf)
      exact hA2 (Subgroup.mem_map_of_mem _ ha)
    calc K = A.map (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) :=
          hAmap.symm
      _ ≤ _ := Subgroup.map_mono hAle

theorem ptKx_not_le [Fact p.Prime] {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)}
    (hK : PPointReduced p M x R K) : ¬ ptKx p x K ≤ M := by
  intro hle
  have hq : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hK.component.2.2.1
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq
  apply hK.not_le
  calc K = ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) :=
          (ptKx_map p x hperf).symm
    _ ≤ redCentM p M x :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono _ (le_inf (ptKx_le_centralizer p x K) hle))

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
