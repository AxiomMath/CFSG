module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedD4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankSL2

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

theorem rankOne_eq_range_of_surj_param {K F : Type} [Group K] [Field F] {D : UniversalRootDatum K}
    {i : Fin D.rank} (φ : Matrix.SpecialLinearGroup (Fin 2) F →* K)
    (hu : ∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1))
    (hl : ∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1))
    (hpu : ∀ g ∈ D.rootGroup (Pi.single i 1), ∃ c, φ (sl2Upper c) = g)
    (hpl : ∀ g ∈ D.rootGroup (-Pi.single i 1), ∃ c, φ (sl2Lower c) = g) :
    rankOne D.rootGroup i = φ.range := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := hpu g hg
    exact ⟨_, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := hpl g hg
    exact ⟨_, rfl⟩
  · rintro _ ⟨s, rfl⟩
    have h : s ∈ (rankOne D.rootGroup i).comap φ :=
      (Subgroup.closure_le ((rankOne D.rootGroup i).comap φ)).2 (by
        rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
        · exact Subgroup.mem_sup_left (hu c)
        · exact Subgroup.mem_sup_right (hl c)) (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s)
    exact h

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

set_option linter.unusedSectionVars false


theorem nodeLevi_d4tw_long (hσ : ∀ c, σ (σ (σ c)) = c) : NodeLevi (twistedDatum σ) (ng 0) := by
  have hφ := slLong_injective hσ
  have hu : ∀ c, slLong σ hσ (sl2Upper c) ∈ (twistedDatum σ).rootGroup (Pi.single (ng 0) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_upper]
      exact xPar_single_two_mem_twisted hσ c.2
  have hl : ∀ c, slLong σ hσ (sl2Lower c) ∈ (twistedDatum σ).rootGroup (-Pi.single (ng 0) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_lower]
      exact xPar_neg_single_two_mem_twisted hσ c.2
  have hr : rankOne (twistedDatum σ).rootGroup (ng 0) = (slLong σ hσ).range := by
    refine rankOne_eq_range_of_surj_param (slLong σ hσ) hu hl ?_ ?_
    · intro g hg
      have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (Pi.single (ng 0) 1) :=
        Subgroup.mem_subgroupOf.1 hg
      obtain ⟨c, hc, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
        proj_single_two rho_single_two _).1 hg'
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      rw [slLong_val, slLongE_upper, hgc]
    · intro g hg
      have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (-Pi.single (ng 0) 1) :=
        Subgroup.mem_subgroupOf.1 hg
      obtain ⟨c, hc, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
        (isRoot_neg_single d4 (nd 2)) proj_neg_single_two
        rho_neg_single_two _).1 hg'
      refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
      rw [slLong_val, slLongE_lower, hgc]
  exact nodeLevi_of_range_sl2 hφ hr

theorem nodeLevi_d4tw_short (hσ : ∀ c, σ (σ (σ c)) = c) : NodeLevi (twistedDatum σ) (ng 1) := by
  have hφ := slShort_injective hσ
  have hu : ∀ c, slShort σ hσ (sl2Upper c) ∈ (twistedDatum σ).rootGroup (Pi.single (ng 1) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slShort_upper]
      have := xOuter_mem σ (s := 1) (Or.inl rfl) (hσ c)
      rw [one_smul] at this
      exact this
  have hl : ∀ c, slShort σ hσ (sl2Lower c) ∈ (twistedDatum σ).rootGroup (-Pi.single (ng 1) 1) :=
    fun c => by
      show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
      rw [Subgroup.mem_subgroupOf, slShort_lower]
      have := xOuter_mem σ (s := -1) (Or.inr rfl) (hσ c)
      rw [neg_one_smul] at this
      exact this
  have hr : rankOne (twistedDatum σ).rootGroup (ng 1) = (slShort σ hσ).range := by
    refine rankOne_eq_range_of_surj_param (slShort σ hσ) hu hl ?_ ?_
    · intro g hg
      have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (Pi.single (ng 1) 1) :=
        Subgroup.mem_subgroupOf.1 hg
      obtain ⟨c, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ (isRoot_single d4 (nd 0))
        proj_single_zero rho_single_zero_ne _).1 hg'
      refine ⟨c, Subtype.ext ?_⟩
      rw [slShort_upper, hgc, xOrbit_single]
    · intro g hg
      have hg' : (g : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (-Pi.single (ng 1) 1) :=
        Subgroup.mem_subgroupOf.1 hg
      obtain ⟨c, hgc⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ
        (isRoot_neg_single d4 (nd 0)) proj_neg_single_zero rho_neg_single_zero_ne _).1 hg'
      refine ⟨c, Subtype.ext ?_⟩
      rw [slShort_lower, hgc, xOrbit_neg_single]
  exact nodeLevi_of_range_sl2 hφ hr

theorem nodeLevi_d4tw (hσ : ∀ c, σ (σ (σ c)) = c) (i : Fin (Tag.rank .G2)) :
    NodeLevi (twistedDatum σ) i := by
  fin_cases i
  · exact nodeLevi_d4tw_long hσ
  · exact nodeLevi_d4tw_short hσ

end CFSG.AGLEmbeddingD2.Tits.GN516
