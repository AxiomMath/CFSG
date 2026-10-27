module

public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section CompI

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

structure D1CompI (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig p P M H R Rbar
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))

theorem D1CompI.isSimpleGroup (hd : D1CompI p P M H R Rbar K) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hd.comp.2.2.2
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hd.comp.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem D1CompI.exists_sylow (hd : D1CompI p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      ¬ IsCyclic (T₁ : Subgroup K) ∧ GLBCore p 1 (T₁ : Subgroup K) ≠ ⊤ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab⟩ := hd.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  exact ⟨T, hT, hsimple, hnonab, hcat, hTnc, hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT⟩

end CompI

end CFSG.AGLEmbedding
