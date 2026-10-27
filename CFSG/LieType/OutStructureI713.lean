module

public import CFSG.LieType.OutStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowFieldNormal

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem sylow_normal_outer_of_pRank_le_one_of_I_7_13_2_5 (h : I_7_13_2_5) :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      CFSG.Open.IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
          ∀ S : Sylow p (Outer K), (S : Subgroup (Outer K)).Normal := by
  intro K _ _ hsimple hnonab hcat p hp hp2 hrank S
  haveI : Finite (Outer K) := CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.finite_outer K
  rcases h K hsimple hnonab hcat p hp hp2 hrank with
    hOut | ⟨F, hEnorm, hFcyc, _hFbot, hEindex, _hFgen⟩ | ⟨hp3, hcyc, _hlift⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.sylow_normal_of_not_dvd hOut S
  · haveI : Fact p.Prime := ⟨hp⟩
    let φ : MulAut K →* Outer K := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
    have hφsurj : Function.Surjective φ :=
      QuotientGroup.mk'_surjective (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
    have hE'norm : (Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F)).Normal := hEnorm.map φ hφsurj
    have hE'cyc : IsCyclic ↥(Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F)) := by
      haveI : IsCyclic ↥F := hFcyc
      have hEq : Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) = F.map φ := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
      rw [hEq]
      exact isCyclic_of_surjective (φ.subgroupMap F) (φ.subgroupMap_surjective F)
    have hker : φ.ker ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F := by
      rw [show φ.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner K from
        QuotientGroup.ker_mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)]
      exact le_sup_left
    have hE'index : ¬ p ∣ (Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F)).index := by
      rw [Subgroup.index_map_eq (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) hφsurj hker]
      exact hEindex
    haveI : (Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F)).Normal := hE'norm
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.sylow_normal_of_normal_isCyclic_index
      (Subgroup.map φ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F)) hE'cyc hE'index S
  · haveI : IsCyclic (Outer K) := hcyc
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.sylow_normal_of_isCyclic S

end CFSG.LieType.OutStructure
