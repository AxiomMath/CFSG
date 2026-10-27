module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StructA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.StructB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Two

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem struct_of_derived_le_layer [Finite G] (cfg : H2Cfg G t v J)
    (hF : fittingSubgroup G = ⊥) (hJE : ⁅J, J⁆ ≤ layer G) :
    (∃ L : Subgroup G, IsComponent L ∧ layer G = L) ∨ ∃ S₁ : Subgroup G, H2Two G t v J S₁ := by
  classical
  obtain ⟨S₀, hS₀, hJ0S₀⟩ : ∃ S₀ : Subgroup G, IsComponent S₀ ∧ ⁅J, J⁆ ≤ S₀ := by
    by_contra hcon
    push_neg at hcon
    have hlayer : layer G ≤ centralizer ((⁅J, J⁆ : Subgroup G) : Set G) := by
      rw [CFSG.layer.eq_sSup]
      refine sSup_le fun L hL => ?_
      rcases derived_le_component_or_rest cfg hF hJE hL with hle | hle
      · exact absurd hle (hcon L hL)
      · have h2 : ⁅J, J⁆ ≤ centralizer ((L ⊔ L : Subgroup G) : Set G) :=
          hle.trans (rest_le_centralizer hL hL)
        exact le_trans le_sup_left (Subgroup.le_centralizer_iff.mp h2)
    have hbot : ⁅J, J⁆ ≤ (⊥ : Subgroup G) := by
      have h3 : ⁅J, J⁆ ≤ centralizer (layer G : Set G) :=
        Subgroup.le_centralizer_iff.mp hlayer
      rwa [centralizer_layer_eq_bot hF] at h3
    exact cfg.derived_ne_bot (le_bot_iff.mp hbot)
  have hM_prop : ∀ M : Subgroup G, IsComponent M → M ≠ S₀ →
      M ⊓ centralizer ({t} : Set G) ≤ kleinV t v ∧ kleinV t v ≤ M := by
    intro M hM hMne
    have hinf : M ⊓ centralizer ({t} : Set G) ≤ kleinV t v := by
      intro x hx
      refine cfg.mem_kleinV_of_centralizes_derived hx.2 ?_
      intro b hb
      exact component_commute hM hS₀ hMne x hx.1 b (hJ0S₀ hb)
    exact ⟨hinf, kleinV_le_of_inf_le cfg hF hM hinf⟩
  have hAtMostOne : ∀ M M' : Subgroup G, IsComponent M → IsComponent M' →
      M ≠ S₀ → M' ≠ S₀ → M = M' := by
    intro M M' hM hM' hMne hM'ne
    by_contra hne
    have hVM : kleinV t v ≤ M := (hM_prop M hM hMne).2
    have hVM' : kleinV t v ≤ M' := (hM_prop M' hM' hM'ne).2
    have hbot : kleinV t v ≤ (⊥ : Subgroup G) := by
      have hle : kleinV t v ≤ M ⊓ M' := le_inf hVM hVM'
      rwa [component_inf_eq_bot hF hM hM' hne] at hle
    exact cfg.kleinV_ne_bot (le_bot_iff.mp hbot)
  by_cases hOther : ∃ S₁ : Subgroup G, IsComponent S₁ ∧ S₁ ≠ S₀
  ·
    obtain ⟨S₁, hS₁, hS₁ne⟩ := hOther
    have hVS₁ : kleinV t v ≤ S₁ := (hM_prop S₁ hS₁ hS₁ne).2
    have hinfS₁ : S₁ ⊓ centralizer ({t} : Set G) ≤ kleinV t v := (hM_prop S₁ hS₁ hS₁ne).1
    have hS₀_le_C : S₀ ≤ centralizer ({t} : Set G) := by
      have h1 : S₀ ≤ centralizer (S₁ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (component_commute hS₀ hS₁ hS₁ne.symm a ha b hb).symm
      have h2 : centralizer (S₁ : Set G) ≤ centralizer (kleinV t v : Set G) :=
        Subgroup.centralizer_le hVS₁
      have h3 : centralizer (kleinV t v : Set G) ≤ centralizer ({t} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr cfg.t_mem_kleinV)
      exact h1.trans (h2.trans h3)
    have hS₀_le_J0 : S₀ ≤ ⁅J, J⁆ :=
      perfect_le_derived cfg hS₀_le_C (Subgroup.isPerfect_iff.mp hS₀.1.1)
    have hS₀_eq_J0 : S₀ = ⁅J, J⁆ := le_antisymm hS₀_le_J0 hJ0S₀
    have hcomp0 : IsComponent ⁅J, J⁆ := by
      rw [← hS₀_eq_J0]
      exact hS₀
    have hS₁ne_J0 : S₁ ≠ ⁅J, J⁆ := fun h => hS₁ne (h.trans hS₀_eq_J0.symm)
    have hcomps : ∀ M : Subgroup G, IsComponent M → M = S₁ ∨ M = ⁅J, J⁆ := by
      intro M hM
      by_cases hM₀ : M = S₀
      · exact Or.inr (hM₀.trans hS₀_eq_J0)
      · exact Or.inl (hAtMostOne M S₁ hM hS₁ hM₀ hS₁ne)
    have hlayer_eq : layer G = S₁ ⊔ ⁅J, J⁆ := by
      rw [← hS₀_eq_J0]
      refine le_antisymm ?_ ?_
      · rw [CFSG.layer.eq_sSup]
        refine sSup_le fun L hL => ?_
        by_cases hL₀ : L = S₀
        · rw [hL₀]; exact le_sup_right
        · rw [hAtMostOne L S₁ hL hS₁ hL₀ hS₁ne]; exact le_sup_left
      · exact sup_le (CFSG.LocalCores.component_le_layer hS₁)
          (CFSG.LocalCores.component_le_layer hS₀)
    exact Or.inr ⟨S₁, ⟨hS₁, hcomp0, hS₁ne_J0, hcomps, hlayer_eq, hVS₁, hinfS₁⟩⟩
  ·
    left
    refine ⟨S₀, hS₀, le_antisymm ?_ (CFSG.LocalCores.component_le_layer hS₀)⟩
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun L hL => ?_
    by_contra hLne
    exact hOther ⟨L, hL, fun h => hLne (le_of_eq h)⟩

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
