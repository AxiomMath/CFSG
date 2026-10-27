module

public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ02
public import CFSG.ClassicalInvolution.Q3.Q3T8AFZ

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank


theorem zLink3_transfer {Z : Type} [Group Z] {Ψ : Set (Subgroup Z)} {ι : Type}
    (D : Q3.LieSystemData3 ι Z Ψ) {i : ι} {c : Q3.CompData} (hc : D.kind i = c) :
    ∃ ψ : c.G →* Z, ψ.ker ≤ Subgroup.center c.G ∧ ψ.range = (D.hom i).range ∧
      ∀ R ∈ (D.kind i).fund, ∃ R' ∈ c.fund, R'.map ψ = R.map (D.hom i) :=
  ⟨castHom hc (D.hom i), castHom_ker_le_center hc _ (D.ker_le_center i), range_castHom hc _,
    fun _ hR => exists_map_castHom hc (D.hom i) hR⟩

theorem zLinkFacts3_proved : ZLinkFacts3 := by
  intro Z _ _ Ψ ι D hΩ hnt M₁ M₂ hM₁ hM₂ i R₁ R₂ hR₁ hR₂ h1 h2
  have hcard : ∀ L ∈ Ψ, Nat.card L = 24 := D.card_eq
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := zLink3_exists_sylow hcard hM₂
  have hne : M₁ ≠ M₂ := fun h => hM₂.2.1 h.symm
  have hv : padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 := (hΩ.omega4 M₁ hM₁ M₂ hM₂.1 hne).1
  have hnt' : ∀ u, IsUniqueInvolution M₁ u → ¬ IsUniqueInvolution M₂ u := fun u hu =>
    zLink3_not_twin hnt hM₁ hM₂ hu
  rcases D.valid i with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
  · by_cases ht2 : t = .G2
    · subst ht2
      obtain ⟨hn, -⟩ := hadm.2.2
      subst hn
      exact (zLink3_g2_false D hΩ hnt hc hM₁ hM₂ hR₁ hR₂ h1 h2).elim
    obtain ⟨ψ, hker, hrange, hfun⟩ := zLink3_transfer D hc
    obtain ⟨R₁', hR₁', e₁⟩ := hfun R₁ hR₁
    obtain ⟨R₂', hR₂', e₂⟩ := hfun R₂ hR₂
    have hM₁e : M₁ = R₁'.map ψ := h1.trans e₁.symm
    have hM₂e : M₂ = R₂'.map ψ := h2.trans e₂.symm
    subst hM₁e hM₂e
    by_cases ht4 : t = .trialityD4
    · subst ht4
      have hn : n = 0 := hadm.2.2
      subst hn
      refine ⟨fun u v hu hw => ?_, fun M hM R hR hMR => ?_⟩
      · rw [← hrange]
        exact zLink3_td4_range hadm ψ hker ⟨Q, hQJ, hQ8, hQN⟩ hu hw
          (fun huv => hnt' u hu (by rw [huv]; exact hw))
      · obtain ⟨R', hR', e⟩ := hfun R hR
        have hMe : M = R'.map ψ := hMR.trans e.symm
        rw [hMe]
        exact zLink3_td4_class hadm ψ hker hR₁' hR' (hcard _ hM₁) (hMe ▸ hcard M hM)
    · refine ⟨fun u v hu hw => ?_, fun M hM R hR hMR => ?_⟩
      · have hComm : ModelFacts.CommutingFundamentalGeneration 3 t n 1 := by
          by_cases hE : t = .twistedE6
          · subst hE
            exact ModelFacts.commutingFundamentalGeneration3_twistedE6 (by norm_num) hadm
          · exact ModelFacts.commutingFundamentalGeneration3_nonTwisted ht2 ht4 hE hfund hadm
        rw [← hrange]
        exact zLink3_model_range hfund hadm ht2 ht4 hComm ψ hker hR₁' hR₂' (hcard _ hM₁)
          (hcard _ hM₂.1) hne ⟨Q, hQJ, hQ8, hQN⟩ hv hu hw (hnt' u hu)
      · obtain ⟨R', hR', e⟩ := hfun R hR
        have hMe : M = R'.map ψ := hMR.trans e.symm
        rw [hMe]
        exact zLink3_model_class hfund hadm ht2 ht4 ψ hR₁' hR'
  · exfalso
    obtain ⟨ψ, hker, hrange, hfun⟩ := zLink3_transfer D hc
    obtain ⟨R₁', hR₁', e₁⟩ := hfun R₁ hR₁
    obtain ⟨R₂', hR₂', e₂⟩ := hfun R₂ hR₂
    have hR₁e : R₁' = ⊤ := Set.mem_singleton_iff.mp hR₁'
    have hR₂e : R₂' = ⊤ := Set.mem_singleton_iff.mp hR₂'
    apply hM₂.2.1
    calc M₂ = R₂.map (D.hom i) := h2
      _ = R₂'.map ψ := e₂.symm
      _ = R₁'.map ψ := by rw [hR₁e, hR₂e]
      _ = R₁.map (D.hom i) := e₁
      _ = M₁ := h1.symm
  · exfalso
    obtain ⟨ψ, hker, hrange, hfun⟩ := zLink3_transfer D hc
    obtain ⟨R₁', hR₁', e₁⟩ := hfun R₁ hR₁
    obtain ⟨R₂', hR₂', e₂⟩ := hfun R₂ hR₂
    have hM₁e : M₁ = R₁'.map ψ := h1.trans e₁.symm
    have hM₂e : M₂ = R₂'.map ψ := h2.trans e₂.symm
    subst hM₁e hM₂e
    exact zLink3_m11_false ψ hker (hcard _ hM₁) ⟨Q, hQJ, hQ8, hQN⟩ hv

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
