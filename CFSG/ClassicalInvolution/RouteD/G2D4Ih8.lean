module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem ih8G2D4_of_maxNormalizer (hM : G2D4MaxNormalizer p) : Ih8G2D4 p f := by
  intro hp2 hq G _ _ _ Ω hΩ _ htrans t k e hMod ht
  obtain ⟨M⟩ := hMod
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 ht k he M.ψ M.ker_le_center
  have hsurj : Function.Surjective M.ψ := M.surj
  have hZ : Subgroup.center (modelUniv t k p e Fact.out).K = ⊥ :=
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 ht k he
  have ht' : (t = .G2 ∧ 5 ≤ p ^ e) ∨ t = .trialityD4 := by
    rcases ht with h | h
    · refine Or.inl ⟨h, ?_⟩
      rcases M.exp_eq with h' | ⟨h', -⟩
      · rw [h']
        exact hq
      · exact absurd (h.symm.trans h') (by decide)
    · exact Or.inr h
  have hcoatom : ∀ R ∈ M.cls,
      IsCoatom (Subgroup.normalizer (R : Set (modelUniv t k p e Fact.out).K)) :=
    fun R hR => hM t k e M.admissible hp2 ht' R (M.cls_sub hR)
  refine ⟨?_, ?_⟩
  ·
    intro K hK K' hK'
    obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
    obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
    obtain ⟨g, hg⟩ := htrans _ hK _ hK'Ω
    obtain ⟨g', rfl⟩ := hsurj g
    have h1 : (conjSub g' R).map M.ψ = K' := by
      rw [← conjSub_map M.ψ g' R]
      exact hg
    subst h1
    obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_comap hinj hz
    obtain ⟨c', hc'z, hc'⟩ := isUniqueInvolution_comap hinj hz'
    have hcc : c' = c := hinj (hc'z.trans hcz.symm)
    rw [hcc] at hc'
    rw [conjSub_eq_of_same_involution hc hc' hZ (hcoatom R hR)]
  ·
    have hcoatomG : ∀ K ∈ Ω, IsCoatom (Subgroup.normalizer (K : Set G)) := by
      intro K hK
      obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
      rw [normalizer_map_of_bijective M.ψ hinj hsurj R]
      exact isCoatom_map_of_bijective M.ψ hinj hsurj (hcoatom R hR)
    exact edgeless_or_connected_of_coatom (r := Disconnected.dAdj Ω) hΩ.conjInvariant htrans
      hcoatomG
      (fun g K J h => by
        rcases h with h | h
        · exact Or.inl (omegaNbr_conj hΩ.conjInvariant h g)
        · exact Or.inr (omegaNbr_conj hΩ.conjInvariant h g))
      (fun K J h => Disconnected.dAdj_symm h) (fun K J h => Disconnected.ne_of_dAdj h)

end CFSG.ClassicalInvolution.G2D4Models
