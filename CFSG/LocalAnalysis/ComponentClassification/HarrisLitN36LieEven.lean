module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Alt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.HarrisLit.Hin

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem concl_of_evenLie
    (hA : EvenLieInvolutionOddCoreFact)
    (hB : EvenLieOuterCoverFact) (h : Config G p m τ K) {t : StatedLieTag} {n f : ℕ}
    (hL : Blueprint.LieModel (G ⧸ center G) t n 2 f) : Concl G p m τ := by
  have := h.simple_bar
  by_cases hinn : τ ∈ innAut G
  ·
    exfalso
    have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
    obtain ⟨s, hs⟩ := h.bar_mem_innAut_iff.mpr hinn
    have hs2 : orderOf s = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) s, hs]
      exact h.orderOf_bar
    have heq : fixedPoints (quotAut τ) = centralizer ({s} : Set (G ⧸ center G)) := by
      rw [centralizer_eq_fixedPoints_conj, hs]
    have hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥ := by
      rw [heq]
      exact hA _ t n f hL s hs2
    obtain ⟨hB', -⟩ := h.isComponent_bar hO
    have hfree := CatLeaf.involutionCentralizersComponentFree_of_evenLieType
      ⟨t, n, f, admissible_of_lieModel' hL, hL⟩
    have key : ∀ H : Subgroup (G ⧸ center G), H = centralizer ({s} : Set (G ⧸ center G)) →
        ∀ B : Subgroup ↥H, IsComponent B → False := by
      rintro H rfl B hB
      exact hfree s hs2 B hB
    exact key _ heq _ hB'
  · rcases hB G h.quasisimple h.oddCore h.center_ne_bot t n f hL τ h.orderOf_eq hinn p m h.prime
        h.ne_two h.one_le h.sixteen_dvd K h.comp h.unique h.lieModel with ⟨h34, hZ⟩ | he8
    · exact Or.inr (Or.inr (Or.inl ⟨h34, hZ, hinn⟩))
    · exact rowFor_alt G p m τ K h ⟨8, by norm_num, he8⟩

end Config

end CFSG.ComponentClassification.HarrisLit.N36
