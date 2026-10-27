module

public import CFSG.ClassicalInvolution.Asc77.AscC22G7
public import CFSG.ClassicalInvolution.Asc77.AscS22G
public import CFSG.ClassicalInvolution.Asc77.AscMuTabSmallA
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace C22G

set_option linter.unusedSectionVars false

section Layer

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem layer_dstarConnected (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hAΩ : ∀ M ∈ Ω, AEmpty Ω M) {u : G} (hu2 : u * u = 1)
    (hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G)
    (hL : LayerOrthType p f Ω u 6 (piSign p f)) :
    T3.DStarConnected (oddQuotientFamily (exactPair Ω u)) := by
  have hGS := (S22.layer_section hp hq hΩ hAΩ hu2 hnc).1
  obtain ⟨t, n, hI, D, hcard, i, ht, hk⟩ := hL
  let hDo := LieSystemData.toOmegaLie D hGS.gen
  have hsurj := hDo.hom_surjective_of_gen hcard hGS.gen i
  let M : Ih8Model p f (oddQuotientFamily (exactPair Ω u)) (D.tag i) (D.rank i) (D.exp i) :=
    { isFundTag := D.isFundTag i
      admissible := D.admissible i
      exp_eq := D.exp_eq i
      ψ := D.hom i
      ker_le_center := D.ker_le_center i
      surj := hsurj
      cls := hDo.cls i
      cls_sub := fun _ hR => hR.1
      mem_iff := fun _ => hDo.mem_iff_exists_cls hcard i
      cls_conj := fun _ hR g => hDo.cls_conj hGS.hyp.conjInvariant i hR g }
  cases hπ : piSign p f
  · rw [hπ] at hI
    obtain ⟨rfl, rfl⟩ := (MuTab.isOrth_six_false t n).mp hI
    exact ih8_dstarConnected_psu4 hGS.hyp hp hq (MuTab.pow_mod_four_of_piSign_false hp hπ) M ht hk
  · rw [hπ] at hI
    obtain ⟨rfl, rfl⟩ := (MuTab.isOrth_six_true t n).mp hI
    exact ih8_dstarConnected_psl4 hGS.hyp hp hq (MuTab.piSign_true_iff.mp hπ) M ht hk

end Layer

end C22G

end CFSG.ClassicalInvolution.Asc77
