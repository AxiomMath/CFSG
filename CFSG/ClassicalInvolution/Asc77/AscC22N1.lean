module

public import CFSG.ClassicalInvolution.Asc77.AscC22G13
import CFSG.ClassicalInvolution.Asc77.AscSCH28
public import CFSG.ClassicalInvolution.Asc77.AscC22P3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement MatrixGroups

namespace C22N

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem nonempty_psuLayer_of_omegaLie {Φ : Set (Subgroup G)} (D : OmegaLie p f Φ)
    (hcard : D.card = 1) (i : Fin D.card) (hit : D.tag i = .PSU) (hir : D.rank i = 4)
    (hie : D.exp i = f) : Nonempty (C22G.PSULayer p f Φ) := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ)
      (ψ : (modelUniv t k p e Fact.out).K →* G),
      t = .PSU → k = 4 → e = f → ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
      ψ.range = omegaGen Φ →
      (∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D, L = R.map ψ) →
      Nonempty (C22G.PSULayer p f Φ) := by
    rintro t k e ψ rfl rfl rfl hker hr hf
    exact ⟨⟨ψ, hker, hr, hf⟩⟩
  refine key _ _ _ (D.hom i) hit hir hie (D.ker_le_center i) ?_ ?_
  · have h1 : ⨆ j, (D.hom j).range = (D.hom i).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j i])
        (le_iSup (fun j => (D.hom j).range) i)
    rw [← h1]
    exact D.generate
  · intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Subsingleton.elim j i
    exact ⟨R, hR, hLR⟩

theorem nonempty_psuLayer_of_layerOrth {c : G}
    (hOc : classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥)
    (hL : LayerOrthType p f Ω c 6 false) :
    Nonempty (C22G.PSULayer p f (exactFamily Ω c)) := by
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := T7Z.exists_omegaLie_of_layerOrth hOc hL
  have htn : t' = .PSU ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  exact nonempty_psuLayer_of_omegaLie D hcard i (hit.trans htn.1) (hir.trans htn.2) hie

theorem oddCore_layer_eq_bot_neg (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : ConjInvariant Ω) {c z : G} (hc1 : c ≠ 1)
    (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hL : LayerOrthType p f Ω c 6 false) (hzY : z ∈ exactLayer Ω c) (hz2 : z * z = 1)
    (hmove : ¬ ∀ y ∈ exactLayer Ω c, y * z = z * y) :
    classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥ := by
  have hcomm : ∀ n ∈ oddCoreOf (exactLayer Ω c), n * z = z * n := fun n hn =>
    T7Z.oddCore_commutes_of_alphaOf hΩ hc1 (A := Subgroup.closure ({c, z} : Set G))
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hα hn
  refine T7Z.oddCore_exactLayer_eq_bot SCH.oddCenterClassical hp2 hq (Or.inr rfl) hL hzY hcomm ?_
  intro hZ
  exact hmove (C22P.commutes_of_mem_zStar hzY hz2 hcomm hZ)

end C22N

end CFSG.ClassicalInvolution.Asc77
