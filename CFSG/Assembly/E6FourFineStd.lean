module

public import CFSG.Assembly.E6FourFineTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Tau
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChainO

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6 CFSG.Timmesfeld.LevisSpin
  CFSG.ClassicalInvolution.WeakCT
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Tau
open scoped Matrix MatrixGroups

set_option maxRecDepth 100000

namespace E6FourFine

section StdLayer

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

include hf in
theorem fine_tauDatum_all :
    OmegaMinus8Fine ℓ f (tauDatum L ℓ f hf).orbitGroup := by
  classical
  have h1S : (1 : Fin Tag.E6.rank) ∈ d4Support := by
    change (1 : Fin Tag.E6.rank) ≠ 0 ∧ (1 : Fin Tag.E6.rank) ≠ 5
    decide
  have h2S : (2 : Fin Tag.E6.rank) ∈ d4Support := by
    change (2 : Fin Tag.E6.rank) ≠ 0 ∧ (2 : Fin Tag.E6.rank) ≠ 5
    decide
  have h3S : (3 : Fin Tag.E6.rank) ∈ d4Support := by
    change (3 : Fin Tag.E6.rank) ≠ 0 ∧ (3 : Fin Tag.E6.rank) ≠ 5
    decide
  have h4S : (4 : Fin Tag.E6.rank) ∈ d4Support := by
    change (4 : Fin Tag.E6.rank) ≠ 0 ∧ (4 : Fin Tag.E6.rank) ≠ 5
    decide
  refine CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_orbitGroup_of_datum_four
    (τ := Tag.E6) (Or.inr (Or.inl rfl))
    (tauDatum L ℓ f hf) (m := 4) le_rfl (CompsPTwoDChainO.twoDChainRecog_all hf le_rfl) bTau
    bTau_root bTau_injective iform_bTau ?_ ?_ ?_ ?_ ?_
  ·
    ext β
    constructor
    · intro hβ
      rw [GenFixedRootDatum.simpleRootsJ_eq] at hβ
      obtain ⟨j, hj, rfl⟩ := d4Aux.mem_unionSimpleRoots_iff.1 hβ
      have hjS : j ∈ d4Support := d4Aux_support ▸ hj
      rcases d4Support_cases hjS with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact single_mem_simpleRootsJ hf h1S
      · exact single_mem_simpleRootsJ hf h3S
      · exact single_mem_simpleRootsJ hf h2S
      · exact single_mem_simpleRootsJ hf h4S
  ·
    intro j hj
    fin_cases j
    · exact (theta_single_tau hf h1S).trans (by rw [gam_one]; rfl)
    · exact (theta_single_tau hf h3S).trans (by rw [gam_three]; rfl)
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · exact (theta_single_tau hf h2S).trans (by rw [gam_two]; rfl)
  · exact (theta_single_tau hf h4S).trans (by rw [gam_four]; rfl)
  ·
    intro j k hjk
    fin_cases j <;> fin_cases k <;>
      first
      | (exfalso; revert hjk; decide)
      | exact exists_frame_E6 (by decide)

include hf in
private theorem fine_fixE6_dN_all :
    OmegaMinus8Fine ℓ f (fixE6 ℓ f (dN L)) := by
  rw [fixE6_dN hf]
  exact fine_tauDatum_all hf

include hf in
theorem exists_fix_swap13_fine :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      OmegaMinus8Fine ℓ f (fixE6 ℓ f n₂) :=
  ⟨dN L, acts_dN, E6Fix_dN hf, fine_fixE6_dN_all hf⟩

include hf in
theorem exists_fix_swap03_fine :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      OmegaMinus8Fine ℓ f (fixE6 ℓ f n₂) := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)
  · rw [fixE6_conj map_conj_d4TrialityRep frob_d4TrialityRep]
    exact OmegaMinus8Fine.map_conj _ (fine_fixE6_dN_all hf)

include hf in
theorem exists_fix_swap01_fine :
    ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      OmegaMinus8Fine ℓ f (fixE6 ℓ f n₂) := by
  have hR := map_conj_mul (L := L) map_conj_d4TrialityRep map_conj_d4TrialityRep
  have hF : Units.map (entrywiseHom (iterateFrobenius L ℓ f))
      (d4TrialityRep L * d4TrialityRep L) = d4TrialityRep L * d4TrialityRep L := by
    rw [map_mul, frob_d4TrialityRep]
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L * (d4TrialityRep L * d4TrialityRep L)⁻¹,
    ?_, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · exact E6Fix.conj hR hF (E6Fix_dN hf)
  · rw [fixE6_conj hR hF]
    exact OmegaMinus8Fine.map_conj _ (fine_fixE6_dN_all hf)

end StdLayer

end E6FourFine

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
