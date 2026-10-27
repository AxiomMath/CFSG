module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderLinear
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped MatrixGroups

theorem autControlAt_psl2 {f : ℕ} (hf : 2 ≤ f) [Finite PSL(2, GaloisField 2 f)]
    (T : Sylow 2 PSL(2, GaloisField 2 f)) :
    AutControlAt (T : Subgroup PSL(2, GaloisField 2 f)) := by
  have hB := CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf
  obtain ⟨hSE, -, hZcard, hTcard⟩ := benderBorel_sylowCenter hB T
  have : IsSimpleGroup PSL(2, GaloisField 2 f) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨MulEquiv.refl _⟩⟩)
  have hcard : Nat.card (Sylow 2 PSL(2, GaloisField 2 f)) =
      Nat.card (T : Subgroup PSL(2, GaloisField 2 f)) + 1 := by
    rw [CFSG.Walter.psl2_even_card_sylow (by omega), hTcard, pow_one]
  exact Omega.autControlAt_of_abelian hSE hcard
    (le_sylowCenter_of_card (by rw [hZcard, hTcard, pow_one]))

theorem centPairAt_psl2 {f : ℕ} (hf : 2 ≤ f) [Finite PSL(2, GaloisField 2 f)]
    (T : Sylow 2 PSL(2, GaloisField 2 f)) :
    CentPairAt (T : Subgroup PSL(2, GaloisField 2 f)) := by
  have hB := CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf
  obtain ⟨-, -, hZcard, hTcard⟩ := benderBorel_sylowCenter hB T
  exact centPairAt_of_abelian (le_sylowCenter_of_card (by rw [hZcard, hTcard, pow_one]))

theorem autControlAt_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) (T : Sylow 2 X) : AutControlAt (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  exact autControlAt_of_mulEquiv e (autControlAt_psl2 hf) T

theorem centPairAt_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) (T : Sylow 2 X) : CentPairAt (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  exact centPairAt_of_mulEquiv e (centPairAt_psl2 hf) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
