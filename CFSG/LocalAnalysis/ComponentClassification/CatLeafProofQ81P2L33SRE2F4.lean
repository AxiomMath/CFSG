module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2Open
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE2Tools
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Fusion
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.F4Pilot CFSG.SeitzReduction.F4Pilot.ClassReps
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open RootOps

variable {K : Type} [Field K]

theorem f4x_elt_ne_one (p : ℕ) :
    (⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ≠ 1 := by
  intro h
  have h' : pinnedX .F4 K (orbitCertRoot .F4 p) 1 = pinnedX .F4 K (orbitCertRoot .F4 p) 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (pinnedX_injective .F4 K (orbitCertRoot .F4 p) h')

theorem f4_frameT_not_isPGroup
    {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    ¬ IsPGroup 2 ↥(centralizer ({frameT K} : Set (adjointGroup .F4 K))) :=
  not_isPGroup_of_mem_closure_odd (x := ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩)
    (f4x_mem_closure_odd_of_two_le hf hK (t := frameT K)
      (fun v hv => Subtype.ext (f4x_central (Or.inr rfl) 1 hv))
      (fun _ h47 _ _ => Subtype.ext (rootDiagUnit_commute_pinnedX_one
        (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47)) ⟨by norm_num, le_refl 47⟩ 1)
    (f4x_elt_ne_one 47)

theorem f4_frameU_not_isPGroup
    {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    ¬ IsPGroup 2 ↥(centralizer ({frameU K} : Set (adjointGroup .F4 K))) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have e : (f4Phi (K := K)).symm (frameU K) = frameT K := by
    rw [MulEquiv.symm_apply_eq]
    exact (f4Phi_f4x_47_44 (K := K)).1.symm
  refine not_isPGroup_of_mulEquiv (f4Phi (K := K)).symm (frameU K) ?_
  rw [e]
  exact f4_frameT_not_isPGroup hf hK

theorem f4_frameTU_not_isPGroup
    {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    ¬ IsPGroup 2 ↥(centralizer ({frameTU K} : Set (adjointGroup .F4 K))) := by
  refine not_isPGroup_of_mem_closure_odd (x := ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩)
    (f4x_mem_closure_odd_of_two_le hf hK (t := frameTU K) (fun v hv => ?_)
      (fun a h47 h44 ha => ?_) ⟨by norm_num, le_refl 47⟩ 1) (f4x_elt_ne_one 47)
  · refine Subtype.ext ?_
    change (v : ModGL .F4 K) * (f4x K 47 1 * f4x K 44 1) = f4x K 47 1 * f4x K 44 1 * v
    rw [← mul_assoc, f4x_central (Or.inr rfl) 1 hv, mul_assoc, f4x_central (Or.inl rfl) 1 hv,
      mul_assoc]
  · refine Subtype.ext ?_
    change rootDiagUnit .F4 a * (f4x K 47 1 * f4x K 44 1) =
      f4x K 47 1 * f4x K 44 1 * rootDiagUnit .F4 a
    rw [← mul_assoc, f4x, rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h47, mul_assoc, f4x,
      rootDiagUnit_commute_pinnedX_one (f4_isRoot_pos ⟨by norm_num, by norm_num⟩).1 h44,
      mul_assoc]

theorem f4_frameV_not_isPGroup
    {f : ℕ} (hf : 2 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    ¬ IsPGroup 2 ↥(centralizer ({frameV K} : Set (adjointGroup .F4 K))) :=
  not_isPGroup_of_mem_closure_odd (x := ⟨f4x K 41 1, pinnedX_mem_adjointGroup _ _⟩)
    (f4x_mem_closure_odd_classV hf hK (p := 41) (by decide) 1) (f4x_elt_ne_one 41)

theorem f4_centralizer_not_isPGroup
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {y : adjointGroup .F4 K} (hy : orderOf y = 2) :
    ¬ IsPGroup 2 ↥(centralizer ({y} : Set (adjointGroup .F4 K))) := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by decide)
  by_cases hf2 : 2 ≤ f
  · obtain ⟨g, hg⟩ := exists_conj_mem_frameReps hy
    refine not_isPGroup_centralizer_of_isConj (a := g * y * g⁻¹)
      (isConj_iff.mpr ⟨g⁻¹, by group⟩) ?_
    simp only [frameReps, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h <;> rw [h]
    · exact f4_frameT_not_isPGroup hf2 hK
    · exact f4_frameU_not_isPGroup hf2 hK
    · exact f4_frameTU_not_isPGroup hf2 hK
    · exact f4_frameV_not_isPGroup hf2 hK
  · have hK2 : Nat.card K = 2 := by rw [hK, show f = 1 by omega, pow_one]
    exact not_isPGroup_of_mem_closure_odd (mem_closure_odd_of_orderOf_eq_two_F4_two hK2 hy) hy1

end CFSG.ComponentClassification.HarrisLit.L33.SR.E2

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem involutionCentralizerNotTwoGroup_F4
    : InvolutionCentralizerNotTwoGroup .F4 := by
  intro Y _ _ f hY _ c hc
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact SR.E2.not_isPGroup_of_mulEquiv e c
    (SR.E2.f4_centralizer_not_isPGroup hf hK (by rw [MulEquiv.orderOf_eq]; exact hc))

end CFSG.ComponentClassification.HarrisLit.L33.E2
