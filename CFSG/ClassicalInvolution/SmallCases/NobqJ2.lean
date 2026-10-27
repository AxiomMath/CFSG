module

public import CFSG.ClassicalInvolution.SmallCases.NobqArr
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2
public import Certificates.Certificate10019
public import CFSG.ClassicalInvolution.SmallCases.NobqJ2Inputs
public import Certificates.Certificate9302
public import Certificates.Certificate9308
public import Certificates.Certificate3139
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J2
public meta import CFSG.ClassicalInvolution.SmallCases.NobqArr

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data
  CFSG.ClassicalInvolution.J2Proof

theorem cent2A_cqAll :
    all3 315 cent2ALevels (cqTestA 315 twoAArr cent2AWit) = true := by
  exact Certificates.certificate9302

theorem cent2A_witness :
    ∀ c ∈ cent2AChain.originalSubgroup, c * c = permTwoA →
    ∃ g ∈ cent2AChain.originalSubgroup, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
      c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ permTwoA := by
  have hgens : ∀ g ∈ [cent2AStrong[0]!, cent2AStrong[1]!],
      ∃ G ∈ cent2AChain.originalSubgroup, Rep 315 g G := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    have hmem : ∀ i < 2, permOfArr 315 cent2AStrong[i]! ∈ cent2AChain.originalSubgroup := by
      intro i hi
      rw [cent2AChain, ofArrays_originalSubgroup]
      exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hrep : ∀ i < 2, Rep 315 cent2AStrong[i]! (permOfArr 315 cent2AStrong[i]!) := fun i hi =>
      rep_permOfArr_of_chainOK cent2A_ok (by
        have : cent2AStrong.size = 5 := rfl
        omega)
    rcases hg with rfl | rfl
    · exact ⟨_, hmem 0 (by norm_num), hrep 0 (by norm_num)⟩
    · exact ⟨_, hmem 1 (by norm_num), hrep 1 (by norm_num)⟩
  have hws := closureA_rep cent2AChain.originalSubgroup _ hgens 4
  refine chain_forall_of_all3 (ofArrays_chainArrays cent2A_ok) (by norm_num) cent2A_ok
    (by show 3 ≤ 3; exact le_rfl) (fun i hi hi' => by
      have : i < 3 := hi'
      omega) ?_ cent2A_cqAll
  intro t g ht hp hgg
  exact cqTestA_sound rep_permTwoA ht hws hp hgg

theorem noUniqueInvNormal_J2P :
    NoUniqueInvNormal P := by
  obtain ⟨hcov, -, he1, -, he2⟩ := inner_classes
  refine noUniqueInvNormal_of_reps P [permA, permTwoA] ?_ hcov ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact permA_mem
    · exact permTwoA_mem
  · intro r hr hrP N
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨N0, hN0, hcard, hrN⟩ := cent2B_structure
      rw [← he1] at hN0 hcard
      exact not_uniqueInvNormal_of_card_eq_two_mul P _ hrP N0 hN0 hcard hrN N
    · exact not_uniqueInvNormal_of_witness_ambient P _ hrP _ he2 cent2A_witness N

theorem noUniqueInvNormal_J2 :
    NoUniqueInvNormal CFSG.Blueprint.NativeSporadic.J2 :=
  NoUniqueInvNormal.of_mulEquiv nativeEquivP noUniqueInvNormal_J2P

end CFSG.ClassicalInvolution.Nobq
