module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCensus
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Conj

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.M22Std.OutCheck

theorem autCensus_pinned
    {F1 : Subgroup (Carrier .M22)}
    (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) : AutCensus (Carrier .M22) F1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := normalizer_involution_census hF
  obtain ⟨hcov, hF1, hb, hout⟩ := normalizer_involution_classes hF
  refine ⟨h0, h1, h2, h3, h4, h5, ?_, hF1, hb, hout, hcov⟩
  intro cf hcf μ ν hμ hν
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcf
  rcases hcf with rfl | rfl | rfl | rfl | rfl
  · exact normalizer_involution_isConj hF (n := 15) (by simp [classTable]) hμ hν
  · exact normalizer_involution_isConj hF (n := 30) (by simp [classTable]) hμ hν
  · exact normalizer_involution_isConj hF (n := 90) (by simp [classTable]) hμ hν
  · exact normalizer_involution_isConj hF (n := 60) (by simp [classTable]) hμ hν
  · exact normalizer_involution_isConj hF (n := 180) (by simp [classTable]) hμ hν

theorem autSylowCensus_m22 :
    AutSylowWith (fun Y _ F => AutCensus Y F) (Carrier .M22) := by
  obtain ⟨S₀, t, F1, hp, hidx, hmem1, W⟩ := sylowWitness_m22_pinned
  exact AutSylowWith.of_sylow AutCensus.isoInv hp hidx W (autCensus_pinned hmem1)

end CFSG.EvenSporadicStandard.M22Std
