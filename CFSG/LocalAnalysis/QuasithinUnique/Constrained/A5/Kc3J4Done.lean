module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4H2B1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Inst
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336c
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336d
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Inst336
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ScanMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ReduceB

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem j4_cN
    : ∀ V : Subgroup ↥J, FpfV V → ¬ HasCommonFixedPt V →
    ∃ V' ∈ reps2A ++ reps2B0, ∃ g : ↥J, V = V'.map (cm g) := by
  intro V hV hnc
  obtain ⟨V', hV', g, hg⟩ := complete_of_pentagon_cover_b Certificates.certificate4029.basic
    [B1344, A85]
    {q : Row | ∃ w ∈ d4Reps.toList, q = toRow w.toVec} pent_reps_complete d4_hD4 V hV hnc
  refine ⟨V', ?_, g, hg⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hV'
  rcases hV' with rfl | rfl
  · exact List.mem_append_right _ B1344_mem_reps2B0
  · exact List.mem_append_left _ A85_mem_reps2A

theorem j4_hdB1
    : ∀ V' ∈ reps2B1, ClassRad V' ∨ NoNonHBlockAt Hj V' := by
  have hF := Certificates.certificate4029.basic
  intro V' hV'
  simp only [reps2B1, List.mem_cons, List.not_mem_nil, or_false] at hV'
  rcases hV' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr noNonHBlockAt_B56
  · exact Or.inr (B7.noNonHBlockAt_b7Explicit hF (by rw [hF.cardJ]; norm_num))
  · exact Or.inl (classRad_B336a hF)
  · exact Or.inl (classRad_B336b hF)
  · exact Or.inl (classRad_B336c hF)
  · exact Or.inl (classRad_B336d hF)
  · exact Or.inl (Dec2.classRad_B336 hF centralizer_fiveElt_eq_X0Sub.le)

theorem kc3For_j4_proved
    : Kc3For (Kc3Spor .J4) :=
  kc3For_j4_of_two_cases_b Certificates.certificate4029.basic reps2A reps2B1 reps2B0 j4_cH j4_cN
    j4_hdA j4_hdB1 j4_hdB0

end CFSG.QuasithinUnique.A5
