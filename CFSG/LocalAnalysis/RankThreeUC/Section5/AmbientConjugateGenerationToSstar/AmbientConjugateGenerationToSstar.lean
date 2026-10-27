module


public import CFSG.LocalAnalysis.RankThreeUC.Section5.ActionVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.AmbientConjugateGenerationToSstar

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem generated {P T B Q : Subgroup G} (hP : P.Normal) (hQP : Q ≤ P)
    (hgen : P = Subgroup.closure
      {x : G | ∃ s ∈ twoCoreCommutator T B, x ∈ Q.map (MulAut.conj s).toMonoidHom}) :
    Subgroup.closure
      {x : P | ∃ s : Sstar P T B, x ∈ (Q.subgroupOf P).map s.val.toMonoidHom} = ⊤ := by
  set S := Subgroup.closure
      {x : P | ∃ s : Sstar P T B, x ∈ (Q.subgroupOf P).map s.val.toMonoidHom} with hS
  have hle : P ≤ S.map P.subtype := by
    conv_lhs => rw [hgen]
    rw [Subgroup.closure_le]
    rintro x ⟨s, hs, q, hq, rfl⟩
    have hsn : s ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.normalizer_eq_top]; trivial
    have hxP : (MulAut.conj s).toMonoidHom q ∈ P := by
      simpa [MulAut.conj_apply] using hP.conj_mem q (hQP hq) s
    refine ⟨⟨_, hxP⟩, ?_, rfl⟩
    refine Subgroup.subset_closure ⟨⟨Subgroup.normalizerMonoidHom P ⟨s, hsn⟩, ?_⟩, ?_⟩
    · exact ⟨⟨s, hsn⟩, hs, rfl⟩
    · refine ⟨⟨q, hQP hq⟩, hq, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom, MulAut.conj_apply]
      rfl
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  rw [← this]; exact hy

end CFSG.LocalAnalysis.RankThreeUC.Section5.AmbientConjugateGenerationToSstar
