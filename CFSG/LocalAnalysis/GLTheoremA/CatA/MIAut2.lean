module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITD4
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10

section Clauses

@[expose] def TD4Inn : LargeEvenRawCont := fun R _ I _ =>
  ∀ (S : Type) [Group S], catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) →
    Nonempty (S ≃* R) → I ⊆ LargeEvenInnSet R

theorem canonTD4Inn {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    CAll lab (LargeEvenSimpleGuard TD4Inn) := by
  by_cases ht : lab.tag = .triD4
  · have h := TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab ht
    refine ((canonAll_iff_legacyAll hlab (fun hd => by
      rcases hd with hd | hd <;> simp [ht] at hd) _).2 h).mono ?_
    intro R _ I F hI hs hna S _ _ _
    exact hI hs hna
  · exact canonAll_simple_of_markedModel hlab fun R _ I F hs hna hM S _ hS ⟨e⟩ =>
      absurd (tag_triD4_of_isTD4 hM hS e) ht

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem td4_not_field_holds {L : Subgroup G} {g : G} (hTD4 : IsTD4 3 L) : ¬ FieldOn 3 g L := by
  intro hF
  obtain ⟨lab, hlab, R, _, I, F, θ, hs, hna, ⟨hlt, -⟩, hMM⟩ :=
    Canonical.largeEvenMarking_exists_markedModel hF.2
  have h := tag_triD4_of_isTD4 hMM hTD4 θ
  rcases hlt with h' | h'
  · exact h' h
  · exact h' rfl

theorem td4_nonInnDiag_holds (hp : p.Prime) {X L : Subgroup G} {g : G}
    (hL : GLAPComponent p X L) (hTD4 : IsTD4 p L) (hNI : NonInner p g L) : NonInnDiag p g L := by
  refine ⟨hNI.1, fun hD => hNI.2 ?_⟩
  have hdiag : CFSG.Assembly.LargeEvenMarking (PQuot p L)
      fun _ _ _ I _ θ => ∃ φ ∈ I, LargeEvenInduces θ (indRel p L g) φ :=
    Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hh => hh g (Subgroup.mem_zpowers g)) hD.2
  have h1 := canon_marking_and_labelAll_simple (P' := TD4Inn)
    (fun lab hlab => canonTD4Inn hlab) hdiag
  obtain ⟨-, lab, hlab, R, _, I, F, θ, hs, hna, ⟨φ, hφ, hind⟩, hTD⟩ :=
    Canonical.largeEvenMarking_exists h1
  have hI : I ⊆ LargeEvenInnSet R := hTD (PSimple p L) hTD4 ⟨θ⟩
  have e := (induces_indRel_iff hNI.1 θ).1 hind
  have hmem : φ ∈ (MulAut.conj : R →* MulAut R).range := by
    obtain ⟨r, hr⟩ := hI hφ
    exact ⟨r, hr⟩
  rw [← indAut_mem_inner_iff hp hL hNI.1]
  rw [e] at hmem
  exact (ggCongr_mem_range_conj_iff θ _).1 hmem

end Clauses

end MI

end CFSG.LocalAnalysis.GLTheoremA
