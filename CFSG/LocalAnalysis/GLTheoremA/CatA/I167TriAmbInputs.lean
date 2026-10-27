module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPDich
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

set_option linter.unusedSectionVars false


theorem tri_glaPComponent_self {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {X : Subgroup Ω}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hchev : IsChevSimple 2 (PSimple p X)) :
    GLAPComponent p X X := by
  have hnt : Nontrivial (PSimple p X) := by
    rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t, n, f, hm⟩ | he | h33
    · exact (CFSG.LieType.Catalog.lieModel_finite_simple _ t n 2 f hm).2.1
    · obtain ⟨e⟩ := he
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      haveI := e.isSimpleGroup
      infer_instance
    · exact (CFSG.LieType.Catalog.lieModel_finite_simple _ .PSU 3 3 1
        (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h33⟩)).2.1
  exact glaPComponent_self_of_nontrivial hX hnt

theorem tri_innDiagOn_of_i144Inner {Ω : Type} [Group Ω] [Finite Ω] {X : Subgroup Ω} {x : Ω}
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω))
    (h : K144.I144Inner (PQuot 3 X) (barAut 3 X ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩)) :
    InnDiagOn 3 (Subgroup.zpowers x) X := by
  refine ⟨Subgroup.zpowers_le.2 hxN, ?_⟩
  have hrel : (fun a b : PQuot 3 X => barAut 3 X ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ a = b) =
      indRel 3 X x := by
    funext a b
    exact propext (FP.indRel_iff_barAut hxN a b).symm
  have h' : GLAMarking (PQuot 3 X) (fun _ _ _ I _ θ => ∃ φ ∈ I, GLAInduces θ (indRel 3 X x) φ) := by
    have hh : GLAMarking (PQuot 3 X) (fun _ _ _ I _ θ => ∃ φ ∈ I,
        GLAInduces θ (fun a b : PQuot 3 X => barAut 3 X ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ a = b) φ) := h
    rwa [hrel] at hh
  have h2 := MI.canon_marking_and_labelAll_simple (P' := MI.RawInnBody 3)
    (fun lab hlab => MI.canonRawInn' Nat.prime_three (by norm_num) hlab) h'
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ h2
  rintro _ R _ I _ θ ⟨⟨φ, hφI, hind⟩, hmul, hinv, hconj, _⟩ a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h1 : (1 : MulAut R) ∈ I := by simpa using hconj 1
  let S : Subgroup (MulAut R) :=
    { carrier := I, mul_mem' := fun ha hb => hmul _ ha _ hb, one_mem' := h1,
      inv_mem' := fun ha => hinv _ ha }
  refine ⟨φ ^ k, show φ ^ k ∈ I from S.zpow_mem hφI k, ?_⟩
  refine (MI.induces_indRel_iff (Subgroup.zpow_mem _ hxN k) θ).2 ?_
  rw [FP.indAut_zpow hxN k, map_zpow, (MI.induces_indRel_iff hxN θ).1 hind]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
