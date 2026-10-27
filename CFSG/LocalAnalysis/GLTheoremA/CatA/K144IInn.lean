module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416RBridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144I

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer
  glaPComponent_map_fixSubgroup glaPComponent_isComponent_of_le_layer)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_mono centerQuotAut centerQuotAut_mk
  center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.K144 (I144InnFact)

section Holds


theorem i144InnFact_holds : I144InnFact := by
  intro K _ _ α J hK hα3 hJ hcat hInn
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨labK, hXK, hin⟩ := innDiagKind_of_i144Inner hK hInn
  have hlam := CanonSubcomp.lambda2_of_hasLabel hXK
  suffices hn : labK.n = 1 from
    hasLabel_mono (T := fun lab => lab.n = 1) (fun l hl => by rw [hl]; exact hn) hXK
  by_contra hn1
  have hn2 : 2 ≤ labK.n := by have := hlam.1; omega
  have hqK := isQuasisimple_of_openQuasisimple hK
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hqK.2.1
  have hna : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := hqK.2.2
  have hcen : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := center_centerQuot_eq_bot hK
  have hβ3 : centerQuotAut K α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hJb : GLAPComponent 3 (fixSubgroup (centerQuotAut K α)) (J.map π) :=
    glaPComponent_map_fixSubgroup π (by rw [QuotientGroup.ker_mk']) α (centerQuotAut K α)
      (fun k => (centerQuotAut_mk K α k).symm) (QuotientGroup.mk'_surjective _) hp3 hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_map hp3 π hJ hJb
  have hpil : PerfectInLayer (centerQuotAut K α) := by
    by_cases hβ1 : centerQuotAut K α = 1
    · rw [hβ1]
      exact perfectInLayer_one_of_simple hsimple hna
    have hc := CanonSubcomp.markChar_eq_two_of_two_le hlam hn2
    have hLM := CanonSubcomp.markedModel_of_hasLabel hXK
    unfold CFSG.StandardType.MarkedModel at hLM
    rw [hc] at hLM
    rcases CanonSubcomp.exists_index_or_small_of_lieModel_two hLM with ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
    · have hpd : (3 : ℕ) ≠ d.1.characteristic := by rw [hd2]; norm_num
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent _ hsimple hna d
        ⟨e⟩ 3 hp3 (by norm_num) hpd _ hβ3 hβ1
    ·
      exfalso
      have hfix : fixSubgroup (centerQuotAut K α) ≠ ⊤ := by
        intro h
        apply hβ1
        ext s
        have hs : s ∈ fixSubgroup (centerQuotAut K α) := by
          rw [h]
          exact Subgroup.mem_top s
        exact mem_fixSubgroup.1 hs
      have hlt : Nat.card ↥(J.map π) < 60 := by
        rw [← h60]
        calc Nat.card ↥(J.map π)
            ≤ Nat.card ↥(fixSubgroup (centerQuotAut K α)) := Subgroup.card_le_of_le hJb.1
          _ < Nat.card ↥(⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
            Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hfix)
          _ = Nat.card (K ⧸ Subgroup.center K) := Subgroup.card_top
      haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
      have hQs := isQuasisimple_pQuot_of_glaPComponent hp3 hJb
      haveI := hQs.2
      haveI : Nontrivial (PQuot 3 (J.map π)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 (J.map π)))).nontrivial
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (PQuot 3 (J.map π))).ne hQs.1
    ·
      exfalso
      have h1' : (canonLabel labK).n = 1 := (CanonSubcomp.canonLabel_n_eq_markDeg hlam hc).trans h1
      have hdvd := CanonSubcomp.n_dvd_canonLabel_n hlam
      rw [h1'] at hdvd
      exact hn1 (Nat.dvd_one.1 hdvd)
  have hJle := hpil _ hJb.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJb)
  have hJc := (glaPComponent_isComponent_of_le_layer hJb hJle).1
  obtain ⟨eA⟩ := chev2_quot_equiv hp3 hJb hJc.2.2
  have hcatb : catalogIs (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) K144.I144Cat :=
    (catalogIs_congr (eA.trans eJ.symm)).2 hcat
  obtain ⟨labJ, hcJ, hJL⟩ := i144Cat_hasLabel hJc.2.2 hcatb
  have hdvd := Y10GField.inn_of_families
    (Y10GInnLin.innDiagLin_of_labelDict Y10GInnLin.linLabelDict_holds) Y10GInnUni.innDiagUni_holds
    Y10GField.innDiagSymp_holds Y10GField.innDiagOrth_holds Y10GField.innDiagExc_holds
    _ 3 (centerQuotAut K α) (J.map π) labK labJ hp3 (by norm_num) hcen hin hβ3 hJL hJb
  rw [hcJ] at hdvd
  have hK1 := CanonSubcomp.n_dvd_canonLabel_n hlam
  rw [Nat.dvd_one.1 hdvd] at hK1
  exact hn1 (Nat.dvd_one.1 hK1)

end Holds

end CFSG.LocalAnalysis.GLTheoremA.K144I

end
