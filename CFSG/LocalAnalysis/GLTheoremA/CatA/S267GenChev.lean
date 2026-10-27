module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.LocalAnalysis.GLTheoremA.PCompNoncomm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieIndexChar
  glaPComponent_isComponent_of_le_layer)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_centralQuotient_mulEquiv
  isChevSimple_congr)


private theorem eq_three_or_five_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  omega

theorem genCompChevOn_holds : GenCompChevOn fun _ => True := by
  intro p T _ _ d hT _ x hxp hx1 J hJ
  obtain ⟨hp, hp2, ⟨e⟩, -, hpq⟩ := hT
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).2
  have hs : IsSimpleGroup T := e.isSimpleGroup
  have hna : ∃ a b : T, a * b ≠ b * a := exists_mul_ne_mul_of_glaPComponent hp hJ
  have hlc : lieIndexChar d.1 = d.1.characteristic :=
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieIndexChar_eq_characteristic d.1
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent T hs hna
    d ⟨e⟩ p hp hp2 hpq x hxp hx1
  have hJcomp : IsComponentOf J (fixSubgroup x) :=
    (glaPComponent_isComponent_of_le_layer hJ (hlayer J hJ.1 (glaPComponent_perfect hJ))).1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  rw [← hlc]
  rcases eq_three_or_five_le_of_prime hp hp2 with rfl | hp5
  ·
    have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
    have hne : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
      intro htop
      haveI : Nontrivial (PQuot 3 J) := isQuasisimple_nontrivial hQ
      haveI : Subsingleton (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton (PQuot 3 J) ‹_›
    have hO : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J :=
      le_center_of_normal_of_isQuasisimple hJq inferInstance hne
    have hd := (lieComp_holds T hs hna d ⟨e⟩ x hxp J hJ).1
    obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hJq.1
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact hO)
    exact isChevSimple_congr e'.symm hd.chev
  ·
    have hexp := lieCompsOn_holds hp hp5 (CFSG.Yardstones.Md42047359a2a.lieFamily d.1) T hs hna
      d rfl ⟨e⟩ x hxp hx1 (Or.inl (by rw [hlc]; exact Ne.symm hpq))
    obtain ⟨X, _, _, hX, f, hf, hk⟩ := hexp.comps J hJcomp
    obtain ⟨e'⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f hf hk
    exact isChevSimple_congr e' hX.chev

theorem genCompChevOn_holds' (Q : TauCeti.LieTypeIndex → Prop) : GenCompChevOn Q :=
  fun p T _ _ d hT _ => genCompChevOn_holds p T d hT trivial

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
