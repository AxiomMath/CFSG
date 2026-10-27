module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsOrthBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

theorem k1419ClsOrthFact_of_labels (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hJL : K1419ClsL3U3LabelFact) : K1419ClsOrthFact := by
  intro S _ _ α J labK hFam hcen hα3 hα1 hin hJc hcat hZ
  obtain ⟨t, m, n, a, ht, hm, hn, hmodel, ha3, ha1, hconj⟩ :=
    k1419ClsOrthData hcen hFam hα3 hα1 hin
  subst hconj
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJc
  obtain ⟨nJ, hlab⟩ := hJL (PQuot 3 J) hQ hcat
  have hcentre : a ∈ J → False := by
    intro haJ
    have hjc : ∀ j ∈ J, a * j = j * a := by
      intro j hj
      have hfix := hJc.1 hj
      rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
        mul_inv_eq_iff_eq_mul] at hfix
      exact hfix
    exact ha1 (k1419ClsCentre_eq_one hZ haJ hjc ha3)
  rcases k1419ClsOrthBlock ht hmodel a ha3 ha1 hJc with
    ⟨b, k, E, hEf, hEfin, hb2, hEk, ⟨e⟩, hx⟩ |
    ⟨b, k, E, hEf, hEfin, τ, hτ, hb2, hτk, hEc, ⟨e⟩, hx⟩ |
    ⟨s, K', hK'f, hK'fin, hs2, hK'card, hne, ⟨e⟩⟩ | ⟨s, hM⟩
  ·
    rcases hlab with ⟨hl, hn6⟩ | ⟨hl, hn6⟩
    · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.A, 2, nJ⟩ b k
        E hb2 hEk hl ⟨e⟩
      have hdict' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.A, b - 1, k⟩ := hdict
      injection hdict' with _ h1 _
      exact hcentre (hx (by omega))
    · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.twA, 2, nJ⟩ b k
        E hb2 hEk hl ⟨e⟩
      have hdict' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.A, b - 1, k⟩ := hdict
      injection hdict' with h1
      cases h1
  ·
    obtain ⟨hb3, -, -⟩ := k1419ClsUniLabel hRig hlab τ hτ hb2 hτk hEc ⟨e⟩
    exact hcentre (hx (by omega))
  ·
    rcases hlab with ⟨hl, hn6⟩ | ⟨hl, hn6⟩
    · have h := Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs2 hK'card hne hl e
      have h' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.B, s, n⟩ := h
      injection h' with h1
      cases h1
    · have h := Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs2 hK'card hne hl e
      have h' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.B, s, n⟩ := h
      injection h' with h1
      cases h1
  ·
    rcases hlab with ⟨hl, hn6⟩ | ⟨hl, hn6⟩
    · have hd := Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.A, 2, nJ⟩ s n hl
      rcases hM with hM | hM
      · have h' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.D, s, n⟩ := hd.1 hM
        injection h' with h1
        cases h1
      · have h' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.twD, s, n⟩ := hd.2 hM
        injection h' with h1
        cases h1
    · have hd := Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.twA, 2, nJ⟩ s n hl
      rcases hM with hM | hM
      · have h' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.D, s, n⟩ := hd.1 hM
        injection h' with h1
        cases h1
      · have h' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.twD, s, n⟩ := hd.2 hM
        injection h' with h1
        cases h1

end CFSG.LocalAnalysis.GLTheoremA.K1419
