module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthSymp
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrth
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a

theorem nonD4LieContraS_symplecticOrthogonal : NonD4LieContraS .symplecticOrthogonal := by
  intro S _ _ hs hna p hp hp3 idx hF hch ⟨e⟩ hD4 Q x J q c
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | B r q' =>
    have hq' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hch
    by_cases hsp : q'.p = 2 ∨ r = 2
    · have hmod : StatedClassicalModel S .PSp r (lieIndexChar (.B r q')) q'.exponent := by
        rcases (show r = 2 ∨ 3 ≤ r by simp only at hr; omega) with rfl | hr3
        · exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q' hv e
        · have hq2 : q'.p = 2 := hsp.resolve_right (by omega)
          exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q' hv hq2 hr3 e
      exact sympl_contra hs hna hmod (by simpa [lieIndexChar, hq'] using hp3) c
    · push Not at hsp
      have hr3 : 3 ≤ r := by simp only at hr; omega
      have hmod : StatedClassicalModel S .POmegaOdd r (lieIndexChar (.B r q')) q'.exponent :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q' hv hsp.1 hr3 e
      exact orth_contra (Or.inl rfl) hs hna hmod (by simpa [lieIndexChar, hq'] using hp3)
        (by intro h; exact absurd h (by decide)) c
  | C r q' =>
    have hq' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hch
    exact sympl_contra hs hna (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q' hv e)
      (by simpa [lieIndexChar, hq'] using hp3) c
  | D r q' =>
    have hq' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hch
    have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q' hv e
    refine orth_contra (Or.inr (Or.inl rfl)) hs hna hmod (by simpa [lieIndexChar, hq'] using hp3)
      (fun _ hr4 => ?_) c
    apply hD4
    obtain ⟨-, K, hK, hKf, -, ⟨e'⟩⟩ := hmod
    subst hr4
    exact ⟨K, hK, hKf, ⟨e'⟩⟩
  | twistedD r q' =>
    have hq' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hch
    exact orth_contra (Or.inr (Or.inr rfl)) hs hna
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q' hv e)
      (by simpa [lieIndexChar, hq'] using hp3) (by intro h; exact absurd h (by decide)) c
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
