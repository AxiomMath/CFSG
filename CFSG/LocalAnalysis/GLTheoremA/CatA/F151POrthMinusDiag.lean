module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmMinus
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167COrthMinus
import CFSG.HardMathSupport.Dickson.BMRows.CensusShape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA (isOmM isOmMA)

private theorem primePower_p_eq_two {q : TauCeti.PrimePower} {f : ℕ} (hf : 1 ≤ f)
    (h : q.card = 2 ^ f) : q.p = 2 := by
  have hdvd : q.p ∣ 2 ^ f := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  have hp2 : q.p ∣ 2 := q.prime_p.dvd_of_dvd_pow hdvd
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hp2

private theorem onLie_charTwo_of_isOmM {i : TauCeti.CFSGIndex} {n f : ℕ} (hf : 1 ≤ f)
    (h : isOmM n (2 ^ f) i) :
    onLie (fun d => d.characteristic = 2) i := by
  rcases i with _ | _ | ⟨d, hv⟩ | _
  · simp [isOmM, onLie] at h
  · simp [isOmM, onLie] at h
  · cases d <;>
      simp only [isOmM, onLie, TauCeti.LieTypeIndex.characteristic_twistedD] at h ⊢
    all_goals try contradiction
    exact primePower_p_eq_two hf (by simpa [TauCeti.PrimePower.card_def] using h.2)
  · simp [isOmM, onLie] at h

private theorem catalogIs_charTwo_of_catalogIs_isOmMA {S : Type} [Group S] {n f : ℕ}
    (hn : 4 ≤ n) (hf : 1 ≤ f) (h : catalogIs S (isOmMA n (2 ^ f))) :
    catalogIs S (onLie fun d => d.characteristic = 2) := by
  obtain ⟨i, hi, hE⟩ := h
  refine ⟨i, ?_, hE⟩
  unfold isOmMA at hi
  rcases hi with hi | ⟨hn3, _⟩
  · exact onLie_charTwo_of_isOmM hf hi
  · omega

theorem orthMinusDiag_of_block (hL : CatLayer) (hC : CatChevComps) (hB : DiagOfBlock)
    (hT : MarkTransport) (hI : ShapeModelDiagIso)
    (hM : T171Sh.OrthComponentBlockAnalysisMinus) : OrthMinusDiag := by
  intro n m K _ _ hn4 hK b c hbc p hp hp2
  have hm1 : 1 ≤ m := by
    have hcard2 : 1 < Nat.card K := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0
      simp at hK
      omega
    · exact hm
  have hadm : StatedLieAdmissible .POmegaMinus n 2 m := ⟨Nat.prime_two, hm1, hn4⟩
  have hSC : StatedClassicalModel (CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenOmega (CFSG.Assembly.LargeEvenQMinus (n - 1) b c)))
      .POmegaMinus n 2 m :=
    CFSG.StandardType.statedClassicalModel_omegaMinus n m hK b c hbc hadm
  have hcatMA := CFSG.LocalAnalysis.GLTheoremA.I167.i167COrth_catalogIs_minus hSC
  let e := T171Sh.orthModelEquivMinus n K b c
  have hcat : catalogIs (CFSG.RankThree.Classical2.ProjOrthDerived
      (CFSG.LieType.Universal.Spin.quadMinus n K b c))
      (onLie fun d => d.characteristic = 2) :=
    CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ e
      (catalogIs_charTwo_of_catalogIs_isOmMA hn4 hm1 hcatMA)
  have hPL := hL (CFSG.RankThree.Classical2.ProjOrthDerived
    (CFSG.LieType.Universal.Spin.quadMinus n K b c)) p hp hp2 hcat
  have hCC := hC (CFSG.RankThree.Classical2.ProjOrthDerived
    (CFSG.LieType.Universal.Spin.quadMinus n K b c)) p hp hp2 hcat
  have hBA : BlockAnalysisAt (CFSG.RankThree.Classical2.ProjOrthDerived
      (CFSG.LieType.Universal.Spin.quadMinus n K b c)) p := by
    intro x y hxp hyp hxy hx1 J hJ hN
    exact hM (m := n) (n := m) (p := p) (K := K) b c hK hn4 hbc hp hp2
      x y hxp hyp hxy hx1 J hJ hN
  have hSMD := hB (CFSG.RankThree.Classical2.ProjOrthDerived
    (CFSG.LieType.Universal.Spin.quadMinus n K b c)) p hp hp2 hPL hCC hBA
  exact hI hT _ _ e.symm p hSMD

end CFSG.LocalAnalysis.GLTheoremA.F151

end
