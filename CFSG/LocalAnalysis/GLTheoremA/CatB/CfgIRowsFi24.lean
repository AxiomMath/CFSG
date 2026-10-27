module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgITriangular
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMFi24Inv
public import Certificates.Certificate10142

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.CfgI

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three CFSG.Sporadic.Fi24.Native
  Timmesfeld.Fi24Cl CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv
  CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg

namespace Fi24Cfg

section Certs


theorem lt_of_all {w : List ℕ} (h : w.all (· < 26) = true) : ∀ l ∈ w, l < 26 := fun l hl =>
  of_decide_eq_true (List.all_eq_true.1 h l hl)

theorem nil_lt : ∀ l ∈ ([] : List ℕ), l < 26 := fun l hl => absurd hl List.not_mem_nil

theorem conj_of_eqOnBase {n x y : List ℕ} (hn : ∀ l ∈ n, l < 26) (hx : ∀ l ∈ x, l < 26)
    (hy : ∀ l ∈ y, l < 26)
    (h : eqOnBase CFSG.Sporadic.Fi24.letters (n ++ x ++ invWord n) y = true) :
    wordElt n * wordElt x * (wordElt n)⁻¹ = wordElt y := by
  have e := rkBMFi24_eq_of_eqOnBase
    (rkBMFi24_append_lt (rkBMFi24_append_lt hn hx) (rkBMFi24_invWord_lt hn)) hy h
  rw [rkBMFi24_wordElt_append, rkBMFi24_wordElt_append, Fi24Sylow.wordElt_invWord] at e
  exact e

noncomputable def xs (i : Fin 6) : CFSG.Sporadic.Fi24.J := wordElt (xWords[i.val]!)

noncomputable def ns (i : Fin 6) : CFSG.Sporadic.Fi24.J := wordElt (nWords[i.val]!)

theorem facts (i : Fin 6) :
    xs i ^ 3 = 1 ∧ xs i ≠ 1 ∧ ns i * xs i * (ns i)⁻¹ = (xs i)⁻¹ ∧
      ∀ j : Fin 6, xs i * xs j = xs j * xs i ∧ (j < i → ns i * xs j * (ns i)⁻¹ = xs j) := by
  have h : cfgCheck CFSG.Sporadic.Fi24.orb = true := Certificates.certificate10142
  unfold cfgCheck at h
  have hall := List.all_eq_true.1 h
  have hxlt : ∀ k : Fin 6, ∀ l ∈ xWords[k.val]!, l < 26 := by
    intro k
    have hk := hall k.val (List.mem_range.2 k.2)
    unfold cfgAt at hk
    simp only [Bool.and_eq_true] at hk
    exact lt_of_all hk.1.1.1.1.1
  have hi := hall i.val (List.mem_range.2 i.2)
  unfold cfgAt at hi
  simp only [Bool.and_eq_true] at hi
  obtain ⟨⟨⟨⟨⟨hx, hn⟩, h3⟩, h1⟩, hinv⟩, hj⟩ := hi
  have hx' := lt_of_all hx
  have hn' := lt_of_all hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt (rkBMFi24_append_lt hx' hx') hx')
      nil_lt h3
    rw [rkBMFi24_wordElt_append, rkBMFi24_wordElt_append, rkBMFi24_wordElt_nil] at e
    rw [xs, pow_three, ← mul_assoc]
    exact e
  · intro he
    have e := rkBMFi24_eqOnBase_of_eq hx' nil_lt (by rw [rkBMFi24_wordElt_nil]; exact he)
    rw [e] at h1
    exact Bool.noConfusion h1
  · have e := conj_of_eqOnBase hn' hx' (rkBMFi24_invWord_lt hx') hinv
    rw [Fi24Sylow.wordElt_invWord] at e
    exact e
  · intro j
    have hjj := List.all_eq_true.1 hj j.val (List.mem_range.2 j.2)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      not_lt] at hjj
    obtain ⟨hc, hf⟩ := hjj
    refine ⟨?_, fun hlt => ?_⟩
    · have e := rkBMFi24_eq_of_eqOnBase (rkBMFi24_append_lt hx' (hxlt j))
        (rkBMFi24_append_lt (hxlt j) hx') hc
      rw [rkBMFi24_wordElt_append, rkBMFi24_wordElt_append] at e
      exact e
    · rcases hf with hle | he
      · exact absurd hlt (not_lt.2 (Fin.le_def.2 hle))
      · exact conj_of_eqOnBase hn' (hxlt j) (hxlt j) he

end Certs

end Fi24Cfg

section Certs


theorem cfgIRank_m3_three : CfgIRankRow 3 S8.Row.m3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  refine Triangular.cfgIRankRow_of_triangular' (M := CFSG.Sporadic.Fi24.J) ?_ rfl Fi24Cfg.xs
    Fi24Cfg.ns (fun i => (Fi24Cfg.facts i).1) (fun i => (Fi24Cfg.facts i).2.1)
    (fun i j => ((Fi24Cfg.facts i).2.2.2 j).1) (fun j => (Fi24Cfg.facts j).2.2.1)
    (fun i j hij => ((Fi24Cfg.facts j).2.2.2 i).2 hij)
  intro i hi
  have hi' : i = TauCeti.CFSGIndex.sporadic .Fi24Prime := hi
  subst hi'
  exact ⟨b.symm.trans CFSG.Sporadic.Fi24.fi24EquivJ⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S8.CfgI
