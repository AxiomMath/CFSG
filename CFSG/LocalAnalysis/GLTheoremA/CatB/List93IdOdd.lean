module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1315
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem not_cube_dvd_336 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 3 ∣ 336) : False := by
  have hle : p ≤ 6 := by
    have h336 : p ^ 3 ≤ 336 := Nat.le_of_dvd (by norm_num) h
    by_contra hc
    have h7 : 7 ≤ p := by omega
    have h343 : 343 ≤ p ^ 3 := calc (343 : ℕ) = 7 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left h7 3
    omega
  interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hp2; done) | (norm_num at h; done)

section Certs


theorem chevOdd_holds : ∀ (S : Type) [Group S] [Finite S] (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 →
    IsChevSimple q S → IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian p E → Nat.card E < p ^ 3 := by
  intro S _ _ q hq hq2 hq3 hchq hch2 p hp hp2 E hE
  by_contra hlt
  push Not at hlt
  have hdvd : p ^ 3 ∣ Nat.card (MulAut S) := cube_dvd_mulAut hp hE hlt
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1315.inputChevTwoOdd_holds S q hq hq2 hq3
      hchq hch2 with ⟨⟨e⟩, -⟩ | ⟨hL, -⟩
  · exact no_alt5 hp hp2 e hE hlt
  · obtain ⟨F, fld, fin, hF, ⟨f⟩⟩ := hL
    have hS : CFSG.Open.StatedClassicalModel S .PSL 2 7 1 := by
      unfold CFSG.Open.StatedClassicalModel
      refine ⟨⟨by norm_num, le_rfl, le_rfl, by norm_num, by norm_num⟩, F, fld, fin, ?_, ⟨f⟩⟩
      rw [pow_one]
      exact hF
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨e7⟩ := small_psl_iso (p := 7) (f := 1) le_rfl hS
    have hAut := small_card_aut_psl (p := 7) (f := 1) le_rfl e7
    rw [hAut] at hdvd
    exact not_cube_dvd_336 hp hp2 (by norm_num at hdvd; exact hdvd)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93

end
