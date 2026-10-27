module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkTits
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FSmallRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i141f_not_cube_dvd_35942400 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : p ^ 3 ∣ 35942400) : False := by
  have : p ≤ 330 := by
    by_contra hc
    have := Nat.pow_le_pow_left (show 331 ≤ p by omega) 3
    have := Nat.le_of_dvd (by norm_num) h
    norm_num at *
    omega
  interval_cases p <;>
    first
      | (norm_num at hp; done)
      | (norm_num at hp2; done)
      | (norm_num at hp3; done)
      | (norm_num at h; done)

section Certs


theorem i141f_autRank_tits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (h : catalogIs S rsTits) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (h3 : p ^ 3 ≤ Nat.card E) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases eq_or_ne p 3 with rfl | hp3
  · exact absurd h3 (not_le.2 ((List93.tits_holds S ⟨i, hi, ⟨e⟩⟩).1 E hE))
  · cases i with
    | lie d =>
      obtain ⟨d1, hv⟩ := d
      have hd : d1 = TauCeti.LieTypeIndex.tits := hi
      subst hd
      have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 2 :=
        CFSG.LocalAnalysis.RankThreeTheoremC.card_outer_of_tits ⟨hv, ⟨e⟩⟩
      have hR : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.reeTitsModel_tits_of_equiv e
      obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 hR
      have hS : Nat.card S = 17971200 :=
        (Nat.card_congr eT.toEquiv).trans CFSG.Sporadic.Schreier.Tits.card_titsD
      have hin : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) ∣ 17971200 := by
        rw [← hS]
        exact Subgroup.card_range_dvd (MulAut.conj : S →* MulAut S)
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
      have hdvd : Nat.card (MulAut S) ∣ 35942400 := by
        rw [hmul, hO]
        exact (Nat.mul_dvd_mul_left 2 hin).trans (by norm_num)
      exact i141f_not_cube_dvd_35942400 hp hp2 hp3 ((cube_dvd_mulAut hp hE h3).trans hdvd)
    | cyclic p h => exact False.elim hi
    | alternating n h => exact False.elim hi
    | sporadic s => exact False.elim hi

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
