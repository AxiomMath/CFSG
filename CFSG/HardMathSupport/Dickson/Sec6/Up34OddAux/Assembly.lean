module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Narrow
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Families
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.ComponentClassification.OuterAutomorphisms

theorem fam_cover_ge_five {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (ht : t ≠ .Tits) (hp5 : 5 ≤ p) :
    FamPslTwo t n p f ∨ FamPslGood t n p f ∨ FamPslBad t n p f ∨ FamPsp t n p f ∨
      FamPsuGood t n p f ∨ FamPsuBad t n p f ∨ FamOrthOdd t n p f ∨ FamOrthPlus t n p f ∨
      FamOrthMinus t n p f ∨ FamD4 t n p f ∨ FamTriD4 t n p f ∨ FamG2 t n p f ∨ FamF4 t n p f ∨
      FamE6 t n p f ∨ FamTwE6 t n p f ∨ FamE7 t n p f ∨ FamE8 t n p f := by
  have hf : 1 ≤ f := hadm.2.1
  rcases fam_cover hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h
  all_goals first | tauto | skip
  ·
    exfalso
    obtain ⟨-, -, h8⟩ := h
    have hdvd : p ∣ 8 := h8 ▸ dvd_pow_self p (by omega : f ≠ 0)
    have hle : p ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hpr := hadm.1
    interval_cases p <;> first | exact absurd hdvd (by decide) | exact absurd hpr (by norm_num)
  ·
    exfalso
    have h2 : p = 2 := by
      have := hadm.2.2
      subst h
      exact this.2.1
    omega
  ·
    exfalso
    have h2 : p = 3 := by
      have := hadm.2.2
      subst h
      exact this.2.1
    omega
  ·
    exfalso
    have h2 : p = 2 := by
      have := hadm.2.2
      subst h
      exact this.2.1
    omega

theorem noL34OuterAt_true (hPslTwo : NoL34OuterAt FamPslTwo) (hPslGood : NoL34OuterAt FamPslGood)
    (hPslBad : NoL34OuterAt FamPslBad) (hPsp : NoL34OuterAt FamPsp)
    (hPsuGood : NoL34OuterAt FamPsuGood) (hPsuBad : NoL34OuterAt FamPsuBad)
    (hOrthOdd : NoL34OuterAt FamOrthOdd) (hOrthPlus : NoL34OuterAt FamOrthPlus)
    (hOrthMinus : NoL34OuterAt FamOrthMinus) (hD4 : NoL34OuterAt FamD4)
    (hTriD4 : NoL34OuterAt FamTriD4) (hG2 : NoL34OuterAt FamG2) (hF4 : NoL34OuterAt FamF4)
    (hE6 : NoL34OuterAt FamE6) (hTwE6 : NoL34OuterAt FamTwE6) (hE7 : NoL34OuterAt FamE7)
    (hE8 : NoL34OuterAt FamE8) : NoL34OuterAt (fun _ _ _ _ => True) := by
  intro P _ _ t n p f hadm ht _ hp5 hm ψ hψ3 hψ
  rcases fam_cover_ge_five hadm ht hp5 with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h
  · exact hPslTwo P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPslGood P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPslBad P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsp P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsuGood P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsuBad P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthOdd P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthPlus P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthMinus P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hD4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hTriD4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hG2 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hF4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE6 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hTwE6 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE7 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE8 P t n p f hadm ht h hp5 hm ψ hψ3 hψ

theorem noL34InnAt_true (hPslTwo : NoL34InnAt FamPslTwo) (hPslGood : NoL34InnAt FamPslGood)
    (hPslBad : NoL34InnAt FamPslBad) (hPsp : NoL34InnAt FamPsp)
    (hPsuGood : NoL34InnAt FamPsuGood) (hPsuBad : NoL34InnAt FamPsuBad)
    (hOrthOdd : NoL34InnAt FamOrthOdd) (hOrthPlus : NoL34InnAt FamOrthPlus)
    (hOrthMinus : NoL34InnAt FamOrthMinus) (hD4 : NoL34InnAt FamD4)
    (hTriD4 : NoL34InnAt FamTriD4) (hG2 : NoL34InnAt FamG2) (hF4 : NoL34InnAt FamF4)
    (hE6 : NoL34InnAt FamE6) (hTwE6 : NoL34InnAt FamTwE6) (hE7 : NoL34InnAt FamE7)
    (hE8 : NoL34InnAt FamE8) : NoL34InnAt (fun _ _ _ _ => True) := by
  intro P _ _ t n p f hadm ht _ hp5 hm ψ hψ3 hψ
  rcases fam_cover_ge_five hadm ht hp5 with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h
  · exact hPslTwo P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPslGood P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPslBad P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsp P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsuGood P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hPsuBad P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthOdd P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthPlus P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hOrthMinus P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hD4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hTriD4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hG2 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hF4 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE6 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hTwE6 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE7 P t n p f hadm ht h hp5 hm ψ hψ3 hψ
  · exact hE8 P t n p f hadm ht h hp5 hm ψ hψ3 hψ

section Bridge

theorem noL34Out_of_outerAt (h : NoL34OuterAt (fun _ _ _ _ => True)) {r : ℕ} (hr5 : 5 ≤ r) :
    NoL34Out r := by
  intro d hd _ α hα hinn
  have hne : d.1.characteristic ≠ 2 := by omega
  obtain ⟨t, n, f, hm⟩ := exists_blueprint_lieModel_of_odd d hne (MulEquiv.refl _)
  have hadm := hm.admissible
  rw [hd] at hm hadm
  have ht : t ≠ .Tits := by
    rintro rfl
    have := hadm.2.2.2.1
    omega
  exact h _ t n r f hadm ht trivial hr5 hm α (by rw [← hα]; exact pow_orderOf_eq_one α) hinn

theorem noL34Inn_of_innAt (h : NoL34InnAt (fun _ _ _ _ => True)) {r : ℕ} (hr5 : 5 ≤ r) :
    NoL34Inn r := by
  intro d hd _ u hu
  have hne : d.1.characteristic ≠ 2 := by omega
  obtain ⟨t, n, f, hm⟩ := exists_blueprint_lieModel_of_odd d hne (MulEquiv.refl _)
  have hadm := hm.admissible
  rw [hd] at hm hadm
  have ht : t ≠ .Tits := by
    rintro rfl
    have := hadm.2.2.2.1
    omega
  refine h _ t n r f hadm ht trivial hr5 hm (MulAut.conj u) ?_ ⟨u, rfl⟩
  rw [← map_pow, ← hu, pow_orderOf_eq_one]
  exact map_one _

end Bridge

theorem not_famPslBad_three {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f) : ¬ FamPslBad t n 3 f := by
  rintro ⟨-, -, hnc⟩
  apply hnc
  have h3 : ¬ 3 ∣ 3 ^ f - 1 := by
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right n (3 ^ f - 1))
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)

theorem not_famPsuBad_three {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f) : ¬ FamPsuBad t n 3 f := by
  rintro ⟨-, -, hdvd⟩
  have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  have := (hdvd.trans (Nat.gcd_dvd_right n (3 ^ f + 1)))
  omega

theorem fam_cover_three {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f)
    (ht : t ≠ .Tits) :
    FamPslTwo t n 3 f ∨ FamPslGood t n 3 f ∨ FamPsp t n 3 f ∨ FamPsuGood t n 3 f ∨
      FamOrthOdd t n 3 f ∨ FamOrthPlus t n 3 f ∨ FamOrthMinus t n 3 f ∨ FamD4 t n 3 f ∨
      FamTriD4 t n 3 f ∨ FamG2 t n 3 f ∨ FamF4 t n 3 f ∨ FamE6 t n 3 f ∨ FamTwE6 t n 3 f ∨
      FamE7 t n 3 f ∨ FamE8 t n 3 f ∨ FamReeG2 t n 3 f := by
  have hf : 1 ≤ f := hadm.2.1
  rcases fam_cover hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h
  all_goals first | tauto | skip
  · exact absurd h (not_famPslBad_three hf)
  ·
    exfalso
    obtain ⟨-, -, h8⟩ := h
    have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  · exact absurd h (not_famPsuBad_three hf)
  ·
    exfalso
    have h2 : 3 = 2 := by
      have := hadm.2.2
      subst h
      exact this.2.1
    omega
  ·
    exfalso
    have h2 : 3 = 2 := by
      have := hadm.2.2
      subst h
      exact this.2.1
    omega

theorem noL34OuterAtThree_true (hPslTwo : NoL34OuterAtThree FamPslTwo)
    (hPslGood : NoL34OuterAtThree FamPslGood) (hPsp : NoL34OuterAtThree FamPsp)
    (hPsuGood : NoL34OuterAtThree FamPsuGood) (hOrthOdd : NoL34OuterAtThree FamOrthOdd)
    (hOrthPlus : NoL34OuterAtThree FamOrthPlus) (hOrthMinus : NoL34OuterAtThree FamOrthMinus)
    (hD4 : NoL34OuterAtThree FamD4) (hTriD4 : NoL34OuterAtThree FamTriD4)
    (hG2 : NoL34OuterAtThree FamG2) (hF4 : NoL34OuterAtThree FamF4)
    (hE6 : NoL34OuterAtThree FamE6) (hTwE6 : NoL34OuterAtThree FamTwE6)
    (hE7 : NoL34OuterAtThree FamE7) (hE8 : NoL34OuterAtThree FamE8)
    (hReeG2 : NoL34OuterAtThree FamReeG2) : NoL34OuterAtThree (fun _ _ _ _ => True) := by
  intro P _ _ t n f hadm ht _ hm ψ hψ3 hψ
  rcases fam_cover_three hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hPslTwo P t n f hadm ht h hm ψ hψ3 hψ
  · exact hPslGood P t n f hadm ht h hm ψ hψ3 hψ
  · exact hPsp P t n f hadm ht h hm ψ hψ3 hψ
  · exact hPsuGood P t n f hadm ht h hm ψ hψ3 hψ
  · exact hOrthOdd P t n f hadm ht h hm ψ hψ3 hψ
  · exact hOrthPlus P t n f hadm ht h hm ψ hψ3 hψ
  · exact hOrthMinus P t n f hadm ht h hm ψ hψ3 hψ
  · exact hD4 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hTriD4 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hG2 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hF4 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hE6 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hTwE6 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hE7 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hE8 P t n f hadm ht h hm ψ hψ3 hψ
  · exact hReeG2 P t n f hadm ht h hm ψ hψ3 hψ

section BridgeThree

theorem noL34Out_three_of_outerAtThree (h : NoL34OuterAtThree (fun _ _ _ _ => True)) :
    NoL34Out 3 := by
  intro d hd _ α hα hinn
  have hne : d.1.characteristic ≠ 2 := by omega
  obtain ⟨t, n, f, hm⟩ := exists_blueprint_lieModel_of_odd d hne (MulEquiv.refl _)
  have hadm := hm.admissible
  rw [hd] at hm hadm
  have ht : t ≠ .Tits := by
    rintro rfl
    have := hadm.2.2.2.1
    omega
  exact h _ t n f hadm ht trivial hm α (by rw [← hα]; exact pow_orderOf_eq_one α) hinn

end BridgeThree

end CFSG.HardMathSupport.Dickson.Sec6
