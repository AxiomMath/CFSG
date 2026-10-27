module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieArith
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecOrd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieChar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowLie

open CFSG Subgroup Assembly.LowTwoRank CatLeaf CatLeafProof

theorem lieOrderNumerator_psl_four (q : ℕ) :
    lieOrderNumerator .PSL 4 q = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  rw [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide]
  simp [Finset.prod_insert]

theorem lieOrderNumerator_psu_four (q : ℕ) :
    lieOrderNumerator .PSU 4 q = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
  rw [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide]
  simp [Finset.prod_insert, Nat.even_iff]

theorem lieOrderNumerator_psp_two (q : ℕ) :
    lieOrderNumerator .PSp 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  rw [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide]
  simp [Finset.prod_insert]

theorem lieOrderNumerator_omega_three (q : ℕ) :
    lieOrderNumerator .POmegaOdd 3 q = q ^ 9 * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) := by
  rw [lieOrderNumerator, show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp [Finset.prod_insert]

theorem char_data {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : r.Prime)
    (hrp : r ≠ p) : 3 ≤ p ^ f ∧ Odd (p ^ f) ∧ ¬ r ∣ p ^ f := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  refine ⟨hp3.trans (Nat.le_self_pow (by omega) p), (hp.odd_of_ne_two hp2).pow, fun h => ?_⟩
  exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))

section Certified


theorem card_lt_ordProj_pow_three {X : Type} [Group X] {t : StatedLieTag} {n r f : ℕ}
    (hr2 : r ≠ 2) (hadm : StatedLieAdmissible t n r f) (hX : Blueprint.LieModel X t n r f) :
    Nat.card X < (ordProj[r] (Nat.card X)) ^ 3 := by
  obtain ⟨-, hord, hfac⟩ := lieOrderFormulasInput X t n r f hadm hX
  have hdiv : 0 < lieOrderDivisor t n (r ^ f) := Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm)
  have hle : Nat.card X ≤ lieOrderNumerator t n (r ^ f) := by
    rw [← hord]
    exact Nat.le_mul_of_pos_right _ hdiv
  have hlt := N36.OddChar.numerator_lt hadm hr2
  rw [hfac]
  calc Nat.card X ≤ lieOrderNumerator t n (r ^ f) := hle
    _ < (r ^ f) ^ (3 * lieSylowExponent t n) := hlt
    _ = (r ^ (lieSylowExponent t n * f)) ^ 3 := by
        rw [← pow_mul, ← pow_mul]
        ring_nf

theorem false_of_ordProj_le {X : Type} [Group X] {t : StatedLieTag} {n r f : ℕ} (hr2 : r ≠ 2)
    (hadm : StatedLieAdmissible t n r f) (hX : Blueprint.LieModel X t n r f) {m d B : ℕ}
    (hcard : Nat.card X * d = m) (hd : 0 < d) (hB : ordProj[r] m ≤ B) (hm : d * B ^ 3 ≤ m) :
    False := by
  have hlt := card_lt_ordProj_pow_three hr2 hadm hX
  have hr : r.Prime := hadm.1
  have : Finite X := (lieOrderFormulasInput X t n r f hadm hX).1
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by
    rw [← hcard]
    exact mul_ne_zero hX0 hd.ne'
  have hvle : ordProj[r] (Nat.card X) ≤ ordProj[r] m :=
    Nat.pow_le_pow_right hr.pos ((Nat.factorization_le_iff_dvd hX0 hm0).mpr ⟨d, hcard.symm⟩ r)
  have h3 : Nat.card X < B ^ 3 := hlt.trans_le (Nat.pow_le_pow_left (hvle.trans hB) 3)
  have h4 : m < d * B ^ 3 := by
    rw [← hcard, mul_comm d]
    exact Nat.mul_lt_mul_of_pos_right h3 hd
  omega

theorem false_of_lieModel_l4 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hXp : Blueprint.LieModel X .PSL 4 p f) {t : StatedLieTag} {n r f' : ℕ}
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hadm : StatedLieAdmissible t n r f')
    (hXr : Blueprint.LieModel X t n r f') : False := by
  obtain ⟨hq3, hqo, hrq⟩ := char_data hp hp2 hf hadm.1 hrp
  obtain ⟨-, hord, -⟩ := lieOrderFormulasInput X .PSL 4 p f (N36.admissible_of_lieModel' hXp) hXp
  rw [lieOrderNumerator_psl_four] at hord
  have hd : lieOrderDivisor .PSL 4 (p ^ f) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < lieOrderDivisor .PSL 4 (p ^ f) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact false_of_ordProj_le hr2 hadm hXr hord hd0 (ordProj_l4_le hq3 hqo hadm.1 hr2 hrq)
    ((Nat.mul_le_mul_right _ hd).trans (four_mul_pow_nine_le_l4 hq3))

theorem false_of_lieModel_u4 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hXp : Blueprint.LieModel X .PSU 4 p f) {t : StatedLieTag} {n r f' : ℕ}
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hadm : StatedLieAdmissible t n r f')
    (hXr : Blueprint.LieModel X t n r f') : False := by
  obtain ⟨hq3, hqo, hrq⟩ := char_data hp hp2 hf hadm.1 hrp
  obtain ⟨-, hord, -⟩ := lieOrderFormulasInput X .PSU 4 p f (N36.admissible_of_lieModel' hXp) hXp
  rw [lieOrderNumerator_psu_four] at hord
  have hd : lieOrderDivisor .PSU 4 (p ^ f) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < lieOrderDivisor .PSU 4 (p ^ f) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact false_of_ordProj_le hr2 hadm hXr hord hd0 (ordProj_u4_le hq3 hqo hadm.1 hr2 hrq)
    ((Nat.mul_le_mul_right _ hd).trans (four_mul_pow_nine_le_u4 hq3))

theorem false_of_lieModel_sp4 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hXp : Blueprint.LieModel X .PSp 2 p f) {t : StatedLieTag} {n r f' : ℕ}
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hadm : StatedLieAdmissible t n r f')
    (hXr : Blueprint.LieModel X t n r f') : False := by
  obtain ⟨hq3, -, hrq⟩ := char_data hp hp2 hf hadm.1 hrp
  obtain ⟨-, hord, -⟩ := lieOrderFormulasInput X .PSp 2 p f (N36.admissible_of_lieModel' hXp) hXp
  rw [lieOrderNumerator_psp_two] at hord
  have hd : lieOrderDivisor .PSp 2 (p ^ f) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  have hd0 : 0 < lieOrderDivisor .PSp 2 (p ^ f) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  exact false_of_ordProj_le hr2 hadm hXr hord hd0
    (GSThmB.X10Rec.ordProj_sp4_le (by omega) hadm.1 hr2 hrq)
    ((Nat.mul_le_mul_right _ hd).trans (two_mul_pow_six_le_sp4 hq3))

theorem false_of_lieModel_o7 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hXp : Blueprint.LieModel X .POmegaOdd 3 p f) {t : StatedLieTag} {n r f' : ℕ}
    (hr2 : r ≠ 2) (hrp : r ≠ p) (hadm : StatedLieAdmissible t n r f')
    (hXr : Blueprint.LieModel X t n r f') : False := by
  obtain ⟨hq3, hqo, hrq⟩ := char_data hp hp2 hf hadm.1 hrp
  obtain ⟨-, hord, -⟩ :=
    lieOrderFormulasInput X .POmegaOdd 3 p f (N36.admissible_of_lieModel' hXp) hXp
  rw [lieOrderNumerator_omega_three] at hord
  exact false_of_ordProj_le hr2 hadm hXr hord (by norm_num [lieOrderDivisor])
    (ordProj_o7_le hq3 hqo hadm.1 hr2 hrq) (two_mul_pow_nine_le_o7 hq3)

theorem false_of_inductionTypeField {L X : Type} [Group L] [Group X] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hI : InductionTypeField p L)
    (e : L ⧸ Open.fusionZStar L ≃* X) {t : StatedLieTag} {n r f' : ℕ} (hr2 : r ≠ 2)
    (hrp : r ≠ p) (hadm : StatedLieAdmissible t n r f') (hXr : Blueprint.LieModel X t n r f') :
    False := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv L
  set e' := eZ.symm.trans e
  obtain ⟨f, hf, h⟩ := hI
  rcases h with ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨-, -, hm⟩ | ⟨hev, hsl⟩
  · exact false_of_lieModel_o7 hp hp2 hf (GSThmB.OddQuot.lieModel_of_equiv e' hm) hr2 hrp hadm
      hXr
  · exact false_of_lieModel_l4 hp hp2 hf (GSThmB.OddQuot.lieModel_of_equiv e' hm) hr2 hrp hadm
      hXr
  · exact false_of_lieModel_u4 hp hp2 hf (GSThmB.OddQuot.lieModel_of_equiv e' hm) hr2 hrp hadm
      hXr
  · exact false_of_lieModel_sp4 hp hp2 hf (GSThmB.OddQuot.lieModel_of_equiv e' hm) hr2 hrp hadm
      hXr
  · have hf2 : 2 ≤ f := by
      obtain ⟨k, hk⟩ := hev
      omega
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h5 : 5 ≤ p ^ f := by
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf2
    obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts hp hp2 hf h5 hsl
    exact hrp (L35.char_eq_of_pslTwo hp hp2 h5 hr2 (GSThmB.OddQuot.lieModel_of_equiv e' hQm) hXr)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.RowLie
