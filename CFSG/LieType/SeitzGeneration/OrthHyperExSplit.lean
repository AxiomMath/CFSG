module

public import CFSG.LieType.SeitzGeneration.OrthCubeM2
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.RankThree.PartOne.CTP.SeitzLinear

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank TauCeti
open CFSG.RankThree.Classical2 (orthDerived)

section Abstract

variable {d : ValidLieTypeIndex} {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_hyperGen_split {π : elementaryGroup Q →* Cat d} (hc : IsOrthogonalCover Q π)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) {k : ℕ} (P : Fin k → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j))
    (hsplit : (p ∣ Nat.card K - 1 ∧ 3 ≤ k) ∨ (p ∣ Nat.card K ^ 2 - 1 ∧ 4 ≤ k)) :
    ∃ E' : Subgroup (Cat d), IsElemAbelian p E' ∧ Nat.card E' = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rcases hsplit with ⟨hpq, hk⟩ | ⟨hpq, hk⟩
  ·
    have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpq
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hdvd
    have hζ : (u : K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
    have hζ1 : (u : K) ≠ 1 := by
      intro h
      have : u = 1 := Units.ext h
      rw [this, orderOf_one] at hu
      exact hp.one_lt.ne' hu.symm
    let i₀ : Fin k := ⟨0, by omega⟩
    let i₁ : Fin k := ⟨1, by omega⟩
    let i₂ : Fin k := ⟨2, by omega⟩
    obtain ⟨E, hEab, hEcard, W, hW0, hWQ, hWE⟩ := exists_stable_cube_diag hc.nondegenerate hT hE
      hp hp2 (hP i₀ i₁ (by simp [i₀, i₁, Fin.ext_iff])) (hP i₀ i₂ (by simp [i₀, i₂, Fin.ext_iff]))
      (hP i₁ i₂ (by simp [i₁, i₂, Fin.ext_iff])) hζ hζ1
    exact exists_hyperGen_of_stable_cube hc hp hp2 hpK hEab hEcard hW0 hWQ hWE
  · obtain ⟨x, hdet, hxp, hx1⟩ := exists_sl2_order hp hpq
    let i₀ : Fin k := ⟨0, by omega⟩
    let i₁ : Fin k := ⟨1, by omega⟩
    let i₂ : Fin k := ⟨2, by omega⟩
    let i₃ : Fin k := ⟨3, by omega⟩
    obtain ⟨E, hEab, hEcard, W, hW0, hWQ, hWE⟩ := exists_stable_cube_m2 hc.nondegenerate hT hE
      hp hp2 (hP i₀ i₁ (by simp [i₀, i₁, Fin.ext_iff])) (hP i₂ i₃ (by simp [i₂, i₃, Fin.ext_iff]))
      (hP i₀ i₂ (by simp [i₀, i₂, Fin.ext_iff])) (hP i₀ i₃ (by simp [i₀, i₃, Fin.ext_iff]))
      (hP i₁ i₂ (by simp [i₁, i₂, Fin.ext_iff])) (hP i₁ i₃ (by simp [i₁, i₃, Fin.ext_iff])) hdet
      hxp hx1
    exact exists_hyperGen_of_stable_cube hc hp hp2 hpK hEab hEcard hW0 hWQ hWE

end Abstract

section Residuals

@[expose] def ONonsplitPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  IsOrthogonalIndex d.1 ∧ ∃ (r : ℕ) (q : PrimePower),
    (d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) ∧ ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1

@[expose] def OSmallPrime (d : ValidLieTypeIndex) (p : ℕ) : Prop :=
  IsOrthogonalIndex d.1 ∧ ∃ q : PrimePower, (d.1 = .B 3 q ∨ d.1 = .twistedD 4 q) ∧
    p ∣ q.card + 1

@[expose] def OrthHyperExNonsplit : Prop := SeitzHyperLieEx fun d p _ => ONonsplitPrime d p

@[expose] def OrthHyperExSmall : Prop := SeitzHyperLieEx fun d p _ => OSmallPrime d p

theorem card_fixedField_eq_card (d : ValidLieTypeIndex) {q : PrimePower}
    (hq : d.1.characteristic = q.p ∧ d.1.fieldExponent = q.exponent) :
    Nat.card ↥(ValidLieTypeIndex.fixedField d) = q.card := by
  rw [card_fixedField_eq, PrimePower.card_def]
  simp only [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent, hq.1, hq.2]

theorem dvd_sq_sub_one_of_dvd_add_one {p q : ℕ} (h : p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at h
    simp [h]
  · have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
      have : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
      rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
    rw [this]
    exact h.mul_right _

theorem hyperExFor_orthogonal_of_residuals (hN : OrthHyperExNonsplit) (hS : OrthHyperExSmall) :
    HyperExFor fun d => IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, hd⟩
  have hfp : Fact p.Prime := ⟨hp⟩
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    by_cases hns : ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1
    · exact hN _ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, Or.inl ⟨r, q, rfl, hr3, hq⟩, r, q, Or.inl rfl,
        hns.1, hns.2⟩
    by_cases hsm : r = 3 ∧ p ∣ q.card + 1
    · obtain ⟨rfl, h⟩ := hsm
      exact hS _ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, Or.inl ⟨3, q, rfl, hr3, hq⟩, q, Or.inl rfl, h⟩
    have hq' : p ≠ q.p := by simpa using hpd
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.B r q, hv⟩ (q := q) (by simp)
    have hcard' : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent := by
      rw [hcard, PrimePower.card_def]
    have h2 : (2 : ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard'
      have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p := ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have hpK : (p : ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 :=
      CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard']; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadOdd (K := ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) h2 hr3
    have hEq := commutator_orthogonalGroup_quadOdd
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) h2 hr3
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadOdd r _) hEq hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3)
    refine exists_hyperGen_split hπ hreg.2 hEq hp hp2 hpK (oddPair _) (fun i j hij =>
      oddPair_orth hij) ?_
    by_cases h1 : p ∣ q.card - 1
    · exact Or.inl ⟨by rw [hcard]; exact h1, hr3⟩
    · have h2' : p ∣ q.card + 1 := by
        by_contra h3
        exact hns ⟨h1, h3⟩
      have hr4 : 4 ≤ r := by
        by_contra h4
        exact hsm ⟨by omega, h2'⟩
      exact Or.inr ⟨by rw [hcard]; exact dvd_sq_sub_one_of_dvd_add_one h2', hr4⟩
  ·
    by_cases hns : ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1
    · exact hN _ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, Or.inr (Or.inl ⟨r, q, rfl⟩), r, q,
        Or.inr (Or.inl rfl), hns.1, hns.2⟩
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1)
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.D r q, hv⟩ (q := q) (by simp)
    have hpK : (p : ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) ≠ 0 :=
      CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard, PrimePower.card_def]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadPlus (K := ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r)
      (by omega)
    have hEq := commutator_orthogonalGroup_quadPlus
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r) (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadPlus r _) hEq hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
    refine exists_hyperGen_split hπ hreg.2 hEq hp hp2 hpK (plusPair _) (fun i j hij =>
      plusPair_orth hij) ?_
    by_cases h1 : p ∣ q.card - 1
    · exact Or.inl ⟨by rw [hcard]; exact h1, by omega⟩
    · have h2' : p ∣ q.card + 1 := by
        by_contra h3
        exact hns ⟨h1, h3⟩
      exact Or.inr ⟨by rw [hcard]; exact dvd_sq_sub_one_of_dvd_add_one h2', hr4⟩
  ·
    by_cases hns : ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1
    · exact hN _ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, Or.inr (Or.inr ⟨r, q, rfl⟩), r, q,
        Or.inr (Or.inr rfl), hns.1, hns.2⟩
    by_cases hsm : r = 4 ∧ p ∣ q.card + 1
    · obtain ⟨rfl, h⟩ := hsm
      exact hS _ p hp hp2 hpd hl ⟨E₀, hE₀, hc₀, Or.inr (Or.inr ⟨4, q, rfl⟩), q, Or.inr rfl, h⟩
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.twistedD r q, hv⟩ (q := q) (by simp)
    have hpK : (p : ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) ≠ 0 :=
      CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard, PrimePower.card_def]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadMinus (n := r) hr4 hirr
    have hEq := commutator_orthogonalGroup_quadMinus (n := r) hr4 hirr
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus r _ b c) hEq hreg.1 e
    refine exists_hyperGen_split hπ hreg.2 hEq hp hp2 hpK (minusPair _ b c) (fun i j hij =>
      minusPair_orth hij) ?_
    by_cases h1 : p ∣ q.card - 1
    · exact Or.inl ⟨by rw [hcard]; exact h1, by omega⟩
    · have h2' : p ∣ q.card + 1 := by
        by_contra h3
        exact hns ⟨h1, h3⟩
      have hr5 : 5 ≤ r := by
        by_contra h5
        exact hsm ⟨by omega, h2'⟩
      exact Or.inr ⟨by rw [hcard]; exact dvd_sq_sub_one_of_dvd_add_one h2', by omega⟩

end Residuals

end CFSG.LieType.SeitzGeneration
