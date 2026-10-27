module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.Model
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicTriality

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Odd


theorem extSeitzAtInnerFor_trialityD4_split_odd {q : TauCeti.PrimePower} :
    ExtSeitzAtInnerFor (.trialityD4 q) fun p => p ∣ q.card - 1 := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, σ, hX, hσ, hσ3, ⟨e⟩⟩ := exists_trialityD4_model_of_isoLie hiso
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hX' : Nat.card X = (q.p ^ q.exponent) ^ 3 := by rw [hX, hqc]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := by intro c; rw [hσ, hqc]
  have : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) :=
    MulEquiv.isSimpleGroup e.symm
  have : CharP X q.p := charP_of_trialityD4_model X hX
  have hpq' : p ∣ q.p ^ q.exponent - 1 := by rw [← hqc]; exact hpq
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  exact closure_centralizers_graphFixed_D4_split q.p q.exponent q.prime_p q.exponent_pos X hX' σ
    hσ' hσ3 p (Ne.symm (by
      rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at hpd)) hp5 hpq' E₁ hcard₁

theorem card_isoLie_trialityD4_all {q : TauCeti.PrimePower} {K : Type} [Group K]
    (hiso : IsoLie K (.trialityD4 q)) :
    Nat.card K = q.card ^ 12 * (q.card ^ 2 - 1) * (q.card ^ 6 - 1) *
      (q.card ^ 8 + q.card ^ 4 + 1) := by
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := exists_trialityD4_model_of_isoLie hiso
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hX' : Nat.card X = (q.p ^ q.exponent) ^ 3 := by rw [hX, hqc]
  have hσ' : ∀ c, σ c = c ^ ((q.p ^ q.exponent) ^ 1) := by intro c; rw [hσ, hqc, pow_one]
  obtain ⟨hC, -, -⟩ := triality_both_orientations_exact_finite_order q.p q.exponent q.prime_p
    q.exponent_pos X hX' 1 (Or.inl rfl) σ.toRingHom hσ'
  rw [Nat.card_congr e.toEquiv, hC, hqc]

theorem extSeitzAtInnerFor_trialityD4_noPlane {q : TauCeti.PrimePower} :
    ExtSeitzAtInnerFor (.trialityD4 q) fun p => ¬ p ∣ q.card - 1 ∧ ¬ p ∣ q.card + 1 ∧
      ¬ (p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd ⟨h0, h1, h2⟩ E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard
    hinner
  intro E₁ hE₁ hcard₁
  exfalso
  have := hE₁
  have hQ : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hQ2 : 2 ≤ q.card := by
    rw [hQ]
    calc 2 ≤ q.p := q.prime_p.two_le
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have hq0 : ¬ p ∣ q.card := by
    rw [hQ]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd)
    apply hpd
    rw [TauCeti.LieTypeIndex.characteristic_trialityD4]
    exact this
  have hdvd : p ∣ Nat.card K := by
    have h0' := Subgroup.card_subgroup_dvd_card E₁
    rw [hcard₁] at h0'
    exact (dvd_pow_self p two_ne_zero).trans h0'
  rw [card_isoLie_trialityD4_all hiso] at hdvd
  have h12 := CFSG.RankThree.PartOne.SEITZ3.d4_prime_twelve hp hQ2 hdvd hq0 h0 h1
    (fun h => h2 (Or.inl h)) (fun h => h2 (Or.inr h))
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := exists_trialityD4_model_of_isoLie hiso
  have : Finite (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) := Finite.of_equiv K e.toEquiv
  have hX' : Nat.card X = (q.p ^ q.exponent) ^ 3 := by rw [hX, hQ]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := by intro c; rw [hσ, hQ]
  rw [hQ] at h12
  have h3 := CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve q.prime_p q.exponent_pos X hX'
    σ hσ' hp hp5 h12
  have h4 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e
  have h5 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
  omega

end Odd

section Residuals

@[expose] def TrialityOddQPlus : Prop :=
  ∀ q : TauCeti.PrimePower, q.p ≠ 2 → ExtSeitzAtInnerFor (.trialityD4 q) fun p => p ∣ q.card + 1

@[expose] def TrialityOddPhi36 : Prop :=
  ∀ q : TauCeti.PrimePower, q.p ≠ 2 → ExtSeitzAtInnerFor (.trialityD4 q) fun p =>
    p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1

end Residuals

section Assembly


theorem extSeitzAtInnerFor_trialityD4_odd_of_residuals (hQ : TrialityOddQPlus)
    (h36 : TrialityOddPhi36) {q : TauCeti.PrimePower} (hq : q.p ≠ 2) :
    ExtSeitzAtInnerFor (.trialityD4 q) fun _ => True := by
  intro K _ _ _ hnab hiso p hp hp5 hpd _ E hE hcard hinner
  by_cases h0 : p ∣ q.card - 1
  · exact extSeitzAtInnerFor_trialityD4_split_odd K hnab hiso p hp hp5 hpd h0 E hE hcard hinner
  by_cases h1 : p ∣ q.card + 1
  · exact hQ q hq K hnab hiso p hp hp5 hpd h1 E hE hcard hinner
  by_cases h2 : p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1
  · exact h36 q hq K hnab hiso p hp hp5 hpd h2 E hE hcard hinner
  exact extSeitzAtInnerFor_trialityD4_noPlane K hnab hiso p hp hp5 hpd ⟨h0, h1, h2⟩ E hE hcard
    hinner

theorem seitzExcAnisotropicTrialityOdd_of_residuals
    (hQ : TrialityOddQPlus)
    (h36 : TrialityOddPhi36) : SeitzExcAnisotropicTrialityOdd := by
  refine seitzExcAnisotropicForAt_of_family (c := TauCeti.LieTypeIndex.trialityD4)
    (P := fun q _ => q.p ≠ 2) (F := IsTrialityIndex)
    (Q := fun d p => 5 ≤ p ∧ ∃ q : TauCeti.PrimePower, d = .trialityD4 q ∧ q.p ≠ 2)
    (fun _ hv => CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv)
    (fun q => by
      by_cases hq : q.p ≠ 2
      · exact (extSeitzAtInnerFor_trialityD4_odd_of_residuals hQ h36 hq).mono (fun _ _ => trivial)
      · exact fun K _ _ _ _ _ p _ _ _ hP => absurd hP hq)
    fun d p _ ⟨h5, q, hd, hq⟩ => ⟨q, hd, h5, hq⟩

end Assembly

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
