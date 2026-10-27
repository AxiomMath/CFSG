module

public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Assembly.LowTwoRank

@[expose] def OrthogonalOddPlanes : Prop :=
  ∀ (r p : ℕ) (K : Type) [Field K] [Finite K], 3 ≤ r → p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K →
    (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K))),
      CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
        Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
          ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

@[expose] def OrthogonalPlusPlanes : Prop :=
  ∀ (r p : ℕ) (K : Type) [Field K] [Finite K], 4 ≤ r → p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K →
    ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K))),
      CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
        Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
          ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

@[expose] def OrthogonalMinusPlanes : Prop :=
  ∀ (r p : ℕ) (K : Type) [Field K] [Finite K] (b c : K), 4 ≤ r → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K →
    ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c))),
      CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 →
        Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
          ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

theorem card_fixedField_eq (d : TauCeti.ValidLieTypeIndex) :
    Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d) =
      TauCeti.ValidLieTypeIndex.characteristic d ^ TauCeti.ValidLieTypeIndex.fieldExponent d := by
  rw [TauCeti.ValidLieTypeIndex.card_fixedField,
    TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]

theorem not_dvd_pow_of_ne {p ℓ f : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (h : p ≠ ℓ) :
    ¬ p ∣ ℓ ^ f := fun hd =>
  h ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hd))

theorem seitzInnerOrthogonal_of_leaves (hO : OrthogonalOddPlanes) (hP : OrthogonalPlusPlanes)
    (hM : OrthogonalMinusPlanes) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, horth⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero
        h2 hr3
    have : IsSimpleGroup (Cat ⟨.B r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.B r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact hO r p _ hr3 hp hp5 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') h2 E₁
      hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
    have : IsSimpleGroup (Cat ⟨.D r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.D r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact hP r p _ hr4 hp hp5 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') E₁ hE₁
      hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hr4 hirr
    have : IsSimpleGroup (Cat ⟨.twistedD r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedD r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact hM r p _ b c hr4 hirr hp hp5 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      E₁ hE₁ hcard₁

end CFSG.LieType.SeitzGeneration
