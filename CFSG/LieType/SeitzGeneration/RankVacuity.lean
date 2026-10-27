module

public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LieType.SeitzGeneration.ThreeIndepSp
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThree
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.Assembly.LowTwoRank

section Abstract

theorem not_rankLE2_of_hasThreeIndep {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : HasThreeIndep G p) : ¬ RankLE2 p G := fun hr => by
  obtain ⟨e₁, e₂, e₃, h12, h13, h23, h₁, h₂, h₃, hi⟩ := h
  exact false_of_three_independent hp hr h12 h13 h23 h₁ h₂ h₃ hi

theorem not_rankLE2_of_mulEquiv {K L : Type*} [Group K] [Group L] [Finite L] (e : K ≃* L)
    {p : ℕ} (hp : p.Prime) (h : HasThreeIndep L p) : ¬ RankLE2 p K :=
  fun hr => not_rankLE2_of_hasThreeIndep hp h (RankLE2.of_mulEquiv e hr)

end Abstract

theorem not_rankLE2_linear {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hpq : p ∣ q.card - 1)
    (hm : 4 ≤ m) : ¬ RankLE2 p (Cat ⟨.A m q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField q.p q.exponent)) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin (m + 1))
      (GaloisField q.p q.exponent) → Matrix (Fin (m + 1)) (Fin (m + 1))
        (GaloisField q.p q.exponent)) Subtype.val_injective
  exact not_rankLE2_of_mulEquiv (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv) hp
    (hasThreeIndep_psl (by omega) hp (by rw [hcardF]; exact hpq))

theorem not_rankLE2_unitary {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ q.card + 1) (hm : 4 ≤ m) : ¬ RankLE2 p (Cat ⟨.twistedA m q, hv⟩) := by
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hfin := hU.finite
  exact not_rankLE2_of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv)
    hp (hasThreeIndep_psu hU (by omega) hp (by rw [hqcard]; exact hpq))

theorem not_rankLE2_psp_model {d : TauCeti.ValidLieTypeIndex} {r ℓ f p : ℕ} {K : Type} [Field K]
    (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime) (hK : Nat.card K = ℓ ^ f)
    (hr : 3 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K ^ 2 - 1) :
    ¬ RankLE2 p (Cat d) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  exact not_rankLE2_of_mulEquiv e hp (hasThreeIndep_psp hr hp hp2 hpq)

theorem not_rankLE2_symplecticHigh_three :
    ∀ (d : TauCeti.ValidLieTypeIndex), IsSymplecticHigh d.1 → ∀ p : ℕ, p = 3 →
      p ≠ d.1.characteristic → ¬ RankLE2 p (Cat d) := by
  rintro ⟨d, hv⟩ hsp p hp3 hpd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  subst hp3
  rcases hsp with ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  · have hq : 3 ≠ q.p := by simpa using hpd
    have hpq : 3 ∣ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) ^ 2 - 1 := by
      rw [CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv]
      refine three_dvd_sq_sub_one fun h => hq ?_
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow h))
    exact not_rankLE2_psp_model (d := ⟨.B r q, hv⟩)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      q.prime_p (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hr3 Nat.prime_three
      (by norm_num) hpq
  · have hq : 3 ≠ q.p := by simpa using hpd
    have hr3 : 3 ≤ r := hrange.1
    have hpq : 3 ∣ Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) ^ 2 - 1 := by
      rw [card_fixedField_C r q hv]
      refine three_dvd_sq_sub_one fun h => hq ?_
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
        (Nat.prime_three.dvd_of_dvd_pow h))
    exact not_rankLE2_psp_model (d := ⟨.C r q, hv⟩)
      (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      q.prime_p (card_fixedField_C r q hv) hr3 Nat.prime_three (by norm_num) hpq

end CFSG.LieType.SeitzGeneration
