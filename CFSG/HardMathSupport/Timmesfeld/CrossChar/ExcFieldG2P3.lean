module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

theorem three_dvd_sq_sub_one_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : 3 ∣ n ^ 2 - 1 := by
  have h1 : n ^ 2 % 3 = 1 := by
    rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h' | h' <;> simp [Nat.pow_mod, h']
  have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => h (h0 ▸ dvd_zero 3))
  omega

theorem not_three_dvd_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (k : ℕ) : ¬ 3 ∣ ℓ ^ k :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hℓ).2 hℓ3.symm))

section Adjoint


theorem isLocallyBalancedAbs_adjointG2_three_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) :
    IsLocallyBalancedAbs 3 3 (adjointGroup Tag.G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact not_three_dvd_pow hℓ hℓ3 f
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K Nat.prime_three
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K hK3)
    fun x hxp hxo => ?_
  have hNF := conj_normalForm_of_pointwise
    (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)).1
  refine fieldCoreAt_of_oddInnerField hℓ hℓ2 hf K hK hNF Nat.prime_three (fun σ _ => ?_) hxp hxo
  refine not_coprime_card_adjointG2 (fixSubfield σ) Nat.prime_three
    (three_dvd_sq_sub_one_of_not_dvd ?_)
  rw [(SteinbergBT.card_fixSubfield hℓ hf hK σ).2]
  exact not_three_dvd_pow hℓ hℓ3 _

end Adjoint

section AdjointEven


theorem isLocallyBalancedAbs_adjointG2_three_even {f : ℕ} (hf : 2 ≤ f) (hf3 : f ≠ 3)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) :
    IsLocallyBalancedAbs 3 3 (adjointGroup Tag.G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK]; exact not_three_dvd_pow Nat.prime_two (by norm_num) f
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K Nat.prime_three
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K hK3)
    fun x hxp hxo => ?_
  refine fieldCoreAt_G2_even hf K hK Nat.prime_three (fun σ hσ => ?_) (fun σ _ => ?_) hxp hxo
  · obtain ⟨hdvd, hcard⟩ := SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ
    rw [hσ] at hdvd hcard
    rw [hcard]
    obtain ⟨k, rfl⟩ := hdvd
    have hk : 2 ≤ 3 * k / 3 := by omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * k / 3) := Nat.pow_le_pow_right (by norm_num) hk
  · refine not_coprime_card_adjointG2 (fixSubfield σ) Nat.prime_three
      (three_dvd_sq_sub_one_of_not_dvd ?_)
    rw [(SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ).2]
    exact not_three_dvd_pow Nat.prime_two (by norm_num) _

end AdjointEven

theorem regimeG2Field_or_three_of_not_vac {idx : TauCeti.ValidLieTypeIndex}
    (hk : LieFamily.G2.Matches idx.1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ¬ regimeG2Vac idx p) :
    regimeG2Field idx p ∨ ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ p = 3 := by
  obtain ⟨q, hq⟩ := hk
  by_cases h5 : 5 ≤ p
  · refine Or.inl ⟨q, hq, h5, ?_, ?_⟩
    · by_contra hnd
      exact h (Or.inl ⟨q, hq, hnd⟩)
    · by_contra hf
      exact h (Or.inr ⟨q, hq, h5, hf⟩)
  · exact Or.inr ⟨q, hq, (eq_three_or_five_le hp hp2).resolve_right h5⟩

section Family


theorem crossCharFamAt_G2_three : CrossCharFamAt .G2 fun idx p =>
    ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ p = 3 ∧ q.card ≠ 8 := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, rfl, hq8⟩
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  refine IsLocallyBalancedAbs.of_mulEquiv e ?_
  by_cases h2 : q.p = 2
  · have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, h2]
    have hf2 : 2 ≤ q.exponent := by
      by_contra hlt
      have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rw [hqc, h1] at hq3
      omega
    have hf3 : q.exponent ≠ 3 := fun h => hq8 (by rw [hqc, h]; norm_num)
    exact isLocallyBalancedAbs_adjointG2_three_even hf2 hf3 K (by rw [hK', h2])
  · exact isLocallyBalancedAbs_adjointG2_three_odd q.prime_p h2 (Ne.symm hpq) q.exponent_pos K hK'

@[expose] def G2EightFieldCore : Prop :=
  ∀ (K : Type) [Field K], Nat.card K = 8 → ∀ x : MulAut (adjointGroup Tag.G2 K), orderOf x = 3 →
    x ∉ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range →
      FieldCoreAt 3 x

theorem crossCharFamAt_G2_eight_of_fieldCore (h : G2EightFieldCore) :
    CrossCharFamAt .G2 fun idx p =>
      ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ p = 3 ∧ q.card = 8 := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, rfl, hq8⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hK8 : Nat.card K = 8 := hK.trans hq8
  have hK3 : ¬ 3 ∣ Nat.card K := by rw [hK8]; norm_num
  refine IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjoint_of_fieldCore K
    Nat.prime_three
    (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K hK3)
    fun x hxp hxo => h K hK8 x hxp hxo)

theorem crossCharFamAt_G2_open_of_eight
    (h8 : CrossCharFamAt .G2 fun idx p =>
      ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ p = 3 ∧ q.card = 8) :
    CrossCharFamAt .G2 fun idx p => ¬ regimeG2Vac idx p ∧ ¬ regimeG2Field idx p := by
  rintro idx hidx p hp hp2 hch ⟨hR, hF⟩
  rcases regimeG2Field_or_three_of_not_vac hidx hp hp2 hR with hF' | ⟨q, hq, rfl⟩
  · exact absurd hF' hF
  · by_cases hq8 : q.card = 8
    · exact h8 idx hidx 3 hp hp2 hch ⟨q, hq, rfl, hq8⟩
    · exact crossCharFamAt_G2_three idx hidx 3 hp hp2 hch ⟨q, hq, rfl, hq8⟩

theorem crossCharFamAt_G2_open_of_fieldCore (h : G2EightFieldCore) :
    CrossCharFamAt .G2 fun idx p => ¬ regimeG2Vac idx p ∧ ¬ regimeG2Field idx p :=
  crossCharFamAt_G2_open_of_eight (crossCharFamAt_G2_eight_of_fieldCore h)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
