module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveE6
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.DefChar Polynomial
open scoped Matrix

noncomputable abbrev twE6PhiTwoWeyl :
    WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord

noncomputable abbrev twE6PhiOneWeyl :
    WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord

section Orders


theorem twE6PhiTwoWeyl_smul (x : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6PhiTwoWeyl • x =
      toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]

theorem twE6PhiOneWeyl_smul (x : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6PhiOneWeyl • x =
      toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]

theorem factorization_five_card_twistedE6_of_dvd_add_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f + 1) :
    (Nat.card (twistedE6RootGroup K σ)).factorization 5 = 6 * (ℓ ^ f + 1).factorization 5 + 1 := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpq : ¬ 5 ∣ ℓ ^ f := Proving.not_five_dvd_of_dvd_add_one h5
  have h := ordProj_card_twistedE6 hℓ hf K hK σ hσ Nat.prime_five (by norm_num) hpq
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (5 : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have heQ : orderOf (Q : ZMod 5) = 1 := by
    rw [orderOf_eq_one_iff]
    have h1 : ((ℓ ^ f + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
    push_cast [hQdef] at h1 ⊢
    linear_combination -h1
  have hlte : ∀ d : ℕ, d ≠ 0 → 5 ^ ((Q ^ d - 1).natAbs).factorization 5 =
      5 ^ ((Q - 1).natAbs).factorization 5 * 5 ^ d.factorization 5 := fun d hd => by
    have h1 := ordProj_int_pow_sub_one_of_dvd Nat.prime_five (by norm_num) hQ2 hpQ heQ
      one_ne_zero hd
    rwa [one_mul, pow_one] at h1
  have hQ1 : (Q - 1).natAbs = ℓ ^ f + 1 := by
    rw [hQdef, show -((ℓ ^ f : ℕ) : ℤ) - 1 = -((ℓ ^ f + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
  simp only [degreesE, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [hlte 2 (by norm_num), hlte 5 (by norm_num), hlte 6 (by norm_num), hlte 8 (by norm_num),
    hlte 9 (by norm_num), hlte 12 (by norm_num),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 2),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 6),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 8),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 9),
    ordProj_eq_one_of_not_dvd' (by norm_num : ¬ 5 ∣ 12),
    Nat.Prime.factorization_self Nat.prime_five, hQ1] at h
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 5) ?_
  change 5 ^ _ = 5 ^ _
  rw [h]
  ring

theorem factorization_five_card_twistedE6_of_dvd_sub_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f - 1) :
    (Nat.card (twistedE6RootGroup K σ)).factorization 5 = 4 * (ℓ ^ f - 1).factorization 5 := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpq : ¬ 5 ∣ ℓ ^ f := not_five_dvd_of_dvd_sub_one (by omega) h5
  have h := ordProj_card_twistedE6 hℓ hf K hK σ hσ Nat.prime_five (by norm_num) hpq
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (5 : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have heQ : orderOf (Q : ZMod 5) = 2 := by
    have hQm : (Q : ZMod 5) = -1 := by
      have h2 : ((Q + 1 : ℤ) : ZMod 5) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        have h3 : Q + 1 = -(((ℓ ^ f - 1 : ℕ) : ℤ)) := by
          rw [hQdef]
          push_cast [show 1 ≤ ℓ ^ f by omega]
          ring
        rw [h3, dvd_neg]
        exact Int.natCast_dvd_natCast.2 h5
      push_cast at h2
      exact eq_neg_of_add_eq_zero_left h2
    rw [hQm]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  rw [prod_ordProj_int_pow_sub_one Nat.prime_five (by norm_num) hQ2 hpQ heQ (degreesE Tag.E6)
    (by decide)] at h
  have hQsq : (Q ^ 2 - 1).natAbs = (ℓ ^ f) ^ 2 - 1 := by
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [hQdef, neg_sq, show ((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1 = (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [h1]; ring, Int.natAbs_natCast]
  have hlen : ((degreesE Tag.E6).filter fun d => 2 ∣ d).length = 4 := by decide
  rw [hQsq, hlen, ← pow_mul,
    factorization_sq_sub_one_of_dvd_sub_one Nat.prime_five (by norm_num) hq2 h5] at h
  rw [Nat.pow_right_injective (by norm_num : 2 ≤ 5) h, mul_comm]

theorem factorization_card_twistedE6_le_of_dvd_add_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f + 1) :
    (Nat.card (twistedE6RootGroup K σ)).factorization 5 ≤
      (((toMat TwistTag.E6.tag.rank twE6TwoMat).charpoly.eval
        ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization 5 + 1 := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he := Proving.orderOf_natCast_zmod_five_of_dvd_add_one h5
  have h2 := ordProj_charpoly_eval_of_blocks Nat.prime_five le_rfl hq2 he (by norm_num) _
    twE6Two_charpoly (by decide)
  have h3 : [2, 2, 2, 2, 2, 2].count 2 = 6 := by decide
  rw [h3, ← pow_mul] at h2
  rw [factorization_five_card_twistedE6_of_dvd_add_one hℓ hf K hK σ hσ h5,
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2,
    factorization_sq_sub_one_of_dvd_add_one Nat.prime_five (by norm_num) hq2 h5, mul_comm]

theorem factorization_card_twistedE6_eq_of_dvd_sub_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f - 1) :
    (Nat.card (twistedE6RootGroup K σ)).factorization 5 =
      (((toMat TwistTag.E6.tag.rank twE6OneMat).charpoly.eval
        ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization 5 := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have he := orderOf_natCast_zmod_five_of_dvd h5 (by omega)
  have h2 := ordProj_charpoly_eval_of_blocks Nat.prime_five le_rfl hq2 he (by norm_num) _
    twE6One_charpoly (by decide)
  have h3 : [1, 1, 1, 1, 2, 2].count 1 = 4 := by decide
  rw [h3, ← pow_mul, pow_one] at h2
  rw [factorization_five_card_twistedE6_of_dvd_sub_one hℓ hf K hK σ hσ h5,
    Nat.pow_right_injective (by norm_num : 2 ≤ 5) h2, mul_comm]

theorem isInnerLocallyBalanced_twistedE6_five_of_dvd_add_one
    (hres : TwistedE6LangTorusPlaneBalance twE6PhiTwoWeyl 5 fun q => 5 ∣ q + 1) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f + 1) :
    IsInnerLocallyBalanced 5 (twistedE6RootGroup K σ) :=
  isInnerLocallyBalanced_twistedE6_of_langTorus hℓ hf K hK σ hσ Nat.prime_five (by norm_num)
    twE6PhiTwoWeyl_smul (n := 2) (by norm_num) twE6Two_pow hres h5
    (charpoly_eval_ne_zero_of_blocks (Nat.one_lt_pow (by omega) hℓ.one_lt) _ twE6Two_charpoly)
    (factorization_card_twistedE6_le_of_dvd_add_one hℓ hf K hK σ hσ h5)

theorem isInnerLocallyBalanced_twistedE6_five_of_dvd_sub_one
    (hres : TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h5 : 5 ∣ ℓ ^ f - 1) :
    IsInnerLocallyBalanced 5 (twistedE6RootGroup K σ) :=
  isInnerLocallyBalanced_twistedE6_of_langTorus hℓ hf K hK σ hσ Nat.prime_five (by norm_num)
    twE6PhiOneWeyl_smul (n := 2) (by norm_num) twE6One_pow hres h5
    (charpoly_eval_ne_zero_of_blocks (Nat.one_lt_pow (by omega) hℓ.one_lt) _ twE6One_charpoly)
    ((factorization_card_twistedE6_eq_of_dvd_sub_one hℓ hf K hK σ hσ h5).le.trans (Nat.le_succ _))

end Orders

section Catalogue


theorem crossCharInnerAt_twistedE6_five_of_lang
    (h1 : TwistedE6LangTorusPlaneBalance twE6PhiTwoWeyl 5 fun q => 5 ∣ q + 1)
    (h2 : TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1) :
    CrossCharInnerAt .twistedE6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 := by
  rintro ⟨d, hv⟩ _ p _ _ _ ⟨⟨q, hd, h5⟩, rfl⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at h5
  refine IsInnerLocallyBalanced.of_mulEquiv e ?_
  rcases five_dvd_sq_sub_one_iff_or.1 h5 with h | h
  · exact isInnerLocallyBalanced_twistedE6_five_of_dvd_sub_one h2 q.prime_p q.exponent_pos K hK σ
      hσ h
  · exact isInnerLocallyBalanced_twistedE6_five_of_dvd_add_one h1 q.prime_p q.exponent_pos K hK σ
      hσ h

end Catalogue

end CFSG.HardMathSupport.Timmesfeld.CrossChar
