module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalCoefficientRing
public import CFSG.CharacterTheory.TwoRankLowerBound.LocalizedAlgebraicIntegers

public section

namespace CFSG.BlockBasics

open CFSG CFSG.BrauerThirdMainTheorem.Helpers CFSG.TwoRankLowerBound.Helpers

theorem residue_prime_existence (p : ℕ) (hp : p.Prime) :
    (∃ m : Ideal BlocksAlgInt, m.IsMaximal ∧ (p : BlocksAlgInt) ∈ m) ∧
      ∀ m : Ideal BlocksAlgInt, m.IsMaximal → (p : BlocksAlgInt) ∈ m →
        CharP (BlocksAlgInt ⧸ m) p := by
  refine ⟨?_, ?_⟩
  · have : Algebra.IsIntegral ℤ ComplexAlgebraicIntegers := complexAlgebraicIntegers_integral
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    have hPprime : P.IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)
    have hPbot : P ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    have : P.IsMaximal := hPprime.isMaximal hPbot
    have hker : RingHom.ker (algebraMap ℤ ComplexAlgebraicIntegers) ≤ P := by
      intro z hz
      rw [RingHom.mem_ker] at hz
      have hz' : (z : ℂ) = 0 := by simpa using congrArg Subtype.val hz
      rw [show z = 0 by exact_mod_cast hz']
      exact P.zero_mem
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P hker
    refine ⟨Q, hQmax, ?_⟩
    have hpP : (p : ℤ) ∈ P := Ideal.subset_span rfl
    rw [← hQ] at hpP
    simpa using hpP
  · intro m hm hpm
    have : m.IsMaximal := hm
    obtain ⟨q, hq, hchar, hmem⟩ := complexAlgebraicIntegers_maximal_residue_characteristic m
    have hqp : (q : ℤ) ∣ p := (hmem p).mp (by simpa using hpm)
    have hqp' : q ∣ p := by exact_mod_cast hqp
    rcases (Nat.dvd_prime hp).mp hqp' with h | h
    · exact absurd h hq.one_lt.ne'
    · exact h ▸ hchar

theorem localCoefficientSubring_eq_localized (m : Ideal BlocksAlgInt) [hm : m.IsMaximal] :
    localCoefficientSubring m hm = localizedComplexIntegerRing m := by
  ext x
  rw [localizedComplexIntegerRing_mem_iff_fraction]
  change x ∈ BlocksLocalRing m ↔ _
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a, b, hb, rfl⟩

theorem fraction_mem_localMaxIdeal_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (a b : BlocksAlgInt) (hb : b ∉ m) : (a : ℂ) / b ∈ BlocksLocalMaxIdeal m ↔ a ∈ m := by
  constructor
  · rintro ⟨a', b', ha', hb', hequal⟩
    have hb0 := denominator_ne_zero m hb
    have hb'0 := denominator_ne_zero m hb'
    have hcross : (a : ℂ) * b' = a' * b := by
      field_simp at hequal
      linear_combination hequal
    have hcrossInt : a * b' = a' * b := Subtype.ext hcross
    have hmem : a * b' ∈ m := hcrossInt ▸ m.mul_mem_right b ha'
    exact (hm.isPrime.mem_or_mem hmem).resolve_right hb'
  · intro ha
    exact ⟨a, b, ha, hb, rfl⟩

theorem localCoefficient_isUnit_iff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (x : localCoefficientSubring m hm) : IsUnit x ↔ (x : ℂ) ∉ BlocksLocalMaxIdeal m := by
  constructor
  · intro hunit hmem
    have hx : x ∈ localCoefficientMaxIdeal m hm := hmem
    exact (localCoefficientMaxIdeal_isMaximal m hm).ne_top
      ((localCoefficientMaxIdeal m hm).eq_top_of_isUnit_mem hx hunit)
  · exact localRing_isUnit_of_not_mem m hm x

theorem local_coefficient_residue (p : ℕ) (m : Ideal BlocksAlgInt) [hm : m.IsMaximal]
    [CharP (BlocksAlgInt ⧸ m) p] :
    letI : Field (BlocksAlgInt ⧸ m) := Ideal.Quotient.field m
    Nonempty (Localization.AtPrime m ≃+* localCoefficientSubring m hm) ∧
    ∃ r : localCoefficientSubring m hm →+* BlocksAlgInt ⧸ m,
      (∀ (a b : BlocksAlgInt) (hb : b ∉ m),
        r ⟨(a : ℂ) / b, a, b, hb, rfl⟩ = Ideal.Quotient.mk m a / Ideal.Quotient.mk m b) ∧
      Function.Surjective r ∧
      (∀ x : localCoefficientSubring m hm, r x = 0 ↔ (x : ℂ) ∈ BlocksLocalMaxIdeal m) ∧
      (∃ _ : IsLocalRing (localCoefficientSubring m hm), ∀ x : localCoefficientSubring m hm,
        x ∈ IsLocalRing.maximalIdeal (localCoefficientSubring m hm) ↔
          (x : ℂ) ∈ BlocksLocalMaxIdeal m) ∧
      (∀ (a b : BlocksAlgInt) (hb : b ∉ m),
        IsUnit (⟨(a : ℂ) / b, a, b, hb, rfl⟩ : localCoefficientSubring m hm) ↔ a ∉ m) ∧
      (∀ n : ℤ, (n : ℂ) ∈ BlocksLocalMaxIdeal m ↔ (p : ℤ) ∣ n) ∧
      ∀ n : ℤ, IsUnit (n : localCoefficientSubring m hm) ↔ ¬ (p : ℤ) ∣ n := by
  classical
  let : Field (BlocksAlgInt ⧸ m) := Ideal.Quotient.field m
  have hEq := localCoefficientSubring_eq_localized m
  let e : localCoefficientSubring m hm ≃+* localizedComplexIntegerRing m :=
    RingEquiv.subringCongr hEq
  let r : localCoefficientSubring m hm →+* BlocksAlgInt ⧸ m :=
    (localizedComplexIntegerResidue m).comp e.toRingHom
  have hformula : ∀ (a b : BlocksAlgInt) (hb : b ∉ m),
      r ⟨(a : ℂ) / b, a, b, hb, rfl⟩ = Ideal.Quotient.mk m a / Ideal.Quotient.mk m b := by
    intro a b hb
    have hsymm : (localizedComplexIntegerEquiv m).symm (e ⟨(a : ℂ) / b, a, b, hb, rfl⟩) =
        IsLocalization.mk' (Localization.AtPrime m) a (⟨b, hb⟩ : m.primeCompl) := by
      rw [RingEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (localizedAlgebraicIntegerEmbedding_fraction m a ⟨b, hb⟩).symm
    change localizedAlgebraicIntegerResidue m
      ((localizedComplexIntegerEquiv m).symm (e ⟨(a : ℂ) / b, a, b, hb, rfl⟩)) = _
    rw [hsymm]
    exact localizedAlgebraicIntegerResidue_fraction m a ⟨b, hb⟩
  have hrep : ∀ x : localCoefficientSubring m hm, ∃ (a b : BlocksAlgInt) (hb : b ∉ m),
      x = ⟨(a : ℂ) / b, a, b, hb, rfl⟩ := by
    intro x
    obtain ⟨a, b, hb, hx⟩ := x.property
    exact ⟨a, b, hb, Subtype.ext hx⟩
  have hbne : ∀ b : BlocksAlgInt, b ∉ m → Ideal.Quotient.mk m b ≠ 0 :=
    fun b hb hzero => hb (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have hkernel : ∀ x : localCoefficientSubring m hm, r x = 0 ↔ (x : ℂ) ∈ BlocksLocalMaxIdeal m := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := hrep x
    rw [hformula a b hb, div_eq_zero_iff, or_iff_left (hbne b hb), Ideal.Quotient.eq_zero_iff_mem]
    exact (fraction_mem_localMaxIdeal_iff m hm a b hb).symm
  have hnonunits : ∀ x : localCoefficientSubring m hm,
      x ∈ nonunits (localCoefficientSubring m hm) ↔ (x : ℂ) ∈ BlocksLocalMaxIdeal m := by
    intro x
    rw [mem_nonunits_iff, localCoefficient_isUnit_iff, not_not]
  have hlocal : IsLocalRing (localCoefficientSubring m hm) := by
    have : Nontrivial (localCoefficientSubring m hm) :=
      ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
    apply IsLocalRing.of_nonunits_add
    intro x y hx hy
    rw [hnonunits] at hx hy ⊢
    exact localMaxIdeal_add m hm hx hy
  have hint : ∀ n : ℤ, (n : ℂ) ∈ BlocksLocalMaxIdeal m ↔ (p : ℤ) ∣ n := by
    intro n
    have hcast : ((n : BlocksAlgInt) : ℂ) = (n : ℂ) := by push_cast; rfl
    rw [← hcast, localMaxIdeal_algInt_iff m hm, ← Ideal.Quotient.eq_zero_iff_mem, map_intCast,
      CharP.intCast_eq_zero_iff (BlocksAlgInt ⧸ m) p]
  refine ⟨⟨(localizedComplexIntegerEquiv m).trans e.symm⟩, r, hformula, ?_, hkernel,
    ⟨hlocal, fun x => (IsLocalRing.mem_maximalIdeal x).trans (hnonunits x)⟩, ?_, hint, ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨⟨(a : ℂ) / (1 : BlocksAlgInt), a, 1, one_not_mem m hm, rfl⟩, ?_⟩
    rw [hformula a 1 (one_not_mem m hm), map_one, div_one]
  · intro a b hb
    rw [localCoefficient_isUnit_iff]
    exact not_congr (fraction_mem_localMaxIdeal_iff m hm a b hb)
  · intro n
    rw [localCoefficient_isUnit_iff, ← hint]
    have hcast : (((n : localCoefficientSubring m hm)) : ℂ) = (n : ℂ) := by push_cast; rfl
    rw [hcast]

end CFSG.BlockBasics
