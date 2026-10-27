module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open CFSG.Open

theorem charP_two_of_card {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (h : Nat.card F = 2 ^ f) : CharP F 2 := by
  letI := Fintype.ofFinite F
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  rcases FiniteField.card F (ringChar F) with ⟨n, _hn, hcard⟩
  have hcard' : Nat.card F = (ringChar F) ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have hdvd : ringChar F ∣ 2 ^ f := by
    rw [← h, hcard']
    exact dvd_pow_self _ n.ne_zero
  have hp2 : ringChar F = 2 := by
    have h2 : ringChar F ∣ 2 := hp.dvd_of_dvd_pow hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact ringChar.of_eq hp2

private lemma nilpotent_pow_card_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {N : Matrix ι ι F} (hN : IsNilpotent N) :
    N ^ Fintype.card ι = 0 := by
  have hchar : N.charpoly = Polynomial.X ^ Fintype.card ι := by
    have hnil : IsNilpotent (N.charpoly - Polynomial.X ^ Fintype.card ι) :=
      Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    exact sub_eq_zero.mp hnil.eq_zero
  have h := Matrix.aeval_self_charpoly N
  rw [hchar] at h
  simpa using h

theorem pow_four_eq_one_proj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] [CharP F 2] (hι : Fintype.card ι ≤ 4) (H : Subgroup (GL ι F))
    (y : StatedProj H) (hy : ∃ k : ℕ, y ^ 2 ^ k = 1) : y ^ 4 = 1 := by
  by_cases hne : Nonempty ι
  · obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hy
    have hk' : ((h ^ 2 ^ k : H) : StatedProj H) = 1 := by
      simpa using hk
    have hmem : (h ^ 2 ^ k : H) ∈ (StatedScalars ι F).subgroupOf H :=
      (QuotientGroup.eq_one_iff _).mp hk'
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    let A : GL ι F := h
    have hA : (A : Matrix ι ι F) ^ 2 ^ k = Matrix.scalar ι (c : F) := by
      have hc' := congrArg (fun g : GL ι F => (g : Matrix ι ι F)) hc
      simpa [A, Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] using hc'.symm
    haveI : PerfectRing F 2 := inferInstance
    obtain ⟨d, hd⟩ := (bijective_iterateFrobenius F 2 k).2 (c : F)
    have hd' : d ^ 2 ^ k = (c : F) := by
      simpa [iterateFrobenius_def] using hd
    let N : Matrix ι ι F := (A : Matrix ι ι F) - Matrix.scalar ι d
    have hcomm : Commute (A : Matrix ι ι F) (Matrix.scalar ι d) :=
      (Matrix.scalar_commute d (fun r' => Commute.all d r') (A : Matrix ι ι F)).symm
    have hNpow : N ^ 2 ^ k = 0 := by
      dsimp only [N]
      rw [sub_pow_char_pow_of_commute (p := 2) (n := k) hcomm]
      rw [hA, ← map_pow, hd', sub_self]
    have hNil : IsNilpotent N := ⟨2 ^ k, hNpow⟩
    have hNcard : N ^ Fintype.card ι = 0 := nilpotent_pow_card_eq_zero hNil
    have hN4 : N ^ 4 = 0 := by
      have h4 : 4 = (4 - Fintype.card ι) + Fintype.card ι :=
        (Nat.sub_add_cancel hι).symm
      rw [h4, pow_add, hNcard, mul_zero]
    have hA4 : (A : Matrix ι ι F) ^ 4 = Matrix.scalar ι (d ^ 4) := by
      have h := sub_pow_char_pow_of_commute (p := 2) (n := 2) hcomm
      norm_num at h
      have h' : N ^ 4 = (A : Matrix ι ι F) ^ 4 - (Matrix.scalar ι d) ^ 4 := by
        simpa only [N, Matrix.scalar_apply] using h
      rw [hN4, ← map_pow] at h'
      exact sub_eq_zero.mp h'.symm
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero k (by norm_num))] at hd'
      exact c.ne_zero hd'.symm
    let u : Fˣ := Units.mk0 (d ^ 4) (pow_ne_zero 4 hd0)
    have hA4u : A ^ 4 = Matrix.GeneralLinearGroup.scalar ι u := by
      ext i j
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar]
      simpa [u] using congrArg (fun M : Matrix ι ι F => M i j) hA4
    have hA4mem : A ^ 4 ∈ StatedScalars ι F := by
      rw [StatedScalars]
      exact MonoidHom.mem_range.mpr ⟨u, hA4u.symm⟩
    have hh4 : (h ^ 4 : H) ∈ (StatedScalars ι F).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      simpa [A] using hA4mem
    have hq : ((h ^ 4 : H) : StatedProj H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hh4
    simpa using hq
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    exact Subsingleton.elim _ _

theorem orderOf_ne_eight_proj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] [CharP F 2] (hι : Fintype.card ι ≤ 4) (H : Subgroup (GL ι F))
    (y : StatedProj H) : orderOf y ≠ 8 := by
  intro h
  have hy : y ^ 4 = 1 := by
    refine pow_four_eq_one_proj hι H y ⟨3, ?_⟩
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact pow_orderOf_eq_one y
  have h4 : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one hy
  rw [h] at h4
  norm_num at h4

end CFSG.EvenSporadicStandard.M12Std.SolomonK
