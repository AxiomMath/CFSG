module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

theorem fg_card_le_two_of_dim_one (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 1) (B : Subgroup (OGroup R)) : Nat.card B ≤ 2 := by
  haveI : Finite (OGroup R) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  calc Nat.card B ≤ Nat.card (OGroup R) := Subgroup.card_le_card_group B
    _ = 2 := natCard_oGroup_one hR hdim

theorem fg_mul_self_of_two_plus (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = 1) (g : OGroup R) :
    g * g = 1 := by
  haveI : Finite (OGroup R) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  by_contra hgg
  have hcard : Nat.card (OGroup R) = 4 := natCard_oGroup_two_plus hR hdim hs
  have hnot2 : ¬ orderOf g ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hgg
  have hdvd4 : orderOf g ∣ 4 := by
    rw [← hcard]
    exact orderOf_dvd_natCard g
  have hord : orderOf g = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf g ∣ 2 ^ 2 from hdvd4) with ⟨j, hj, hjeq⟩
    have hne0 : j ≠ 0 := by
      rintro rfl
      exact hnot2 (by rw [hjeq]; norm_num)
    have hne1 : j ≠ 1 := by
      rintro rfl
      exact hnot2 (by rw [hjeq]; norm_num)
    have hj2 : j = 2 := by omega
    rw [hjeq, hj2]
    norm_num
  haveI : Finite (Subgroup.zpowers g) := Subtype.finite
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hmem : piOrth R ∈ Subgroup.zpowers g := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : g ^ (2 * k) = 1 := by
    calc g ^ (2 * k) = g ^ (k * 2) := by rw [mul_comm]
      _ = (g ^ k) ^ (2 : ℤ) := by rw [zpow_mul]
      _ = 1 := by rw [hk, zpow_two, piOrth_mul_self]
  have hdvd : (4 : ℤ) ∣ 2 * k := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := g) (i := 2 * k)).mpr h1
    rwa [hord] at h
  obtain ⟨m, hm⟩ := hdvd
  have hk_eq : k = 2 * m := by omega
  have hexists : ∃ p : OGroup R, p * p = piOrth R := by
    refine ⟨g ^ m, ?_⟩
    calc (g ^ m) * (g ^ m) = g ^ (m + m) := by rw [← zpow_add]
      _ = g ^ k := by congr 1; omega
      _ = piOrth R := hk
  have hsign := (exists_mul_self_eq_piOrth_iff hR).mp hexists
  have hm1 : quadSign R = -1 := by
    rw [hdim] at hsign
    simpa using hsign.2
  rw [hs] at hm1
  exact (by decide : (1 : ℤˣ) ≠ -1) hm1

theorem fg_subgroup_two_plus (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = 1) (B : Subgroup (OGroup R)) :
    Nat.card B ≤ 2 ∨
      Nonempty (↥B ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  haveI : Finite (OGroup R) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Nonempty ↥B := ⟨1⟩
  have hcard : Nat.card (OGroup R) = 4 := natCard_oGroup_two_plus hR hdim hs
  have hdvd : Nat.card B ∣ 4 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card B
  by_cases hB4 : Nat.card B = 4
  · right
    have hsq : ∀ b : ↥B, b * b = 1 := fun b =>
      Subtype.ext (by simpa using fg_mul_self_of_two_plus hR hdim hs (b : OGroup R))
    haveI : Nontrivial ↥B := by
      rw [← Finite.one_lt_card_iff_nontrivial, hB4]
      norm_num
    have hexp_dvd : Monoid.exponent ↥B ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun b => by simpa [pow_two] using hsq b)
    have hexp : Monoid.exponent ↥B = 2 := by
      have hgt : 1 < Monoid.exponent ↥B := Monoid.one_lt_exponent
      rcases (Nat.dvd_prime Nat.prime_two).mp hexp_dvd with h | h
      · omega
      · exact h
    haveI : IsKleinFour ↥B := ⟨hB4, hexp⟩
    haveI : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
      inferInstanceAs (IsKleinFour (Multiplicative (ZMod 2 × ZMod 2)))
    exact IsKleinFour.nonempty_mulEquiv
  · left
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card B ∣ 2 ^ 2 from hdvd) with ⟨j, hj, hjeq⟩
    have hne2 : j ≠ 2 := by
      rintro rfl
      exact hB4 (by rw [hjeq]; norm_num)
    have hjle : j ≤ 1 := by omega
    have hpow : 2 ^ j ≤ 2 := by
      calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hjle
        _ = 2 := by norm_num
    rw [hjeq]
    exact hpow

end CFSG.OddStandard.SmallF3.Omega
