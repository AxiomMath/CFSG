module

public import CFSG.GH74.KGroups.L3EpsSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem card_specialLinear_three {F : Type} [Field F] [Finite F] :
    Nat.card SL(3, F) = Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_three, Nat.card_eq_fintype_card (α := F)]
  generalize Fintype.card F = q at hq ⊢
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : q ≤ q ^ 3 := by nlinarith [pow_pos (show 0 < q by omega) 2]
  have h4 : q ^ 2 ≤ q ^ 3 := by nlinarith [pow_pos (show 0 < q by omega) 2]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  zify [h1, h2, h3, h4, show 1 ≤ q by omega]
  ring

theorem odd_card_of_pow_three {G : Type*} [Group G] [Finite G] (h : ∀ x : G, x ^ 3 = 1) :
    Odd (Nat.card G) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h3 := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at h3
  omega

theorem factorization_two_card_sl3 {q : ℕ} (hq : q % 2 = 1) (hq2 : 2 ≤ q) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)).factorization 2 =
      (q ^ 2 - 1).factorization 2 + (q - 1).factorization 2 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q := by omega
  have hq3 : ¬ 2 ∣ q ^ 3 := by
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hz3 : (q ^ 3).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hq3
  have hq21 : q ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hq31 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [Nat.one_le_pow 3 q (by omega), h2]
    ring
  have hq1 : q - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ (q ^ 2 + q + 1) := by
    intro h
    have : (q ^ 2 + q + 1) % 2 = 1 := by
      rcases Nat.odd_iff.2 hq with ⟨k, rfl⟩
      ring_nf
      omega
    omega
  have hz : (q ^ 2 + q + 1).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hodd
  have hne3 : q ^ 3 ≠ 0 := by positivity
  have hne31 : q ^ 3 - 1 ≠ 0 := by
    have : 8 ≤ q ^ 3 := by nlinarith [Nat.pow_le_pow_left hq2 3]
    omega
  rw [Nat.factorization_mul (mul_ne_zero hne3 hq21) hne31, Nat.factorization_mul hne3 hq21]
  simp only [Finsupp.add_apply]
  rw [hz3, hq31, Nat.factorization_mul hq1 (by omega)]
  simp only [Finsupp.add_apply]
  rw [hz]
  ring

theorem factorization_two_card_projectiveSL {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 2 = 1) :
    (Nat.card (projectiveSL 3 F)).factorization 2 =
      (Nat.card F ^ 2 - 1).factorization 2 + (Nat.card F - 1).factorization 2 := by
  have hq2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hodd : Odd (Nat.card (scalars 3 F)) :=
    odd_card_of_pow_three (fun x => by
      have := scalars_pow_three (K := F) x.2
      exact Subtype.ext (by simpa using this))
  have hmul : Nat.card SL(3, F) = Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 F)
  have hz : (Nat.card (scalars 3 F)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2))
  have hN0 : Nat.card (projectiveSL 3 F) ≠ 0 := Nat.card_pos.ne'
  have hZ0 : Nat.card (scalars 3 F) ≠ 0 := Nat.card_pos.ne'
  have h1 := congrArg (fun n => n.factorization 2) hmul
  simp only [Nat.factorization_mul hN0 hZ0, Finsupp.add_apply, hz, add_zero] at h1
  rw [← h1, card_specialLinear_three]
  exact factorization_two_card_sl3 hF hq2


section General

variable {X : Type*} [Group X] [Finite X]

theorem card_of_isMaxPGroup {S : Subgroup X} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S) :
    Nat.card S = ordProj[2] (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS.exists_le_sylow
  have hSP : S = P.toSubgroup := le_antisymm hP (hmax P.toSubgroup P.isPGroup' hP)
  rw [hSP]
  exact P.card_eq_multiplicity

theorem isMax_of_card {S : Subgroup X} (hcard : Nat.card S = ordProj[2] (Nat.card X)) :
    ∀ T : Subgroup X, IsPGroup 2 T → S ≤ T → T ≤ S := by
  intro T hT hST
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  have hPc : Nat.card P = ordProj[2] (Nat.card X) := P.card_eq_multiplicity
  have heq : S = P.toSubgroup := by
    apply Subgroup.eq_of_le_of_card_ge (hST.trans hP)
    rw [hPc, hcard]
  rw [heq] at hST ⊢
  exact hP

theorem card_dvd_ordProj {S : Subgroup X} (hS : IsPGroup 2 S) :
    Nat.card S ∣ ordProj[2] (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS.exists_le_sylow
  rw [← P.card_eq_multiplicity]
  exact Subgroup.card_dvd_of_le hP

end General

section Inner

variable {X : Type*} [Group X] [Finite X]

theorem card_le_of_inner (A : Subgroup (MulAut X)) (hA : IsPGroup 2 A) (P : Subgroup X)
    (hAP : A ⊓ inner X ≤ P.map (MulAut.conj : X →* MulAut X)) :
    Nat.card A ≤ Nat.card P * ordProj[2] (Nat.card (Outer X)) := by
  classical
  let ψ : A →* Outer X := (QuotientGroup.mk' (inner X)).comp A.subtype
  have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card A := Subgroup.card_mul_index ψ.ker
  have h2 : ψ.ker.index = Nat.card ψ.range := Subgroup.index_ker ψ
  have hker : Nat.card ψ.ker ≤ Nat.card P := by
    have hle : ψ.ker.map A.subtype ≤ P.map (MulAut.conj : X →* MulAut X) := by
      rintro _ ⟨k, hk, rfl⟩
      refine hAP ⟨k.2, ?_⟩
      have hk' : ψ k = 1 := hk
      exact (QuotientGroup.eq_one_iff _).1 hk'
    calc Nat.card ψ.ker = Nat.card (ψ.ker.map A.subtype) :=
          (Subgroup.card_map_of_injective A.subtype_injective).symm
      _ ≤ Nat.card ↥(P.map (MulAut.conj : X →* MulAut X)) := Subgroup.card_le_of_le hle
      _ ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have hrange : IsPGroup 2 ψ.range := IsPGroup.of_surjective hA ψ.rangeRestrict ψ.rangeRestrict_surjective
  have h3 : Nat.card ψ.range ≤ ordProj[2] (Nat.card (Outer X)) :=
    Nat.le_of_dvd (Nat.ordProj_pos _ _) (card_dvd_ordProj hrange)
  rw [← h1, h2]
  exact Nat.mul_le_mul hker h3

end Inner

section Models

variable {X : Type} [Group X] {p f : ℕ}

theorem odd_of_pow_mod_four_eq_three (hp : Odd p) (h : p ^ f % 4 = 3) : Odd f := by
  by_contra hf
  obtain ⟨k, rfl⟩ := Nat.not_odd_iff_even.1 hf
  have hpk : Odd (p ^ k) := hp.pow
  obtain ⟨m, hm⟩ := hpk
  have : p ^ (k + k) = (2 * m + 1) ^ 2 := by rw [← hm, ← two_mul, pow_mul']
  rw [this] at h
  have h2 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
  omega

theorem projectiveSL_card_two_part {F : Type} [Field F] [Finite F] (hF : Nat.card F % 2 = 1) :
    ordProj[2] (Nat.card (projectiveSL 3 F)) =
      ordProj[2] (Nat.card F - 1) ^ 2 * ordProj[2] (Nat.card F + 1) := by
  have hq2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have h := factorization_two_card_projectiveSL hF
  have hsq : (Nat.card F ^ 2 - 1).factorization 2 =
      (Nat.card F - 1).factorization 2 + (Nat.card F + 1).factorization 2 := by
    have h1 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      have h3 : 1 ≤ Nat.card F := by omega
      zify [h3, Nat.one_le_pow 2 (Nat.card F) (by omega)]
      ring
    rw [h1, Nat.factorization_mul (by omega) (by omega)]
    rfl
  rw [hsq] at h
  show 2 ^ (Nat.card (projectiveSL 3 F)).factorization 2 = (2 ^ (Nat.card F - 1).factorization 2) ^ 2 *
    2 ^ (Nat.card F + 1).factorization 2
  rw [h, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem lin_model_card (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSL 3 p f) :
    Finite X ∧ ordProj[2] (Nat.card X) = ordProj[2] (p ^ f - 1) ^ 2 * ordProj[2] (p ^ f + 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hp : p.Prime := hX.1.1
  have hq : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  have hF2 : Nat.card F % 2 = 1 := by rw [hF]; exact hq
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, projectiveSL_card_two_part hF2, hF]

theorem lin_outer_dvd (hX : StatedClassicalModel X .PSL 3 p f) :
    Nat.card (Outer X) ∣ 2 * f * Nat.gcd 3 (p ^ f - 1) :=
  (linear_model_outer_two_part_bound X 3 p f hX).2.2.2.2 (by norm_num)

theorem lin_outer_two_le (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSL 3 p f)
    (h3 : p ^ f % 4 = 3) : ordProj[2] (Nat.card (Outer X)) ≤ 2 := by
  have hp : p.Prime := hX.1.1
  have hf : Odd f := odd_of_pow_mod_four_eq_three (hp.odd_of_ne_two hp2) h3
  have hf0 : f ≠ 0 := by rintro rfl; exact absurd hf (by decide)
  have hg : Odd (Nat.gcd 3 (p ^ f - 1)) := Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  have hg0 : Nat.gcd 3 (p ^ f - 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  have hne : 2 * f * Nat.gcd 3 (p ^ f - 1) ≠ 0 := by positivity
  refine (ordProj_two_le_of_dvd hne (lin_outer_dvd hX)).trans (le_of_eq ?_)
  rw [Nat.ordProj_mul 2 (by positivity) hg0, Nat.ordProj_mul 2 two_ne_zero hf0,
    ordProj_two_eq_one_of_odd hf, ordProj_two_eq_one_of_odd hg, Nat.Prime.factorization_self Nat.prime_two]
  simp

end Models

end CFSG.GH74.KGroups.L3Eps
