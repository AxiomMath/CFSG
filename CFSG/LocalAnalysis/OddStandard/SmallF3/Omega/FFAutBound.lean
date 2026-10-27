module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Out

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_natCard_mulAut_le (T : Type) [Group T] [Finite T] :
    Nat.card (MulAut T) ≤ Nat.card T * Nat.card (Outer T) := by
  have h1 : Nat.card (MulAut T) = Nat.card (Outer T) * Nat.card (inner T) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (inner T)
  have h2 : Nat.card (inner T) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective (MulAut.conj : T →* MulAut T).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  rw [h1, mul_comm (Nat.card T)]
  exact Nat.mul_le_mul_left _ h2

theorem ff_ringChar_ne_two_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    ringChar K ≠ 2 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h3 : (3 : K) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, hK] at h
    exact_mod_cast h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have h1 : (1 : K) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem ff_ringAut_eq_one_of_card_three {K : Type} [Field K] (hK : Nat.card K = 3)
    (σ : K ≃+* K) : σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 3) (n := 1) (by norm_num) le_rfl (by rw [hK, pow_one])
  have : Subsingleton (K ≃+* K) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact Subsingleton.elim σ 1

theorem ff_card_outer_le_two_of_lieModel_psp {T : Type} [Group T] [Finite T]
    (h : LieModel T .PSp 2 3 1) : Nat.card (Outer T) ≤ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  have hdvd := CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45.card_outer_dvd_two
    (ff_ringChar_ne_two_of_card_three hK3) (ff_ringAut_eq_one_of_card_three hK3)
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem ff_lieModel_omegaProj_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hs : quadSign Q = 1) :
    LieModel (omegaProj hQ) .PSp 2 3 1 :=
  isOmegaStar_five_iff.mp
    ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, hdim, hs, ⟨MulEquiv.refl _⟩⟩

theorem ff_lieModel_omegaProj_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    LieModel (omegaProj hQ) .PSL 4 3 1 :=
  isOmegaStar_six_plus_iff.mp
    ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, hdim, hs, ⟨MulEquiv.refl _⟩⟩

theorem ff_lieModel_omegaProj_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    LieModel (omegaProj hQ) .PSU 4 3 1 :=
  isOmegaStar_six_minus_iff.mp
    ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, hdim, hs, ⟨MulEquiv.refl _⟩⟩

theorem ff_natCard_mulAut_omegaProj_five_le (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hs : quadSign Q = 1) :
    Nat.card (MulAut (omegaProj hQ)) ≤ 51840 := by
  have h1 := ff_natCard_mulAut_le (omegaProj hQ)
  have h2 := ff_card_outer_le_two_of_lieModel_psp (ff_lieModel_omegaProj_five hQ hdim hs)
  rw [natCard_omegaProj_five hQ hdim] at h1
  exact h1.trans (by simpa using Nat.mul_le_mul_left 25920 h2)

theorem ff_natCard_mulAut_omegaProj_six_plus_le (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card (MulAut (omegaProj hQ)) ≤ 24261120 := by
  have h1 := ff_natCard_mulAut_le (omegaProj hQ)
  have h2 := Nat.le_of_dvd (by norm_num)
    (aor_card_outer_dvd_of_psl_four (ff_lieModel_omegaProj_six_plus hQ hdim hs))
  rw [ff_natCard_omegaProj_six_plus hQ hdim hs] at h1
  exact h1.trans (by simpa using Nat.mul_le_mul_left 6065280 h2)

theorem ff_natCard_mulAut_omegaProj_six_minus_le (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card (MulAut (omegaProj hQ)) ≤ 26127360 := by
  have h1 := ff_natCard_mulAut_le (omegaProj hQ)
  have h2 := Nat.le_of_dvd (by norm_num)
    (aor_card_outer_dvd_of_psu_four (ff_lieModel_omegaProj_six_minus hQ hdim hs))
  rw [ff_natCard_omegaProj_six_minus hQ hdim hs] at h1
  exact h1.trans (by simpa using Nat.mul_le_mul_left 3265920 h2)

end CFSG.OddStandard.SmallF3.Omega
