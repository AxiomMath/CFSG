module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.GroupTheory.WeirSylow

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ringChar_zmod3_ne_two' : ringChar (ZMod 3) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  norm_num

theorem natCard_oGroup_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) :
    Nat.card (OGroup Q) = 103680 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 3) (V := V)
    ringChar_zmod3_ne_two' (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (n := 2)
    (by rw [hdim])
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 ^ 2) *
      (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 103680 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_six_plus (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = 1) : Nat.card (OGroup Q) = 24261120 := by
  have hplus : IsPlusType Q :=
    (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by rw [hdim])).mpr hs
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (m := 2) (by rw [hdim]) (ε := 1)
    (Or.inl ⟨rfl, hplus⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 * (2 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (2 + 1) - 1) *
      (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 24261120 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_six_minus (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) : Nat.card (OGroup Q) = 26127360 := by
  have hnplus : ¬ IsPlusType Q := fun h => by
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by rw [hdim])).mp h
    rw [hs] at h1
    exact (by decide : (-1 : ℤˣ) ≠ 1) h1
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
    (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (m := 2) (by rw [hdim]) (ε := -1)
    (Or.inr ⟨rfl, hnplus⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 * (2 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (2 + 1) - (-1)) *
      (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 26127360 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7) :
    Nat.card (OGroup Q) = 18341406720 := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 3) (V := V)
    ringChar_zmod3_ne_two' (QuadraticMap.nondegenerate_polar_iff.mpr hQ) (n := 3)
    (by rw [hdim])
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (3 ^ 2) *
      (∏ i ∈ Finset.Icc 1 3, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 18341406720 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem piOrth_not_mem_omegaGroup_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) : piOrth Q ∉ omegaGroup hQ := by
  rw [piOrth_mem_omegaGroup_iff hQ, hdim]
  exact fun h => (by decide : ¬ Even (7 : ℕ)) h.1

theorem natCard_omegaGroup_seven (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) : Nat.card (omegaGroup hQ) = 4585351680 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hcard := Subgroup.card_mul_index (H := omegaGroup hQ)
  rw [index_omegaGroup hQ h2, natCard_oGroup_seven hQ hdim] at hcard
  omega

theorem natCard_omegaProj_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7) :
    Nat.card (omegaProj hQ) = 4585351680 := by
  have h := card_omegaProj_mul hQ (by rw [hdim]; norm_num)
  rw [if_neg (piOrth_not_mem_omegaGroup_seven hQ hdim), mul_one,
    natCard_omegaGroup_seven hQ hdim] at h
  exact h

theorem natCard_projOrth_seven (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7) :
    Nat.card (ProjOrth Q) = 9170703360 := by
  have h := Subgroup.card_mul_index (omegaProj hQ)
  rw [index_omegaProj_of_odd hQ (by rw [hdim]; norm_num) (by rw [hdim]; decide),
    natCard_omegaProj_seven hQ hdim] at h
  omega

end CFSG.OddStandard.SmallF3.Omega
