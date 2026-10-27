module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.GroupTheory.WeirSylow

section Orders

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

private theorem ringChar_zmod3_ne_two : ringChar (ZMod 3) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  norm_num

private theorem natCard_oGroup_odd_aux (hR : R.Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 3) W = 2 * n + 1) :
    (Nat.card (OGroup R) : ℤ) =
      2 * (Nat.card (ZMod 3) : ℤ) ^ (n ^ 2) *
        ∏ i ∈ Finset.Icc 1 n, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1) :=
  CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 3) (V := W)
    ringChar_zmod3_ne_two (QuadraticMap.nondegenerate_polar_iff.mpr hR) hdim

theorem natCard_oGroup_one (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 1) :
    Nat.card (OGroup R) = 2 := by
  have h := natCard_oGroup_odd_aux hR (n := 0) (by rw [hdim])
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (0 ^ 2) *
      (∏ i ∈ Finset.Icc 1 0, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 2 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_three (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 3) :
    Nat.card (OGroup R) = 48 := by
  have h := natCard_oGroup_odd_aux hR (n := 1) (by rw [hdim])
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (1 ^ 2) *
      (∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 48 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

private theorem natCard_oGroup_even_aux (hR : R.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank (ZMod 3) W = 2 * (m + 1)) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType R) ∨ (ε = -1 ∧ ¬ IsPlusType R)) :
    (Nat.card (OGroup R) : ℤ) =
      2 * (Nat.card (ZMod 3) : ℤ) ^ (m * (m + 1)) * ((Nat.card (ZMod 3) : ℤ) ^ (m + 1) - ε) *
        ∏ i ∈ Finset.Icc 1 m, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1) :=
  CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := W)
    (QuadraticMap.nondegenerate_polar_iff.mpr hR) hdim hε

private theorem isPlusType_of_sign (hR : R.Nondegenerate) {d : ℕ}
    (hdim : Module.finrank (ZMod 3) W = 2 * d) (hs : quadSign R = 1) : IsPlusType R :=
  (isPlusType_iff_quadSign_eq_one hR hdim).mpr hs

private theorem not_isPlusType_of_sign (hR : R.Nondegenerate) {d : ℕ}
    (hdim : Module.finrank (ZMod 3) W = 2 * d) (hs : quadSign R = -1) : ¬ IsPlusType R := by
  intro h
  have h1 := (isPlusType_iff_quadSign_eq_one hR hdim).mp h
  rw [hs] at h1
  exact (by decide : (-1 : ℤˣ) ≠ 1) h1

theorem natCard_oGroup_two_plus (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 2)
    (hs : quadSign R = 1) : Nat.card (OGroup R) = 4 := by
  have h := natCard_oGroup_even_aux hR (m := 0) (by rw [hdim]) (ε := 1)
    (Or.inl ⟨rfl, isPlusType_of_sign hR (d := 1) (by rw [hdim]) hs⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (0 * (0 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (0 + 1) - 1) *
      (∏ i ∈ Finset.Icc 1 0, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 4 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_two_minus (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 2)
    (hs : quadSign R = -1) : Nat.card (OGroup R) = 8 := by
  have h := natCard_oGroup_even_aux hR (m := 0) (by rw [hdim]) (ε := -1)
    (Or.inr ⟨rfl, not_isPlusType_of_sign hR (d := 1) (by rw [hdim]) hs⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (0 * (0 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (0 + 1) - (-1)) *
      (∏ i ∈ Finset.Icc 1 0, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 8 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_four_plus (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 4)
    (hs : quadSign R = 1) : Nat.card (OGroup R) = 1152 := by
  have h := natCard_oGroup_even_aux hR (m := 1) (by rw [hdim]) (ε := 1)
    (Or.inl ⟨rfl, isPlusType_of_sign hR (d := 2) (by rw [hdim]) hs⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (1 * (1 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (1 + 1) - 1) *
      (∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 1152 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

theorem natCard_oGroup_four_minus (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) W = 4)
    (hs : quadSign R = -1) : Nat.card (OGroup R) = 1440 := by
  have h := natCard_oGroup_even_aux hR (m := 1) (by rw [hdim]) (ε := -1)
    (Or.inr ⟨rfl, not_isPlusType_of_sign hR (d := 2) (by rw [hdim]) hs⟩)
  have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (1 * (1 + 1)) *
      ((Nat.card (ZMod 3) : ℤ) ^ (1 + 1) - (-1)) *
      (∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 1440 := by
    rw [Nat.card_zmod]
    decide +kernel
  exact_mod_cast h.trans hval

end Orders

section Centralizer

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem natCard_centralizer_involution (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    Nat.card (Subgroup.centralizer ({t} : Set (OGroup Q))) =
      Nat.card (OGroup (Q.restrict (fixSp t))) * Nat.card (OGroup (Q.restrict (commSp t))) := by
  rw [← range_blockHom hQ htt, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective (blockHom_injective htt)).toEquiv).symm

theorem natCard_map_toProj_mul (K : Subgroup (OGroup Q)) (hK : piOrth Q ∈ K)
    (h0 : 0 < Module.finrank (ZMod 3) V) :
    Nat.card (K.map (toProj Q)) * 2 = Nat.card K := by
  have hle : piGroup Q ≤ K := by
    intro g hg
    rcases mem_piGroup_iff.mp hg with rfl | rfl
    · exact K.one_mem
    · exact hK
  have h2 : Nat.card (piGroup Q ⊓ K : Subgroup (OGroup Q)) = 2 := by
    rw [inf_eq_left.mpr hle]
    exact card_piGroup (Q := Q) h0
  have h := Subgroup.relIndex_mul_card (H := (toProj Q).ker) (K := K)
  rw [Subgroup.relIndex_ker (f := toProj Q), QuotientGroup.ker_mk', h2] at h
  exact h

end Centralizer

end CFSG.OddStandard.SmallF3.Omega
