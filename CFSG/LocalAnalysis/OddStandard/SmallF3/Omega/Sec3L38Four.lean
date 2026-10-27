module

import CFSG.ClassicalInvolution.Balance.Basic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem odd_card_zmod3 : Odd (Nat.card (ZMod 3)) := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

private theorem card_zmod3_eq_three_pow_one : Nat.card (ZMod 3) = 3 ^ 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  norm_num

theorem no_totally_singular_plane_of_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    ¬ ∃ S : Submodule (ZMod 3) V, Module.finrank (ZMod 3) S = 2 ∧ ∀ x ∈ S, Q x = 0 := by
  rintro ⟨T, hTdim, hTQ⟩
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q := ⟨T, by omega, hTQ⟩
  have h1 : quadSign Q = 1 :=
    (isPlusType_iff_quadSign_eq_one hQ (d := 2) (by omega)).mp hplus
  have hc := congrArg (fun u : ℤˣ => (u : ℤ)) (show (-1 : ℤˣ) = 1 from by rw [← hs, h1])
  norm_num at hc

theorem isQuasisimple_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    CFSG.IsQuasisimple (omegaGroup hQ) := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived
      (K := ZMod 3) (W := V) odd_card_zmod3 Q hQ' hdim
      (no_totally_singular_plane_of_four_minus hQ hdim hs)
  rw [omegaGroup_eq_commutator hQ (by omega)]
  exact hq

theorem lieModel_quotient_center_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    LieModel (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) .PSL 2 3 2 := by
  have hQ' : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hq := isQuasisimple_omegaGroup_four_minus hQ hdim hs
  have hM : IsComponent (omegaGroup hQ) := ⟨hq, (omegaGroup_normal hQ).isSubnormal⟩
  exact (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_four
    (p := 3) (e := 1) (by norm_num) (by norm_num) le_rfl card_zmod3_eq_three_pow_one
    Q hQ' hdim (no_totally_singular_plane_of_four_minus hQ hdim hs) hM).2

theorem natCard_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    Nat.card (omegaGroup hQ) = 360 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hpolar : (QuadraticMap.polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hnplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := fun h => by
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 2) (by rw [hdim])).mp h
    rw [hs] at h1
    exact (by decide : (-1 : ℤˣ) ≠ 1) h1
  have hcard := Subgroup.card_mul_index (H := omegaGroup hQ)
  rw [index_omegaGroup hQ h2] at hcard
  have hOint : (Nat.card (OGroup Q) : ℤ) = 1440 := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
      hpolar (m := 1) (by rw [hdim]) (ε := -1) (Or.inr ⟨rfl, hnplus⟩)
    have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (1 * (1 + 1)) *
        ((Nat.card (ZMod 3) : ℤ) ^ (1 + 1) - (-1)) *
        (∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 1440 := by
      rw [Nat.card_zmod]
      decide +kernel
    exact h.trans hval
  have hO_nat : Nat.card (OGroup Q) = 1440 := by exact_mod_cast hOint
  rw [hO_nat] at hcard
  omega

theorem natCard_center_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    Nat.card (Subgroup.center (omegaGroup hQ)) = 1 := by
  have hquot : Nat.card (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) = 360 := by
    have h := CFSG.GH74.card_of_lieModel_PSL (G := omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ))
      (n := 2) (p := 3) (f := 2) (by norm_num)
      (lieModel_quotient_center_omegaGroup_four_minus hQ hdim hs)
    rw [show CFSG.Open.ordA (2 - 1) (3 ^ 2) = 360 by decide] at h
    exact h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (omegaGroup hQ))
  rw [natCard_omegaGroup_four_minus hQ hdim hs, hquot] at hcard
  have h1 : (1 : ℕ) = Nat.card (Subgroup.center (omegaGroup hQ)) :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 360 by norm_num)
      (by rw [mul_one]; exact hcard)
  exact h1.symm

theorem lieModel_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    LieModel (omegaGroup hQ) .PSL 2 3 2 := by
  have hZ : Subgroup.center (omegaGroup hQ) = ⊥ :=
    Subgroup.card_eq_one.mp (natCard_center_omegaGroup_four_minus hQ hdim hs)
  exact LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot) (lieModel_quotient_center_omegaGroup_four_minus hQ hdim hs)

theorem oddCore_omegaGroup_four_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4) (hs : quadSign Q = -1) :
    oddCore (omegaGroup hQ) = ⊥ := by
  have hq := isQuasisimple_omegaGroup_four_minus hQ hdim hs
  have h' : CFSG.Open.IsQuasisimple (omegaGroup hQ) := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hO : CFSG.oddCore (omegaGroup hQ) ≤ Subgroup.center (omegaGroup hQ) :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h'
  rw [Subgroup.card_eq_one.mp (natCard_center_omegaGroup_four_minus hQ hdim hs)] at hO
  exact le_bot_iff.mp hO

end CFSG.OddStandard.SmallF3.Omega
