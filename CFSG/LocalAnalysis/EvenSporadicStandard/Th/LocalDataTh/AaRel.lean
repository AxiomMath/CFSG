module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Normalizer
public import Certificates.Certificate24204

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native
open scoped Matrix

set_option linter.unusedSectionVars false

section Elements


@[expose] noncomputable def gAa1 : J := nf 1 (codeVec 8 50) * wordProd wG1

@[expose] noncomputable def gAa2 : J := nf 0 (codeVec 8 45)

@[expose] noncomputable def gAa3 : J :=
  nf 1 (codeVec 8 243) * wordProd wG3 * nf 0 (codeVec 8 2)

@[expose] noncomputable def gAa4 : J :=
  nf 0 (codeVec 8 73) * wordProd wG4 * nf 0 (codeVec 8 10)

@[expose] noncomputable def bAa : J := nf 0 (codeVec 8 136)

theorem isRows_nfC1 (n : ℕ) : IsRows (rowsNfC 1 n) (nf 1 (codeVec 8 n)) := by
  have h : (fun i : Fin 8 => (codeVec 8 n i).val) = bitsOf n :=
    funext fun i => (bitsOf_eq n i).symm
  rw [nf_eq_nfN]
  show IsRows (rowsNf 1 (bitsOf n)) (nfN (1 : ZMod 2).val (fun i : Fin 8 => (codeVec 8 n i).val))
  rw [h]
  exact isRows_nfN 1 (bitsOf n)

theorem isRows_gAa1 : IsRows rowsG1 gAa1 :=
  (isRows_nfC1 50).mul (IsRows.word isRows_x isRows_y wG1)

theorem isRows_gAa2 : IsRows rowsG2 gAa2 := isRows_nf_zero 45

theorem isRows_gAa3 : IsRows rowsG3 gAa3 :=
  ((isRows_nfC1 243).mul (IsRows.word isRows_x isRows_y wG3)).mul (isRows_nf_zero 2)

theorem isRows_gAa4 : IsRows rowsG4 gAa4 :=
  ((isRows_nf_zero 73).mul (IsRows.word isRows_x isRows_y wG4)).mul (isRows_nf_zero 10)

theorem isRows_bAa : IsRows rowsBe bAa := isRows_nf_zero 136

structure AaRel : Prop where
  comm12 : gAa1 * gAa2 = gAa2 * gAa1
  comm13 : gAa1 * gAa3 = gAa3 * gAa1
  comm14 : gAa1 * gAa4 = gAa4 * gAa1
  comm23 : gAa2 * gAa3 = gAa3 * gAa2
  comm24 : gAa2 * gAa4 = gAa4 * gAa2
  comm34 : gAa3 * gAa4 = gAa4 * gAa3
  sq1 : gAa1 * gAa1 = cA (codeVec 4 2)
  sq2 : gAa2 * gAa2 = cA (codeVec 4 1)
  sq3 : gAa3 * gAa3 = cA (codeVec 4 5)
  sq4 : gAa4 * gAa4 = cA (codeVec 4 10)
  cen10 : gAa1 * aGen 0 = aGen 0 * gAa1
  cen11 : gAa1 * aGen 1 = aGen 1 * gAa1
  cen12 : gAa1 * aGen 2 = aGen 2 * gAa1
  cen13 : gAa1 * aGen 3 = aGen 3 * gAa1
  cen20 : gAa2 * aGen 0 = aGen 0 * gAa2
  cen21 : gAa2 * aGen 1 = aGen 1 * gAa2
  cen22 : gAa2 * aGen 2 = aGen 2 * gAa2
  cen23 : gAa2 * aGen 3 = aGen 3 * gAa2
  cen30 : gAa3 * aGen 0 = aGen 0 * gAa3
  cen31 : gAa3 * aGen 1 = aGen 1 * gAa3
  cen32 : gAa3 * aGen 2 = aGen 2 * gAa3
  cen33 : gAa3 * aGen 3 = aGen 3 * gAa3
  cen40 : gAa4 * aGen 0 = aGen 0 * gAa4
  cen41 : gAa4 * aGen 1 = aGen 1 * gAa4
  cen42 : gAa4 * aGen 2 = aGen 2 * gAa4
  cen43 : gAa4 * aGen 3 = aGen 3 * gAa4
  bcen0 : bAa * aGen 0 = aGen 0 * bAa
  bcen1 : bAa * aGen 1 = aGen 1 * bAa
  bcen2 : bAa * aGen 2 = aGen 2 * bAa
  bcen3 : bAa * aGen 3 = aGen 3 * bAa
  bsq : bAa * bAa = 1
  binv1 : bAa * gAa1 * bAa = gAa1 * (gAa1 * gAa1)
  binv2 : bAa * gAa2 * bAa = gAa2 * (gAa2 * gAa2)
  binv3 : bAa * gAa3 * bAa = gAa3 * (gAa3 * gAa3)
  binv4 : bAa * gAa4 * bAa = gAa4 * (gAa4 * gAa4)

theorem aaRel : AaRel := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ :=
    Certificates.certificate24204
  exact ⟨(isRows_gAa1.mul isRows_gAa2).eq_of_eqRows (isRows_gAa2.mul isRows_gAa1) h0,
    (isRows_gAa1.mul isRows_gAa3).eq_of_eqRows (isRows_gAa3.mul isRows_gAa1) h1,
    (isRows_gAa1.mul isRows_gAa4).eq_of_eqRows (isRows_gAa4.mul isRows_gAa1) h2,
    (isRows_gAa2.mul isRows_gAa3).eq_of_eqRows (isRows_gAa3.mul isRows_gAa2) h3,
    (isRows_gAa2.mul isRows_gAa4).eq_of_eqRows (isRows_gAa4.mul isRows_gAa2) h4,
    (isRows_gAa3.mul isRows_gAa4).eq_of_eqRows (isRows_gAa4.mul isRows_gAa3) h5,
    (isRows_gAa1.mul isRows_gAa1).eq_of_eqRows (isRows_cA 2) h6,
    (isRows_gAa2.mul isRows_gAa2).eq_of_eqRows (isRows_cA 1) h7,
    (isRows_gAa3.mul isRows_gAa3).eq_of_eqRows (isRows_cA 5) h8,
    (isRows_gAa4.mul isRows_gAa4).eq_of_eqRows (isRows_cA 10) h9,
    (isRows_gAa1.mul isRows_aGen_zero).eq_of_eqRows (isRows_aGen_zero.mul isRows_gAa1) h10,
    (isRows_gAa1.mul isRows_aGen_one).eq_of_eqRows (isRows_aGen_one.mul isRows_gAa1) h11,
    (isRows_gAa1.mul isRows_aGen_two).eq_of_eqRows (isRows_aGen_two.mul isRows_gAa1) h12,
    (isRows_gAa1.mul isRows_aGen_three).eq_of_eqRows (isRows_aGen_three.mul isRows_gAa1) h13,
    (isRows_gAa2.mul isRows_aGen_zero).eq_of_eqRows (isRows_aGen_zero.mul isRows_gAa2) h14,
    (isRows_gAa2.mul isRows_aGen_one).eq_of_eqRows (isRows_aGen_one.mul isRows_gAa2) h15,
    (isRows_gAa2.mul isRows_aGen_two).eq_of_eqRows (isRows_aGen_two.mul isRows_gAa2) h16,
    (isRows_gAa2.mul isRows_aGen_three).eq_of_eqRows (isRows_aGen_three.mul isRows_gAa2) h17,
    (isRows_gAa3.mul isRows_aGen_zero).eq_of_eqRows (isRows_aGen_zero.mul isRows_gAa3) h18,
    (isRows_gAa3.mul isRows_aGen_one).eq_of_eqRows (isRows_aGen_one.mul isRows_gAa3) h19,
    (isRows_gAa3.mul isRows_aGen_two).eq_of_eqRows (isRows_aGen_two.mul isRows_gAa3) h20,
    (isRows_gAa3.mul isRows_aGen_three).eq_of_eqRows (isRows_aGen_three.mul isRows_gAa3) h21,
    (isRows_gAa4.mul isRows_aGen_zero).eq_of_eqRows (isRows_aGen_zero.mul isRows_gAa4) h22,
    (isRows_gAa4.mul isRows_aGen_one).eq_of_eqRows (isRows_aGen_one.mul isRows_gAa4) h23,
    (isRows_gAa4.mul isRows_aGen_two).eq_of_eqRows (isRows_aGen_two.mul isRows_gAa4) h24,
    (isRows_gAa4.mul isRows_aGen_three).eq_of_eqRows (isRows_aGen_three.mul isRows_gAa4) h25,
    (isRows_bAa.mul isRows_aGen_zero).eq_of_eqRows (isRows_aGen_zero.mul isRows_bAa) h26,
    (isRows_bAa.mul isRows_aGen_one).eq_of_eqRows (isRows_aGen_one.mul isRows_bAa) h27,
    (isRows_bAa.mul isRows_aGen_two).eq_of_eqRows (isRows_aGen_two.mul isRows_bAa) h28,
    (isRows_bAa.mul isRows_aGen_three).eq_of_eqRows (isRows_aGen_three.mul isRows_bAa) h29,
    (isRows_bAa.mul isRows_bAa).eq_of_eqRows IsRows.one h30,
    ((isRows_bAa.mul isRows_gAa1).mul isRows_bAa).eq_of_eqRows
      (isRows_gAa1.mul (isRows_gAa1.mul isRows_gAa1)) h31,
    ((isRows_bAa.mul isRows_gAa2).mul isRows_bAa).eq_of_eqRows
      (isRows_gAa2.mul (isRows_gAa2.mul isRows_gAa2)) h32,
    ((isRows_bAa.mul isRows_gAa3).mul isRows_bAa).eq_of_eqRows
      (isRows_gAa3.mul (isRows_gAa3.mul isRows_gAa3)) h33,
    ((isRows_bAa.mul isRows_gAa4).mul isRows_bAa).eq_of_eqRows
      (isRows_gAa4.mul (isRows_gAa4.mul isRows_gAa4)) h34⟩

end Elements

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
