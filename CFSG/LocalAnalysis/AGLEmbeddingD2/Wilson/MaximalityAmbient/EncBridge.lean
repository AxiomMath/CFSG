module

public import CFSG.Sporadic.J4.F2Spec
public import Certificates.Data.J4M2.Orbit
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.EncBridge

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.J4M2

theorem natToV2_toNat (n : Nat) : (natToV2 n).toNat = n % 2 ^ 128 := by
  unfold natToV2 V2.toNat
  simp only [UInt64.toNat_ofNat']
  have h : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [h, Nat.mod_mul, Nat.mod_mod]

theorem testBit_natToV2 (n : Nat) {j : Nat} (hj : j < 128) :
    (natToV2 n).testBit j = n.testBit j := by
  rw [← V2.testBit_toNat _ hj, natToV2_toNat, Nat.testBit_mod_two_pow]
  simp [hj]

theorem toVec_natToV2 (n : Nat) :
    (natToV2 n).toVec = CFSG.Sporadic.SmallF2.toVecD 112 n := by
  funext j
  rw [V2.toVec_apply, CFSG.Sporadic.SmallF2.toVecD_apply, testBit_natToV2 n (by omega)]

theorem rowsMatrix_map_natToV2 (R : Array Nat) :
    rowsMatrix (R.map natToV2) = CFSG.Sporadic.SmallF2.rowsMatrix 112 R := by
  ext i j
  rw [rowsMatrix_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply]
  rw [Array.getElem?_map]
  cases h : R[i.val]? with
  | none => simp [V2.toVec_apply, CFSG.Sporadic.SmallF2.toVecD_apply, V2.zero_testBit]
  | some n => simp [toVec_natToV2]

theorem toVecD_toNat (a : V2) : CFSG.Sporadic.SmallF2.toVecD 112 a.toNat = a.toVec := by
  funext j
  rw [V2.toVec_apply, CFSG.Sporadic.SmallF2.toVecD_apply, V2.testBit_toNat _ (by omega)]

theorem rowsMatrix_map_toNat (R : Array V2) :
    CFSG.Sporadic.SmallF2.rowsMatrix 112 (R.map V2.toNat) = rowsMatrix R := by
  ext i j
  rw [rowsMatrix_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply]
  rw [Array.getElem?_map]
  cases h : R[i.val]? with
  | none => simp [V2.toVec_apply, CFSG.Sporadic.SmallF2.toVecD_apply, V2.zero_testBit]
  | some a => simp [toVecD_toNat]

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.EncBridge
