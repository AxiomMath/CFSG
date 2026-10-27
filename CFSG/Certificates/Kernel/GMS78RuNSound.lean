module

public import Certificates.Data.Kernel.GMS78RuN
public import CFSG.Certificates.Kernel.GMS78RuGen
import CFSG.Certificates.Kernel.GMS78RuNGlue

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

theorem nTau_val {nbt ntw : List (List (Fin 8))} {nc nb : List Nat} {INV d : Nat}
    (hNBT : ∀ j < 8, ∀ i < 8, (Gen.nBT nbt j i).val = fget NBT (8 * j + i) 3)
    (hNC : ∀ k < 8, nc.getD k 0 = fget NCOLS k 8) (hNB : ∀ k < 8, nb.getD k 0 = fget NBAS k 8)
    (hI : invTabOK INV = true) (hgl : glK (fget DC d 9) = true)
    (hTW : rowAt ntw (glIdxK (fget DC d 9)) (TWD >>> (24 * d)) 8 = true) (m : Nat) :
    (Gen.nTau nbt ntw nc nb (NG.unV (fget DC d 9)) m).val =
      nTauK d (gamTab (fget DC d 9) (adK (fget DC d 9) (fget INV (fget DC d 9) 9))) m := by
  have hR : fget DC d 9 < 512 := NG.fget_lt DC d 9
  obtain ⟨-, -, -, hIdx⟩ := NG.glK_facts _ hgl hR
  simp only [Gen.nTau, Gen.nQuad, Gen.nCo, NG.fxor_val, NG.xs8_val, NG.fite_val]
  rw [NG.maskApply_eq_maskAppK hNC]
  change _ = (xs8K (maskAppK NCOLS m) fun j => fget TWD (8 * d + j) 3) ^^^
    (xs8K (maskAppK NCOLS m) fun j => xs8K (maskAppK NCOLS m) fun i =>
      fget (gamTab (fget DC d 9) (adK (fget DC d 9) (fget INV (fget DC d 9) 9))) (8 * i + j) 3)
  rw [NG.xs8K_eq, NG.xs8K_eq]
  congr 1
  · apply NG.selN_congr
    intro j hj
    have e24 : 24 * d = 8 * d * 3 := by omega
    rw [Gen.nTw, hIdx, NG.rowAt_getD hTW hj, e24, NG.fget_shift]
  · apply NG.selN_congr
    intro j hj
    rw [NG.xs8K_eq]
    apply NG.selN_congr
    intro i hi
    rw [NG.gamTab_fget _ _ hi hj]
    by_cases hij : i < j
    · rw [ite_eq_left hij, ite_eq_left hij]
      simp only [Gen.nGam, NG.fxor_val, NG.nBeta_val hNBT hNC, NG.linApply_val, NG.packV_unV hR, Gen.nB,
        hNB i hi, hNB j hj, NG.nAd_eq hI hgl hR]
    · rw [ite_eq_right hij, ite_eq_right hij]

public section

theorem nc_sound (qt : List (Fin 8)) (nbt ntw : List (List (Fin 8))) (sb nc nb : List Nat)
    (dct : List (Fin 8 × Fin 8 × Fin 8)) {QT INV : Nat} (hQ : bindQ qt QT = true)
    (hN : bindNC sb nbt nc nb dct ntw = true)
    (hD : CFSG.KC.Enum.allN 8 (fun d => glK (CFSG.KLie.CT.fget DC d 9)) = true)
    (hI : invTabOK INV = true) (h1 : kGamCol QT = true) (h2 : ∀ d < 8, kDPart QT INV d = true) :
    Gen.gamColCheck qt nbt sb = true ∧ Gen.dPartCheck qt nbt ntw sb nc nb dct = true := by
  obtain ⟨hSB, hNBT, hNC, hNB, hDC, hTW⟩ := NG.bindNC_facts hN
  refine ⟨?_, ?_⟩
  · simp only [Gen.gamColCheck, List.all_eq_true, List.mem_range, beq_iff_eq]
    intro j hj c hc
    have h := Nat.eq_of_beq_eq_true (NG.allN_of (NG.allN_of h1 hj) hc)
    apply Fin.ext
    rw [NG.xs8_val, NG.sMaskN_K hSB c (Nat.le_of_lt hj), hSB j hj,
      NG.bC_val hQ (NG.fget_lt SB j 8) (NG.sMaskNK_lt c j), ← h, NG.xs8K_eq]
    exact NG.selN_congr fun i hi => hNBT j hj i hi
  · simp only [Gen.dPartCheck, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
      Bool.and_eq_true, beq_iff_eq]
    intro d c hc
    have hd := d.isLt
    have hR : fget DC d.val 9 < 512 := NG.fget_lt DC d.val 9
    have hgl : glK (fget DC d.val 9) = true := NG.enum_allN8 hD hd
    have hr : Gen.dCode dct d = NG.unV (fget DC d.val 9) := by
      rw [← hDC d.val hd, NG.unV_packV]
      rfl
    have h := h2 d.val hd
    simp only [kDPart, NG.strictB_eq] at h
    obtain ⟨e1, e2⟩ := NG.andB_true (NG.allN_of h hc)
    obtain ⟨eK, hlt⟩ := NG.dPartK_eq hQ hSB d c
    have e1' := Nat.eq_of_beq_eq_true e1
    have e2' := Nat.eq_of_beq_eq_true e2
    rw [eK, NG.land_255 _ hlt] at e1'
    rw [eK, NG.shr_8 _ hlt] at e2'
    refine ⟨?_, ?_⟩
    · rw [Gen.sMask, Gen.sMask, NG.sMaskN_K hSB _ (Nat.le_refl 8), NG.sMaskN_K hSB _ (Nat.le_refl 8), e1',
        hr, NG.nAd_eq hI hgl hR]
    · apply Fin.ext
      rw [e2', hr, Gen.sMask, NG.sMaskN_K hSB _ (Nat.le_refl 8)]
      exact (nTau_val hNBT hNC hNB hI hgl (hTW d.val hd) _).symm

end

end CFSG.KC.GMS
