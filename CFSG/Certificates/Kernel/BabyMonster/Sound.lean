module

public import CFSG.Certificates.Kernel.BabyMonster.StripLib
public import CFSG.Certificates.Kernel.BSeed.Sound

public section

namespace CFSG.KC.BM

open CFSG.KC.YModel CFSG.KC.BSeed CFSG.KC.BM.SL

theorem stripMat_mul_of_allStrips {Ws : List (List Nat)} {A C : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hA : wfMat A = true) (h : AllStrips Ws A C) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = stripMat C := by
  rw [allStrips_spec h, wfMat_eq] at *
  simp only [wfMat_eq] at hW
  exact stripMatG_foldl (by norm_num) hW (wf_bit hA).1

theorem stripMat_mul_eq_one {Ws : List (List Nat)} {A : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hA : wfMat A = true) (h : AllStrips Ws A idStrips) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) = 1 := by
  rw [stripMat_mul_of_allStrips hW hA h, stripMat_eq]
  exact stripMatG_id (by norm_num) idStrips_eq

theorem rowsMat_eq_stripMat {R : List (List Nat)} {S : List Nat} (h : AllBlocks R S 0)
    (hS : wfMat S = true) :
    rowsMat 4370 (fun i => lget (lgetL R (Nat.div i 64)) (Nat.mod i 64)) = stripMat S := by
  obtain ⟨hl, hb⟩ := allBlocks_spec h
  rw [wfMat_eq] at hS
  have hS69 := (wf_bit hS).1
  have hR : ∀ s < 69, (R.getD s []).length = rowsSn 4370 s ∧
      sob 279680 4370 (R.getD s []) 0 0 = S.getD s 0 := fun s hs => by
    have := blockOK_spec (hb s (by omega))
    rwa [Nat.zero_add] at this
  ext i j
  have := (rows_of_blocks (by norm_num) (by norm_num) hS hR i.isLt).2 j.val
  change bz ((lget (lgetL R (i.val / 64)) (i.val % 64)).testBit j.val) = stripMatG 4370 S i j
  rw [stripMatG_apply, lget_eq, lgetL_eq, this]

end CFSG.KC.BM

end
