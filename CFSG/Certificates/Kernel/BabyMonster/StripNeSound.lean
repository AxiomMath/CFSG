module

public import CFSG.Certificates.Kernel.BabyMonster.WfProd

public section

namespace CFSG.KC.BM

open CFSG.KC.BM.SL

theorem allStrips_map (Ws : List (List Nat)) : ∀ A : List Nat, AllStrips Ws A (A.map (mulW Ws))
  | [] => AllStrips.nil
  | a :: as => AllStrips.cons a _ as _ (Nat.beq_refl _) (allStrips_map Ws as)

theorem stripMat_mul_ne_of_strip {Ws Ds : List (List Nat)} {A C : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hD : ∀ D ∈ Ds, wfMat D = true) (hA : wfMat A = true)
    (hC : wfMat C = true) {j : Nat} (hj : j < 69)
    (h : notB (Nat.beq (mulW Ws (A.getD j 0)) (mulW Ds (C.getD j 0))) = true) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) ≠ (Ds.map stripMat).foldl (· * ·) (stripMat C) := by
  intro e
  have hP := allStrips_map Ws A
  have hQ := allStrips_map Ds C
  rw [stripMat_mul_of_allStrips hW hA hP, stripMat_mul_of_allStrips hD hC hQ] at e
  have wP := wfMat_of_allStrips hA hP
  have wQ := wfMat_of_allStrips hC hQ
  rw [wfMat_eq] at wP wQ hA hC
  rw [stripMat_eq, stripMat_eq] at e
  have hPQ := stripMatG_inj (stripShape_of_wf wP) (stripShape_of_wf wQ) e
  have ej := congrArg (fun L : List Nat => L.getD j 0) hPQ
  rw [getD_map_of_lt (by rw [(wf_bit hA).1]; exact hj),
    getD_map_of_lt (by rw [(wf_bit hC).1]; exact hj)] at ej
  rw [ej, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem stripMat_ne_one_of_strip {A : List Nat} (hA : wfMat A = true) {j : Nat} (hj : j < 69)
    (h : notB (Nat.beq (A.getD j 0) (idS j)) = true) : stripMat A ≠ 1 := by
  intro e
  have e2 : idStrips.getD j 0 = idS j := by
    rw [idStrips_eq, getD_map_of_lt (by simpa using hj), List.getD_eq_getElem?_getD,
      List.getElem?_range hj]
    rfl
  rw [← e2] at h
  have hid := stripMatG_id (n := 4370) (by norm_num) idStrips_eq
  rw [stripMat_eq, ← hid] at e
  rw [wfMat_eq] at hA
  have hI : StripShape 4370 idStrips := by
    rw [idStrips_eq]
    exact stripShape_id 4370
  have hAI := stripMatG_inj (stripShape_of_wf hA) hI e
  rw [hAI, Nat.beq_refl] at h
  exact absurd h (by decide)

end CFSG.KC.BM

end
