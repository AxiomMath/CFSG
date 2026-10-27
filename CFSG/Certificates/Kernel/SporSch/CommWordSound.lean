module

public import Certificates.Data.Kernel.SporSch.CommWord
public import Certificates.Data.CommProdM23
public import CFSG.Certificates.Kernel.SporSch.CodesImg

public section

namespace CFSG.KS.SporSch.CommWord

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CodesImg
open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu Certificates.CommProd

variable {n : ℕ}

theorem evalCodes_append (S : List (Equiv.Perm (Fin n))) (a b : List ℤ) :
    evalCodes S (a ++ b) = evalCodes S a * evalCodes S b := by
  induction a with
  | nil => simp [evalCodes]
  | cons z a ih => simp only [List.cons_append, evalCodes, ih, mul_assoc]

theorem evalCodes_single (S : List (Equiv.Perm (Fin n))) (z : ℤ) :
    evalCodes S [z] = if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹ := by
  simp [evalCodes]

theorem evalCodes_invW (S : List (Equiv.Perm (Fin n))) :
    ∀ w : List ℤ, (∀ z ∈ w, z ≠ 0) → evalCodes S (invW w) = (evalCodes S w)⁻¹
  | [], _ => by simp [invW, evalCodes]
  | z :: w, h => by
    have hz : z ≠ 0 := h z List.mem_cons_self
    have ih := evalCodes_invW S w fun y hy => h y (List.mem_cons_of_mem _ hy)
    have e : invW (z :: w) = invW w ++ [-z] := by simp [invW]
    rw [e, evalCodes_append, ih, evalCodes_single, evalCodes, mul_inv_rev]
    congr 1
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have h1 : 0 < -z := by omega
      have h2 : ¬ 0 < z := by omega
      simp only [h1, h2, if_true, if_false, inv_inv]
    · have h1 : ¬ 0 < -z := by omega
      simp only [h1, hgt, if_true, if_false, neg_neg]

theorem prodComm_eq (S : List (Equiv.Perm (Fin n))) :
    ∀ W : List (List ℤ × List ℤ), (∀ p ∈ W, (∀ z ∈ p.1, z ≠ 0) ∧ ∀ z ∈ p.2, z ≠ 0) →
      prodComm S W = evalCodes S (cpWord W)
  | [], _ => rfl
  | p :: r, h => by
    have hp := h p List.mem_cons_self
    have ih := prodComm_eq S r fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [prodComm, ih, cpWord, evalCodes_append, evalCodes_append, evalCodes_append,
      evalCodes_append, evalCodes_invW S _ hp.1, evalCodes_invW S _ hp.2, commVal]
    simp only [mul_assoc]

theorem imageList_inj' {g h : Equiv.Perm (Fin n)} (e : imageList g = imageList h) : g = h := by
  unfold imageList at e
  rw [List.ofFn_inj] at e
  exact Equiv.ext fun i => Fin.ext (congrFun e i)

variable {w : ℕ}

theorem commProdOK_of_img (hsz : szOK n w = true) {S : List (Equiv.Perm (Fin n))}
    {P Pi : ℕ → ℕ} (hg : ∀ j < S.length, imageList (S.getD j 1) = (unpack n w (P j)).toList)
    (hp : ∀ j < S.length, permOK n w (mask w) (n * w) (P j) (Pi j) = true)
    (hid : imageList (1 : Equiv.Perm (Fin n)) = (unpack n w (pidn n w)).toList)
    {W : List (List (List ℤ × List ℤ))} (hlen : W.length = S.length)
    (hnz : ∀ ws ∈ W, ∀ p ∈ ws, (∀ z ∈ p.1, z ≠ 0) ∧ ∀ z ∈ p.2, z ≠ 0)
    (hk : ∀ i < S.length, lettersK S.length (cpWord (W.getD i [])) = true ∧
      wordK n w (mask w) (pidn n w) P Pi (cpWord (W.getD i [])) = P i) :
    commProdOK S W = true := by
  unfold commProdOK
  simp only [hlen, beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  intro i hi
  have hW : ∀ p ∈ W.getD i [], (∀ z ∈ p.1, z ≠ 0) ∧ ∀ z ∈ p.2, z ≠ 0 := by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hi)]
    exact hnz _ (List.getElem_mem _)
  apply imageList_inj'
  rw [hg i hi, prodComm_eq S _ hW, evalCodes_img hsz hg hp hid (hk i hi).1, (hk i hi).2]

end CFSG.KS.SporSch.CommWord

end
