module

public import Certificates.Data.Kernel.J4M4Card.Defs
public import Certificates.Data.J4M4Card.Native
public import CFSG.Certificates.Kernel.J4Q.VOrbBFS

public section

namespace CFSG.KS.J4M4Card

open CFSG.KC.J4Q CFSG.KD.J4M4Card CFSG.Sporadic.J4.Native

theorem getLL_eq : ∀ (l : List (List Nat)) (i : Nat), getLL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getLL_eq l i

theorem neN_spec {a b : Nat} (h : neN a b = true) : a ≠ b := by
  rintro rfl
  simp [neN, notB, Nat.beq_refl] at h

theorem eq_of_neN_false {a b : Nat} (h : neN a b = false) : a = b := by
  unfold neN notB at h
  cases hb : Nat.beq a b
  · rw [hb] at h
    exact absurd h (by decide)
  · exact Nat.eq_of_beq_eq_true hb

theorem row_wf {A : Array V2} (hA : WfA A) {i : Nat} (hi : i < 112) : (A[i]?.getD V2.zero).wf = true := by
  have hs : i < A.size := by rw [hA.1]; exact hi
  rw [Array.getElem?_eq_getElem hs, Option.getD_some]
  exact Array.all_eq_true.1 hA.2 i hs

theorem rowsDiffer_of_ne {A B : Array V2} (hA : WfA A) (hB : WfA B) (h : encR A ≠ encR B) :
    CFSG.Quasithin.J4M4Card.rowsDiffer A B = true := by
  by_contra hd
  apply h
  have he : eqRows A B = true := by
    unfold eqRows
    rw [hA.1, hB.1]
    simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range]
    intro i hi
    have hd' : CFSG.Sporadic.J4.QT.differs (A[i]?.getD V2.zero) (B[i]?.getD V2.zero) = false := by
      unfold CFSG.Quasithin.J4M4Card.rowsDiffer at hd
      simp only [List.any_eq_true, List.mem_range, not_exists, not_and, Bool.not_eq_true] at hd
      exact hd i hi
    rw [differs_eq (row_wf hA hi) (row_wf hB hi)] at hd'
    rw [CFSG.KC.J4Q.VOrbBFS.v2N_inj (eq_of_neN_false hd')]
    unfold V2.beq
    simp
  rw [eqRows_eq hA hB] at he
  exact Nat.eq_of_beq_eq_true he

theorem keK_spec {c rm one G Gi : Nat} {M Mi Us : List Nat} :
    ∀ (ws : List (List Int)) (ms : List Nat), keK c rm one G Gi M Mi Us ws ms = true →
      ∀ j < ws.length, Nat.beq (wordJ c rm one M Mi (ws.getD j []))
        (mulJ c rm (mulJ c rm Gi (etaK c rm one Us (ms.getD j 0))) G) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | w :: ws, [], h, _, _ => absurd h (by simp [keK])
  | w :: ws, m :: ms, h, j, hj => by
    have h' : andB (Nat.beq (wordJ c rm one M Mi w)
        (mulJ c rm (mulJ c rm Gi (etaK c rm one Us m)) G)) (keK c rm one G Gi M Mi Us ws ms) = true :=
      h
    have h1 : Nat.beq (wordJ c rm one M Mi w)
        (mulJ c rm (mulJ c rm Gi (etaK c rm one Us m)) G) = true ∧
        keK c rm one G Gi M Mi Us ws ms = true := by
      revert h'
      cases Nat.beq (wordJ c rm one M Mi w) (mulJ c rm (mulJ c rm Gi (etaK c rm one Us m)) G) <;>
        simp [andB]
    rcases j with _ | j
    · exact h1.1
    · exact keK_spec ws ms h1.2 j (by simp at hj; omega)

end CFSG.KS.J4M4Card

end
