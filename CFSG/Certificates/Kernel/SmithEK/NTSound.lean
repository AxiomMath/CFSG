module

public import Certificates.Data.Kernel.SmithEKNT
public import CFSG.Certificates.Kernel.SmithEK.NSound

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

theorem ivFP_sound {FP n : Nat} {l : List Nat} (h : ivFP FP n l = true) :
    l.length = n ∧ ∀ k, at' 105 FP k = l.getD k 0 := by
  unfold ivFP at h
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hn, hFP⟩, hlt⟩ := h
  refine ⟨hn, fun k => ?_⟩
  have e : l.foldr (fun x acc => Nat.add x (Nat.mul (2 ^ 105) acc)) 0 =
      l.foldr (fun x acc => x + 2 ^ 105 * acc) 0 := rfl
  rw [hFP, e]
  exact at'_foldr 105 l hlt k

theorem ivLt_sound {FP n : Nat} (h : ivLt FP n = true) {v : Nat} (hv : v < n) {k : Nat}
    (hk : k < 21) : at' 5 (at' 105 FP v) k < 21 := by
  have h1 := (recAll_iff (fun v => Nat.rec (motive := fun _ => Bool) true (fun k acc' => acc' &&
    Nat.blt (at' 5 (at' 105 FP v) k) 21) 21) n).1 h v hv
  have h2 := (recAll_iff (fun k => Nat.blt (at' 5 (at' 105 FP v) k) 21) 21).1 h1 k hk
  exact Nat.le_of_ble_eq_true h2

theorem ivEdgeK_sound {FP : Nat} {SG SR : List (List Nat)} {g u v : Nat}
    (h : ivEdgeK FP SG SR g u v = true) {k : Nat} (hk : k < 21) :
    at' 5 (at' 105 FP v) k =
      (SG.getD g []).getD (at' 5 (at' 105 FP u) ((SR.getD g []).getD k 0)) 0 := by
  have := (recAll_iff (fun k => Nat.beq (at' 5 (at' 105 FP v) k)
    ((SG.getD g []).getD (at' 5 (at' 105 FP u) ((SR.getD g []).getD k 0)) 0)) 21).1 h k hk
  exact Nat.eq_of_beq_eq_true this

theorem eqLN_true {a b : List Nat} (h : CFSG.KC.Misc.eqLN a b = true) : a = b := by
  rw [CFSG.KS.PK.eqLN_eq] at h
  exact of_decide_eq_true h

end CFSG.SmithE.K
