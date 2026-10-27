module

public import Certificates.Data.Kernel.T75JM.L2KD
public import CFSG.Certificates.Kernel.T75JM.L2KSound

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint CFSG.CosetTable

variable {L : Int → Nat}

theorem allW2_spec {g : Nat → List Nat → List Nat → Bool} :
    ∀ {ws rs : List (List Nat)} {i : Nat}, allW2 ws g rs i = true →
      ∀ j (hj : j < ws.length), g (i + j) ws[j] ((rs.drop j).headD []) = true
  | [], _, _, _, j, hj => absurd hj (by simp)
  | u :: ws, rs, i, h, j, hj => by
    have e : allW2 (u :: ws) g rs i = (g i u (rs.headD []) && allW2 ws g rs.tail (Nat.succ i)) :=
      rfl
    rw [e, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := allW2_spec h.2 j (by simpa using hj)
      rw [List.drop_tail] at this
      rw [show i + (j + 1) = Nat.succ i + j by omega]
      simpa using this

theorem conj_of_conjAt (hL : LetterRd L)
    (h1 : n0InvCheck = true) (hok : n0kOk L = true) {b l : Nat} (hl : l < 16) {g y : N0}
    {P Y : Nat}
    (hP : ∀ x < 22, idx 22 (phiK h1 (n0RelCheck_of hL (n0kOk_parts hok).1) g) x = fd 5 P x)
    (hY : ∀ x < 22, idx 22 (phiK h1 (n0RelCheck_of hL (n0kOk_parts hok).1) y) x = fd 5 Y x)
    (h : conjAt (ak L b) (tk L l) P Y = true) :
    n0 (a6W b ++ tw l) * g = y * n0 (a6W b ++ tw l) := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  refine phiK_injective (h2 := h2) hL h1 hok (eq_of_idx fun x hx => ?_)
  have hx' := List.all_eq_true.1 h x (List.mem_range.2 hx)
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq] at hx'
  have hgx : idx 22 (phiK h1 h2 g) x < 22 := idx_lt _ hx
  have hnx : idx 22 (phiK h1 h2 (n0 (a6W b ++ tw l))) x < 22 := idx_lt _ hx
  rw [map_mul, map_mul, idx_mul, idx_mul, idx_elem hL b hl hgx, hP x hx, hY _ hnx,
    idx_elem hL b hl hx]
  exact Nat.eq_of_beq_eq_true hx'

theorem a6W_zero : a6W 0 = [] := rfl

theorem inv_class_of (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) {rs : List (List Nat)} (h : icK L rs = true) :
    ∀ x : N0, x * x = 1 → (∀ k < 16, x ≠ n0 (tw k)) → ∃ n : N0, n * n0 (bGen 0) * n⁻¹ = x := by
  have h2 := n0RelCheck_of hL (n0kOk_parts hok).1
  unfold icK at h
  rw [withL_eq, sB_eq] at h
  unfold icE at h
  refine n0K_forall hL h1 hok _ fun a ha k hk => ?_
  intro hsq hT
  have hg := allW2_spec h a (by rw [a6Words_length]; exact ha)
  rw [Nat.zero_add, sB_eq, ← a6Words_getD ha] at hg
  have hg' := List.all_eq_true.1 hg k (List.mem_range.2 hk)
  rw [sB_eq] at hg'
  have hdef : wordK 22 5 idn L ((a6Words.getD a []).map a6Z) = ak L a := rfl
  rw [hdef] at hg'
  have ha0 : Nat.beq a 0 = false := by
    cases a with
    | zero => exact (hT k hk (by rw [a6W_zero, List.nil_append])).elim
    | succ a => rfl
  have hinv : invAt (ak L a) (tk L k) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.mem_range.1 hx
    have e := congrArg (fun g => idx 22 (phiK h1 h2 g) x) hsq
    simp only [map_mul, idx_mul, map_one, idx_one] at e
    rw [idx_elem hL a hk (idx_lt _ hx'), idx_elem hL a hk hx'] at e
    rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, e]
    exact Nat.beq_refl _
  rw [ha0, hinv] at hg'
  simp only [Bool.false_or, Bool.not_true] at hg'
  unfold icOne at hg'
  have e := conj_of_conjAt hL h1 hok (Nat.mod_lt _ (by norm_num))
    (g := n0 (bGen 0)) (y := n0 (a6W a ++ tw k)) (fun x hx => idx_pw hL _ hx)
    (fun x hx => by rw [idx_elem hL a hk hx, fd_pc _ _ hx]) hg'
  refine ⟨n0 (a6W (((rs.drop a).headD []).getD k 0 / 16) ++
    tw (((rs.drop a).headD []).getD k 0 % 16)), ?_⟩
  rw [e]
  group

end CFSG.KC.N0K

end
