module

public import Certificates.Data.Kernel.T75M23.L2K7D
public import CFSG.Certificates.Kernel.T75M23.L2K7Sound

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
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
    (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) (hok : n7kOk L = true) {b l : Nat}
    (hl : l < 16) {g y : N7} {P Y : Nat}
    (hP : ∀ x < 23, idx 23 (phiK h1 h2 g) x = fd 5 P x)
    (hY : ∀ x < 23, idx 23 (phiK h1 h2 y) x = fd 5 Y x)
    (h : conjAt (ak L b) (tk L l) P Y = true) :
    n7 (a7W b ++ tw7 l) * g = y * n7 (a7W b ++ tw7 l) := by
  refine phiK_injective hL h1 h2 hok (eq_of_idx fun x hx => ?_)
  have hx' := List.all_eq_true.1 h x (List.mem_range.2 hx)
  rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq, fdN_eq] at hx'
  have hgx : idx 23 (phiK h1 h2 g) x < 23 := idx_lt _ hx
  have hnx : idx 23 (phiK h1 h2 (n7 (a7W b ++ tw7 l))) x < 23 := idx_lt _ hx
  rw [map_mul, map_mul, idx_mul, idx_mul, idxK_elem hL b hl hgx, hP x hx, hY _ hnx,
    idxK_elem hL b hl hx]
  exact Nat.eq_of_beq_eq_true hx'

theorem a7W_zero : a7W 0 = [] := by decide +kernel

theorem inv_class_of (hL : LetterRd L) (h1 : n7InvCheck = true)
    (h2 : n7RelCheck = true) (hok : n7kOk L = true) {rs : List (List Nat)} (h : icK L rs = true) :
    ∀ x : N7, x * x = 1 → (∀ k < 16, x ≠ n7 (tw7 k)) → ∃ n : N7, n * n7 (bGen7 0) * n⁻¹ = x := by
  unfold icK at h
  rw [withL_eq, sB_eq] at h
  unfold icE at h
  refine n7K_forall hL h1 h2 hok _ fun a ha k hk => ?_
  intro hsq hT
  have hg := allW2_spec h a (by rw [a7Words_length]; exact ha)
  rw [Nat.zero_add, sB_eq, ← a7Words_getD ha] at hg
  have hg' := List.all_eq_true.1 hg k (List.mem_range.2 hk)
  rw [sB_eq] at hg'
  have hdef : wordK 23 5 idn L ((a7Words.getD a []).map a7Z) = ak L a := rfl
  rw [hdef] at hg'
  have ha0 : Nat.beq a 0 = false := by
    cases a with
    | zero => exact (hT k hk (by rw [a7W_zero, List.nil_append])).elim
    | succ a => rfl
  have hinv : invAt (ak L a) (tk L k) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    have hx' := List.mem_range.1 hx
    have e := congrArg (fun g => idx 23 (phiK h1 h2 g) x) hsq
    simp only [map_mul, idx_mul, map_one, idx_one] at e
    rw [idxK_elem hL a hk (idx_lt _ hx'), idxK_elem hL a hk hx'] at e
    rw [fdN_eq, fdN_eq, fdN_eq, fdN_eq, e]
    exact Nat.beq_refl _
  rw [ha0, hinv] at hg'
  simp only [Bool.false_or, Bool.not_true] at hg'
  unfold icOne at hg'
  have e := conj_of_conjAt hL h1 h2 hok (Nat.mod_lt _ (by norm_num))
    (g := n7 (bGen7 0)) (y := n7 (a7W a ++ tw7 k)) (fun x hx => idxK_pw hL _ hx)
    (fun x hx => by rw [idxK_elem hL a hk hx, fd_pc _ _ hx]) hg'
  refine ⟨n7 (a7W (((rs.drop a).headD []).getD k 0 / 16) ++
    tw7 (((rs.drop a).headD []).getD k 0 % 16)), ?_⟩
  rw [e]
  group

end CFSG.KC.N7K

end
