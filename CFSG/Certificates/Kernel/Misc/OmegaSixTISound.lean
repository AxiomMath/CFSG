module

public import Certificates.Data.Kernel.Misc.OmegaSixTI
public import CFSG.Certificates.Kernel.Misc.OmegaSixASound
public import CFSG.Certificates.Kernel.MathieuAut.InAutKSound
public import Certificates.Data.Foote82InvolAutA6

public section

namespace CFSG.KC.OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux
  CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix CFSG.KD.YamakiRep
  CFSG.KD.YamakiRepF CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiRepF CFSG.KC.Loop
  CFSG.CGT.Foote82.InvolA6
open CFSG.KD.Sp62 (MULF ONE)

theorem sub0 (X : ℕ) : subOneCode (arrF X) 0 = 0 := by
  have h := subOne_xor X (p := 0) (q := 0) (by norm_num) (by norm_num)
  simp only [Nat.xor_self] at h
  exact h

theorem decomp : ∀ w < 64, ∀ n < 6, w % 2 ^ (n + 1) = w % 2 ^ n ^^^ bitK w n * 2 ^ n := by
  decide +kernel

theorem sKn_succ (X w n : ℕ) : sKn X w (n + 1) = sKn X w n ^^^ bitK w n * subK X n := rfl

theorem bit_le (w n : ℕ) : bitK w n ≤ 1 := Nat.and_le_right

theorem sK_eq (X : ℕ) {w : ℕ} (hw : w < 64) : subOneCode (arrF X) w = sK X w := by
  have key : ∀ n ≤ 6, subOneCode (arrF X) (w % 2 ^ n) = sKn X w n := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [pow_zero, Nat.mod_one]
      exact sub0 X
    | succ n ih =>
      intro hn
      have hn' : n < 6 := by omega
      have hp : 2 ^ n < 64 :=
        calc 2 ^ n < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hn'
          _ = 64 := by norm_num
      have hm : w % 2 ^ n < 64 := lt_of_le_of_lt (Nat.mod_le _ _) hw
      rw [decomp w hw n hn', sKn_succ, ← ih (by omega)]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (bit_le w n) with h | h
      · rw [h, Nat.zero_mul, Nat.zero_mul, Nat.xor_zero, Nat.xor_zero]
      · rw [h, Nat.one_mul, Nat.one_mul, subOne_xor X hm hp, subOne_eq X n hn']
  have h6 := key 6 le_rfl
  rwa [Nat.mod_eq_of_lt (by norm_num; exact hw)] at h6

theorem arrF_size (X : ℕ) : (arrF X).size = 64 := by
  simp [arrF, marr]

theorem arrF_lt (X : ℕ) {j : ℕ} (hj : j < 64) : (arrF X)[j]! < 64 := by
  rw [arrF, marr_get _ hj]
  exact vcode_lt _

theorem compA_get (t u : Array ℕ) {i : ℕ} (hi : i < 64) : (compA t u)[i]! = t[u[i]!]! := by
  rw [compA, getElem!_ofFn_nat _ hi]

theorem idA_get {i : ℕ} (hi : i < 64) : (idA ())[i]! = i := by
  rw [idA, getElem!_ofFn_nat _ hi]

theorem left_inv {G GI : ℕ} (h : MULF G GI = ONE) {v : ℕ} (hv : v < 64) :
    (arrF G)[(arrF GI)[v]!]! = v := by
  have e : compA (arrF G) (arrF GI) = idA () := by rw [arrF_mul, h, arrF_one]
  have := congrArg (fun a => a[v]!) e
  rwa [compA_get _ _ hv, idA_get hv] at this

theorem ext64 {a b : Array ℕ} (ha : a.size = 64) (hb : b.size = 64)
    (h : ∀ v < 64, a[v]! = b[v]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro v hv1 hv2
  rw [← getElem!_pos a v hv1, ← getElem!_pos b v hv2]
  exact h v (by rw [ha] at hv1; exact hv1)

theorem invArr_arrF {G GI : ℕ} (h1 : MULF G GI = ONE) (h2 : MULF GI G = ONE) :
    invArr (arrF G) = arrF GI := by
  have hsz : (invArr (arrF G)).size = 64 := by
    unfold invArr
    rw [CFSG.KS.MathieuAut.size_foldl_set (fun i => (arrF G)[i]!), Array.size_replicate]
  refine ext64 hsz (arrF_size GI) fun v hv => ?_
  have hj := arrF_lt GI hv
  have e : (invArr (arrF G))[(arrF G)[(arrF GI)[v]!]!]! = (arrF GI)[v]! := by
    unfold invArr
    refine CFSG.KS.MathieuAut.foldl_set_self (fun i => (arrF G)[i]!) (List.range 64) _
      (fun j hj => by simpa using arrF_lt G (List.mem_range.1 hj)) (fun i hi k hk e => ?_) _
      (List.mem_range.2 hj)
    have hi' := List.mem_range.1 hi
    have hk' := List.mem_range.1 hk
    have a := left_inv h2 hi'
    have b := left_inv h2 hk'
    rw [← a, ← b, e]
  rwa [left_inv h1 hv] at e

theorem lookup_of_BInvE {T : ℕ → Array ℕ} {PA PB : ℕ → ℕ} {c : ℕ} {E : Enum}
    (h : BInvE T PA PB c E) {t : ℕ} (ht : t < c) : E.lookup (T t) = some t := by
  unfold Enum.lookup
  rw [h.2.2.2.2.2.2 t ht]
  simp only
  rw [if_pos ⟨by rw [h.1]; exact ht, h.2.2.2.1 t ht⟩]

theorem anyLt_of {n : ℕ} {p : ℕ → Bool} {j : ℕ} (hj : j < n) (h : p j = true) :
    anyLt n p = true := by
  unfold anyLt
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨⟨j, hj⟩, List.mem_finRange _, h⟩

end CFSG.KC.OmegaSix

end
