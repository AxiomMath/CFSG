module

public import Certificates.Data.Kernel.Misc.Coset.CovAct
public import Certificates.Data.Kernel.Misc.Coset.CovActSym
public import CFSG.Certificates.Kernel.Misc.Coset.ActSound
public import CFSG.Certificates.CosetTableAction
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.KC.MiscCoset.CovAct

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.KC.MiscCoset.Act

@[expose] def shiftS (q s t : ℕ) : ℕ := q * (s / q) + (s % q + t) % q

theorem div_shiftS {q : ℕ} (hq : 0 < q) (s t : ℕ) : shiftS q s t / q = s / q := by
  unfold shiftS
  rw [Nat.mul_add_div hq, Nat.div_eq_of_lt (Nat.mod_lt _ hq), Nat.add_zero]

theorem mod_shiftS {q : ℕ} (hq : 0 < q) (s t : ℕ) : shiftS q s t % q = (s % q + t) % q := by
  unfold shiftS
  rw [Nat.mul_add_mod, Nat.mod_mod]

theorem shiftS_shiftS {q : ℕ} (hq : 0 < q) (s a b : ℕ) :
    shiftS q (shiftS q s a) b = shiftS q s (a + b) := by
  have e : shiftS q (shiftS q s a) b = q * (shiftS q s a / q) + (shiftS q s a % q + b) % q := rfl
  rw [e, div_shiftS hq, mod_shiftS hq, Nat.mod_add_mod, Nat.add_assoc]
  rfl

theorem shiftS_comm {q : ℕ} (hq : 0 < q) (s a b : ℕ) :
    shiftS q (shiftS q s a) b = shiftS q (shiftS q s b) a := by
  rw [shiftS_shiftS hq, shiftS_shiftS hq, Nat.add_comm]

theorem shiftS_mod {q : ℕ} (s t : ℕ) : shiftS q s (t % q) = shiftS q s t := by
  unfold shiftS
  rw [Nat.add_mod_mod]

theorem shiftS_zero {q : ℕ} (s : ℕ) : shiftS q s 0 = s := by
  unfold shiftS
  rw [Nat.add_zero, Nat.mod_mod, Nat.div_add_mod]

theorem shiftS_of_mod {q : ℕ} (s t : ℕ) (ht : t % q = 0) : shiftS q s t = s := by
  rw [← shiftS_mod, ht, shiftS_zero]

theorem shiftS_base {q : ℕ} (hq : 0 < q) (p t : ℕ) (ht : t < q) : shiftS q (q * p) t = q * p + t := by
  unfold shiftS
  rw [Nat.mul_div_cancel_left _ hq, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt ht]

theorem shiftS_eq {q : ℕ} (hq : 0 < q) (s : ℕ) : shiftS q (q * (s / q)) (s % q) = s := by
  rw [shiftS_base hq _ _ (Nat.mod_lt _ hq), Nat.div_add_mod]

theorem shiftS_lt {q N : ℕ} (hq : 0 < q) {s : ℕ} (hs : s / q < N) (t : ℕ) : shiftS q s t < q * N := by
  unfold shiftS
  have h1 := Nat.mod_lt (s % q + t) hq
  have h2 : q * (s / q) + q ≤ q * N := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hs
  omega

theorem stepE_eq (q s e : ℕ) : stepE q s e = shiftS q e (s % q) := by
  change q * (e / q) + (s % q + e % q) % q = q * (e / q) + (e % q + s % q) % q
  rw [Nat.add_comm (s % q)]

theorem stepS_eq (A : ℕ → ℕ) (q L s c : ℕ) :
    stepS A q L s c = shiftS q (A (s / q * L + c)) (s % q) := by
  unfold stepS
  rw [stepE_eq]
  rfl

theorem stepS_shiftS (A : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (L s t c : ℕ) :
    stepS A q L (shiftS q s t) c = shiftS q (stepS A q L s c) t := by
  rw [stepS_eq, stepS_eq, div_shiftS hq, mod_shiftS hq, shiftS_shiftS hq, shiftS_mod]

theorem walkS_cons (A : ℕ → ℕ) (q L c : ℕ) (w : List ℕ) (s : ℕ) :
    walkS A q L (c :: w) s = walkS A q L w (stepS A q L s c) := rfl

theorem walkS_nil (A : ℕ → ℕ) (q L : ℕ) (s : ℕ) : walkS A q L [] s = s := rfl

theorem walkS_append (A : ℕ → ℕ) (q L : ℕ) (u v : List ℕ) (s : ℕ) :
    walkS A q L (u ++ v) s = walkS A q L v (walkS A q L u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons c u ih => exact ih _

theorem walkS_shiftS (A : ℕ → ℕ) {q : ℕ} (hq : 0 < q) (L : ℕ) (w : List ℕ) (s t : ℕ) :
    walkS A q L w (shiftS q s t) = shiftS q (walkS A q L w s) t := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih => rw [walkS_cons, walkS_cons, stepS_shiftS A hq, ih]

theorem invC_eq (c : ℕ) : invC c = invCode c := by
  unfold invC invCode
  cases Nat.beq (Nat.mod c 2) 0 <;> rfl

section Point

variable {A : ℕ → ℕ} {q N mb L : ℕ} {mac : List (List ℕ)} {chk : List (List ℕ × ℕ)}

theorem macRec_spec (A : ℕ → ℕ) (q L p mb : ℕ) :
    ∀ (mac : List (List ℕ)) (j : ℕ), List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun w _ ih j => andB
        (Nat.beq (A (Nat.add (Nat.mul p L) (Nat.add (Nat.add mb mb) j))) (walkS A q L w (Nat.mul q p)))
        (ih (Nat.succ j))) mac j = true →
      ∀ i (hi : i < mac.length), A (p * L + (2 * mb + (j + i))) = walkS A q L mac[i] (q * p)
  | [], _, _, i, hi => absurd hi (by simp)
  | w :: mac, j, h, i, hi => by
    have h' := h
    simp only [andB_eq, Bool.and_eq_true] at h'
    rcases i with _ | i
    · have := Nat.eq_of_beq_eq_true h'.1
      simpa [two_mul] using this
    · have := macRec_spec A q L p mb mac (j + 1) h'.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem chkRec_spec (A : ℕ → ℕ) (q L p : ℕ) : ∀ (chk : List (List ℕ × ℕ)),
    List.rec (motive := fun _ => Bool) true
      (fun wt _ ih => andB (Nat.beq (walkS A q L wt.1 (Nat.mul q p)) (Nat.add (Nat.mul q p) wt.2)) ih)
      chk = true → ∀ wt ∈ chk, walkS A q L wt.1 (q * p) = q * p + wt.2
  | [], _, _, hw => absurd hw (by simp)
  | wt :: chk, h, wt', hw => by
    have h' : (Nat.beq (walkS A q L wt.1 (Nat.mul q p)) (Nat.add (Nat.mul q p) wt.2) &&
        List.rec (motive := fun _ => Bool) true
          (fun wt _ ih => andB (Nat.beq (walkS A q L wt.1 (Nat.mul q p))
            (Nat.add (Nat.mul q p) wt.2)) ih) chk) = true := by
      rw [← andB_eq]; exact h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hw with rfl | hw
    · exact Nat.eq_of_beq_eq_true h'.1
    · exact chkRec_spec A q L p chk h'.2 wt' hw

theorem cpOK_spec {p : ℕ} (h : cpOK A q N mb L mac chk p = true) :
    (∀ c < 2 * mb, A (p * L + c) < q * N ∧
      stepS A q L (stepS A q L (q * p) c) (invCode c) = q * p) ∧
    (∀ i (hi : i < mac.length), A (p * L + (2 * mb + i)) = walkS A q L mac[i] (q * p)) ∧
    (∀ wt ∈ chk, walkS A q L wt.1 (q * p) = q * p + wt.2) := by
  unfold cpOK at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨fun c hc => ?_, fun i hi => ?_, chkRec_spec A q L p chk h.2.2⟩
  · have hc' : c < 0 + Nat.add mb mb := by rw [Nat.add_eq]; omega
    have := allR_spec h.1 c (Nat.zero_le _) hc'
    rw [andB_eq, Bool.and_eq_true] at this
    refine ⟨by simpa [Nat.blt_eq] using this.1, ?_⟩
    rw [← invC_eq]
    exact Nat.eq_of_beq_eq_true this.2
  · have := macRec_spec A q L p mb mac 0 h.2.1 i hi
    simpa using this

end Point

section Cover

variable {M : ℕ} {A : ℕ → ℕ} {q N mb L : ℕ} {zs : List ℕ} {mac : List (List ℕ)}
  {chk : List (List ℕ × ℕ)}

@[expose] def zcode (q mb : ℕ) (zs : List ℕ) (c : ℕ) : ℕ :=
  if c % 2 = 0 then zs.getD (c / 2 - mb) 0 % q else (q - zs.getD (c / 2 - mb) 0 % q) % q

@[expose] noncomputable def δc (A : ℕ → ℕ) (q mb L : ℕ) (zs : List ℕ) (s c : ℕ) : ℕ :=
  if c < 2 * mb then stepS A q L s c else shiftS q s (zcode q mb zs c)

theorem δc_shiftS (hq : 0 < q) (s t c : ℕ) :
    δc A q mb L zs (shiftS q s t) c = shiftS q (δc A q mb L zs s c) t := by
  unfold δc
  split
  · exact stepS_shiftS A hq L s t c
  · exact shiftS_comm hq s t _

theorem foldl_shiftS (hq : 0 < q) (w : List ℕ) (s t : ℕ) :
    w.foldl (δc A q mb L zs) (shiftS q s t) = shiftS q (w.foldl (δc A q mb L zs) s) t := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih => rw [List.foldl_cons, List.foldl_cons, δc_shiftS hq, ih]

theorem foldl_base (w : List ℕ) (hw : ∀ c ∈ w, c < 2 * mb) (s : ℕ) :
    w.foldl (δc A q mb L zs) s = walkS A q L w s := by
  induction w generalizing s with
  | nil => rfl
  | cons c w ih =>
    rw [List.foldl_cons, walkS_cons, ih (fun c' h => hw c' (List.mem_cons_of_mem _ h))]
    unfold δc
    rw [if_pos (hw c List.mem_cons_self)]

section Hyp

variable (hq : 0 < q) (hpt : ∀ p < N, cpOK A q N mb L mac chk p = true)
include hq hpt

theorem stepS_lt {s c : ℕ} (hs : s < q * N) (hc : c < 2 * mb) : stepS A q L s c < q * N := by
  have hp : s / q < N := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact hs)
  have he := ((cpOK_spec (hpt _ hp)).1 c hc).1
  rw [stepS_eq]
  exact shiftS_lt hq ((Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact he)) _

theorem walkS_lt (w : List ℕ) (hw : ∀ c ∈ w, c < 2 * mb) {s : ℕ} (hs : s < q * N) :
    walkS A q L w s < q * N := by
  induction w generalizing s with
  | nil => exact hs
  | cons c w ih =>
    exact ih (fun c' h => hw c' (List.mem_cons_of_mem _ h)) (stepS_lt hq hpt hs (hw c List.mem_cons_self))

theorem stepS_mac {s : ℕ} (hs : s < q * N) {i : ℕ} (hi : i < mac.length) :
    stepS A q L s (2 * mb + i) = walkS A q L mac[i] s := by
  have hp : s / q < N := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact hs)
  rw [stepS_eq, (cpOK_spec (hpt _ hp)).2.1 i hi, ← walkS_shiftS A hq,
    shiftS_eq hq]

theorem walkS_expand (hmac : ∀ w ∈ mac, ∀ c ∈ w, c < 2 * mb) (hL : L = 2 * mb + mac.length) :
    ∀ w : List ℕ, (∀ c ∈ w, c < L) → ∀ s < q * N,
      walkS A q L w s = walkS A q L (expandW mb mac w) s ∧ walkS A q L w s < q * N := by
  intro w
  induction w with
  | nil => intro _ s hs; exact ⟨rfl, hs⟩
  | cons c w ih =>
    intro hw s hs
    have hw' : ∀ c ∈ w, c < L := fun c' h => hw c' (List.mem_cons_of_mem _ h)
    have hc := hw c List.mem_cons_self
    rw [expandW, List.flatMap_cons, ← expandW, walkS_append, walkS_cons]
    by_cases hb : 2 * mb ≤ c
    · rw [if_pos hb]
      obtain ⟨i, rfl⟩ : ∃ i, c = 2 * mb + i := ⟨c - 2 * mb, by omega⟩
      have hi : i < mac.length := by omega
      have hm := List.getElem_mem hi
      rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi, stepS_mac hq hpt hs hi]
      exact ih hw' _ (walkS_lt hq hpt _ (hmac _ hm) hs)
    · rw [if_neg hb]
      have hc' : c < 2 * mb := by omega
      exact ih hw' _ (stepS_lt hq hpt hs hc')

theorem walkS_chk (hmac : ∀ w ∈ mac, ∀ c ∈ w, c < 2 * mb) (hL : L = 2 * mb + mac.length)
    {wt : List ℕ × ℕ} (hwt : wt ∈ chk) (hwL : ∀ c ∈ wt.1, c < L) (ht : wt.2 < q) {s : ℕ}
    (hs : s < q * N) : walkS A q L (expandW mb mac wt.1) s = shiftS q s wt.2 := by
  have hp : s / q < N := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact hs)
  rw [← (walkS_expand hq hpt hmac hL wt.1 hwL s hs).1, ← shiftS_eq hq s, walkS_shiftS A hq,
    (cpOK_spec (hpt _ hp)).2.2 wt hwt, ← shiftS_base hq _ _ ht, shiftS_comm hq]

theorem zcode_add {c : ℕ} : (zcode q mb zs c + zcode q mb zs (invCode c)) % q = 0 := by
  have hq' : ∀ z, (z % q + (q - z % q) % q) % q = 0 := by
    intro z
    have := Nat.mod_lt z hq
    rw [Nat.add_mod_mod, Nat.add_sub_cancel' this.le, Nat.mod_self]
  unfold zcode
  rw [show invCode c = if c % 2 = 0 then c + 1 else c - 1 by
    unfold invCode
    by_cases h : c % 2 = 0
    · have : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
      rw [this]; simp [h]
    · have : Nat.beq (Nat.mod c 2) 0 = false := by
        cases hb : Nat.beq (Nat.mod c 2) 0 with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [this]; simp [h]]
  by_cases h : c % 2 = 0
  · rw [if_pos h, if_pos h, if_neg (by omega), show (c + 1) / 2 = c / 2 by omega]
    exact hq' _
  · rw [if_neg h, if_neg h, if_pos (by omega), show (c - 1) / 2 = c / 2 by omega, Nat.add_comm]
    exact hq' _

theorem δc_live {s : ℕ} (hs : s < q * N) (c : ℕ) : δc A q mb L zs s c < q * N := by
  unfold δc
  split
  · exact stepS_lt hq hpt hs ‹_›
  · exact shiftS_lt hq ((Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact hs)) _

theorem δc_inv {s : ℕ} (hs : s < q * N) {c : ℕ} (hc : c < 2 * M) (hmb : mb ≤ M) :
    δc A q mb L zs (δc A q mb L zs s c) (invCode c) = s := by
  have hp : s / q < N := (Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact hs)
  have hic : invCode c = if c % 2 = 0 then c + 1 else c - 1 := by
    unfold invCode
    by_cases h : c % 2 = 0
    · have : Nat.beq (Nat.mod c 2) 0 = true := by rw [Nat.beq_eq]; exact h
      rw [this]; simp [h]
    · have : Nat.beq (Nat.mod c 2) 0 = false := by
        cases hb : Nat.beq (Nat.mod c 2) 0 with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [this]; simp [h]
  by_cases hb : c < 2 * mb
  · have hb' : invCode c < 2 * mb := by rw [hic]; split <;> omega
    unfold δc
    rw [if_pos hb, if_pos hb', ← shiftS_eq hq s, stepS_shiftS A hq, stepS_shiftS A hq,
      ((cpOK_spec (hpt _ hp)).1 c hb).2]
  · have hb' : ¬ invCode c < 2 * mb := by rw [hic]; split <;> omega
    unfold δc
    rw [if_neg hb, if_neg hb', shiftS_shiftS hq]
    exact shiftS_of_mod s _ (zcode_add hq hpt)

end Hyp

end Cover

section Group

variable {q N : ℕ} (hq : 0 < q)
include hq

theorem add_sub_mod_mod (t : ℕ) : (t + (q - t % q)) % q = 0 := by
  have h1 := Nat.mod_lt t hq
  have h2 := Nat.div_add_mod t q
  have e : t + (q - t % q) = q * (t / q + 1) := by
    rw [Nat.mul_succ]
    omega
  rw [e, Nat.mul_mod_right]

@[expose] noncomputable def shPerm (t : ℕ) : Equiv.Perm {s : ℕ // s < q * N} where
  toFun s := ⟨shiftS q s.1 t,
    shiftS_lt hq ((Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact s.2)) _⟩
  invFun s := ⟨shiftS q s.1 (q - t % q),
    shiftS_lt hq ((Nat.div_lt_iff_lt_mul hq).2 (by rw [Nat.mul_comm N q]; exact s.2)) _⟩
  left_inv s := Subtype.ext (by
    change shiftS q (shiftS q s.1 t) (q - t % q) = s.1
    rw [shiftS_shiftS hq, shiftS_of_mod _ _ (add_sub_mod_mod hq t)])
  right_inv s := Subtype.ext (by
    change shiftS q (shiftS q s.1 (q - t % q)) t = s.1
    rw [shiftS_shiftS hq, Nat.add_comm, shiftS_of_mod _ _ (add_sub_mod_mod hq t)])

theorem shPerm_apply (t : ℕ) (s : {s : ℕ // s < q * N}) : (shPerm hq t s).1 = shiftS q s.1 t := rfl

theorem shPerm_mul (a b : ℕ) : shPerm (N := N) hq a * shPerm hq b = shPerm hq (a + b) := by
  ext s
  rw [Equiv.Perm.mul_apply, shPerm_apply, shPerm_apply, shPerm_apply, shiftS_shiftS hq,
    Nat.add_comm]

theorem shPerm_of_mod (t : ℕ) (ht : t % q = 0) : shPerm (N := N) hq t = 1 := by
  ext s
  rw [shPerm_apply, shiftS_of_mod _ _ ht]
  rfl

theorem shPerm_mod (t : ℕ) : shPerm (N := N) hq (t % q) = shPerm hq t := by
  ext s
  rw [shPerm_apply, shPerm_apply, shiftS_mod]

noncomputable abbrev shG (t : ℕ) : (Equiv.Perm {s : ℕ // s < q * N})ᵐᵒᵖ := MulOpposite.op (shPerm hq t)

theorem shG_mul (a b : ℕ) : shG (N := N) hq a * shG hq b = shG hq (a + b) := by
  rw [shG, shG, ← MulOpposite.op_mul, shPerm_mul, Nat.add_comm]

theorem shG_of_mod (t : ℕ) (ht : t % q = 0) : shG (N := N) hq t = 1 := by
  rw [shG, shPerm_of_mod hq t ht]
  rfl

theorem shG_mod (t : ℕ) : shG (N := N) hq (t % q) = shG hq t := by rw [shG, shPerm_mod]

theorem shG_inv (t : ℕ) : (shG (N := N) hq t)⁻¹ = shG hq (q - t % q) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← shG_mod hq t, shG_mul]
  exact shG_of_mod hq _ (by rw [Nat.add_sub_cancel' (Nat.mod_lt t hq).le, Nat.mod_self])

theorem shPerm_pow (t n : ℕ) : shPerm (N := N) hq t ^ n = shPerm hq (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.zero_mul, shPerm_of_mod hq 0 (Nat.zero_mod q)]
  | succ n ih => rw [pow_succ, ih, shPerm_mul, Nat.succ_mul]

end Group

section Main

variable {M : ℕ} {A : ℕ → ℕ} {q N mb L : ℕ} {zs : List ℕ} {mac : List (List ℕ)}
  {chk : List (List ℕ × ℕ)}

theorem expandW_lt (hmac : ∀ w ∈ mac, ∀ c ∈ w, c < 2 * mb) (w : List ℕ)
    (hw : ∀ c ∈ w, c < 2 * mb + mac.length) : ∀ c ∈ expandW mb mac w, c < 2 * mb := by
  intro c hc
  rw [expandW, List.mem_flatMap] at hc
  obtain ⟨d, hd, hcd⟩ := hc
  by_cases hb : 2 * mb ≤ d
  · rw [if_pos hb] at hcd
    have hi : d - 2 * mb < mac.length := by have := hw d hd; omega
    rw [List.getD_eq_getElem _ _ hi] at hcd
    exact hmac _ (List.getElem_mem hi) c hcd
  · rw [if_neg hb, List.mem_singleton] at hcd
    omega

theorem letterCode_ge {l : Fin M × Bool} (hl : mb ≤ l.1.val) : 2 * mb ≤ letterCode l := by
  obtain ⟨g, b⟩ := l
  have : mb ≤ g.val := hl
  unfold letterCode
  split <;> omega

theorem zl_letter {l : Fin M × Bool} (hl : mb ≤ l.1.val) :
    zcode q mb zs (letterCode l) = zl q mb zs l := by
  obtain ⟨g, b⟩ := l
  have hl' : mb ≤ g.val := hl
  have hn : ¬ g.val < mb := by omega
  unfold zcode zl letterCode
  cases b
  · have h1 : (2 * g.val + 1) % 2 = 1 := by omega
    have h2 : (2 * g.val + 1) / 2 = g.val := by omega
    simp [h1, h2, hn]
  · have h1 : (2 * g.val) % 2 = 0 := by omega
    have h2 : (2 * g.val) / 2 = g.val := by omega
    simp [h1, h2, hn]

theorem covAct_sound (ws : List (List (Fin M × Bool))) (hq : 0 < q)
    (hpt : ∀ p < N, cpOK A q N mb L mac chk p = true) (hint : List (ℕ × ℕ × ℕ))
    (hsym : symOK q mb L zs mac chk ws hint = true) :
    ∃ ψ : PG M ws →* (Equiv.Perm {s : ℕ // s < q * N})ᵐᵒᵖ,
      ∀ g : Fin M, mb ≤ g.val → ψ (PresentedGroup.of g) = shG hq (zs.getD (g.val - mb) 0) := by
  unfold symOK at hsym
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hsym
  obtain ⟨⟨⟨⟨⟨⟨-, hmb⟩, hL⟩, hmac⟩, hchk⟩, hlen⟩, hall⟩ := hsym
  set δ := δc A q mb L zs with hδ
  have hlive : ∀ c, c < q * N → ∀ x < 2 * M, δ c x < q * N := fun c hc x _ =>
    δc_live hq hpt hc x
  have hinv : ∀ c, c < q * N → ∀ x < 2 * M, δ (δ c x) (invCode x) = c := fun c hc x hx =>
    δc_inv hq hpt hc hx hmb
  obtain ⟨ψ₀, hψ₀⟩ := exists_action_step (m := M) ([] : List (List (Fin M × Bool)))
    (fun c => c < q * N) δ hlive hinv (by intro c _ r hr; simp [codes] at hr)
  set φ : FreeGroup (Fin M) →* (Equiv.Perm {s : ℕ // s < q * N})ᵐᵒᵖ :=
    ψ₀.comp (PresentedGroup.mk _) with hφ
  have hact : ∀ (w : List (Fin M × Bool)) (s : {s : ℕ // s < q * N}),
      ((φ (FreeGroup.mk w)).unop s).1 = (w.map letterCode).foldl δ s.1 := by
    intro w s
    have := act_evalWord_step ψ₀ hψ₀ (w.map letterCode) (codes_lt w) s
    rw [evalWord_presLetter] at this
    exact this
  have hcomm : ∀ (t : ℕ) (x : FreeGroup (Fin M)), shG hq t * φ x = φ x * shG hq t := by
    intro t x
    rw [← FreeGroup.mk_toWord (x := x)]
    apply MulOpposite.unop_injective
    ext s
    simp only [shG, MulOpposite.unop_mul, MulOpposite.unop_op, Equiv.Perm.mul_apply, shPerm_apply,
      hact]
    exact foldl_shiftS hq _ _ _
  have hcent : ∀ l : Fin M × Bool, mb ≤ l.1.val →
      φ (FreeGroup.mk [l]) = shG hq (zl q mb zs l) := by
    intro l hl
    apply MulOpposite.unop_injective
    ext s
    simp only [shG, hact, MulOpposite.unop_op, shPerm_apply, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil, hδ]
    unfold δc
    rw [if_neg (Nat.not_lt.mpr (letterCode_ge hl)), zl_letter hl]
  have hdecomp : ∀ u : List (Fin M × Bool),
      φ (FreeGroup.mk u) = φ (FreeGroup.mk (projB mb u)) * shG hq (zsum q mb zs u) := by
    intro u
    induction u with
    | nil =>
      rw [shG_of_mod hq _ (by simp [zsum]), mul_one]
      rfl
    | cons l u ih =>
      have hsplit : ∀ v : List (Fin M × Bool), FreeGroup.mk (l :: v) =
          FreeGroup.mk [l] * FreeGroup.mk v := fun v => by rw [FreeGroup.mul_mk]; rfl
      have hz : zsum q mb zs (l :: u) = zl q mb zs l + zsum q mb zs u := by
        simp [zsum]
      by_cases hl : l.1.val < mb
      · have hp : projB mb (l :: u) = l :: projB mb u := by
          simp [projB, List.filter_cons, hl]
        have hzl : zl q mb zs l = 0 := by simp [zl, hl]
        rw [hsplit u, map_mul, ih, hp, hsplit (projB mb u), map_mul, mul_assoc, hz, hzl,
          Nat.zero_add]
      · have hp : projB mb (l :: u) = projB mb u := by
          simp [projB, List.filter_cons, hl]
        rw [hsplit u, map_mul, ih, hp, hcent l (by omega), ← mul_assoc, hcomm, mul_assoc, shG_mul,
          hz]
  have hchkφ : ∀ wt ∈ chk, ∀ v : List (Fin M × Bool),
      v.map letterCode = expandW mb mac wt.1 → φ (FreeGroup.mk v) = shG hq wt.2 := by
    intro wt hwt v hv
    have hwL := (hchk wt hwt).2
    apply MulOpposite.unop_injective
    ext s
    rw [hact, MulOpposite.unop_op, shPerm_apply, hv,
      foldl_base _ (expandW_lt hmac wt.1 (fun c hc => hL ▸ hwL c hc)) s.1]
    exact walkS_chk hq hpt hmac hL hwt (fun c hc => hwL c hc) (hchk wt hwt).1 s.2
  have hrot : ∀ (v : List (Fin M × Bool)) (k t : ℕ), k ≤ v.length →
      φ (FreeGroup.mk (v.rotate k)) = shG hq t → φ (FreeGroup.mk v) = shG hq t := by
    intro v k t hk h
    rw [List.rotate_eq_drop_append_take hk, ← FreeGroup.mul_mk, map_mul] at h
    rw [← List.take_append_drop k v, ← FreeGroup.mul_mk, map_mul]
    have e : φ (FreeGroup.mk (List.drop k v)) =
        shG hq t * (φ (FreeGroup.mk (List.take k v)))⁻¹ := by
      rw [← h, mul_inv_cancel_right]
    rw [e, ← mul_assoc, ← hcomm, mul_inv_cancel_right]
  have hrel : ∀ u ∈ ws, φ (FreeGroup.mk u) = 1 := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    have hi' : i < hint.length := hlen ▸ hi
    have hzl : i < (ws.zip hint).length := by simp [hi, hi']
    have hz : (ws.zip hint)[i]'hzl = (ws[i], hint[i]) := List.getElem_zip
    have H := hall _ (List.getElem_mem hzl)
    rw [hz] at H
    change hintOK q mb zs mac chk ws[i] hint[i] = true at H
    generalize hint[i] = h at H
    obtain ⟨j, k, b⟩ := h
    unfold hintOK at H
    rw [hdecomp]
    split at H
    · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at H
      rw [← FreeGroup.reduce.self, H.1, shG_of_mod hq _ H.2, mul_one, ← FreeGroup.one_eq_mk,
        map_one]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at H
      obtain ⟨hj, H⟩ := H
      have hwt : chk.getD (j - 1) ([], 0) ∈ chk := by
        rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
      split at H
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at H
        obtain ⟨⟨hk, hE⟩, ht⟩ := H
        rw [hrot _ k _ hk (hchkφ _ hwt _ hE), shG_mul]
        exact shG_of_mod hq _ ht
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at H
        obtain ⟨⟨hk, hE⟩, ht⟩ := H
        have hk' : k ≤ (FreeGroup.invRev (projB mb ws[i])).length := by
          rwa [FreeGroup.invRev_length]
        have h1 := hrot _ k _ hk' (hchkφ _ hwt _ hE)
        rw [← FreeGroup.inv_mk, map_inv, inv_eq_iff_eq_inv, shG_inv] at h1
        have htq := (hchk _ hwt).1
        rw [h1, Nat.mod_eq_of_lt htq, shG_mul]
        exact shG_of_mod hq _ ht
  have hlift : ∀ r ∈ {r : FreeGroup (Fin M) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift (fun i => φ (FreeGroup.of i)) r = 1 := by
    intro r hr
    have e : FreeGroup.lift (fun i => φ (FreeGroup.of i)) = φ :=
      FreeGroup.ext_hom _ _ fun i => FreeGroup.lift_apply_of
    simp only [Set.mem_setOf_eq, List.mem_map] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    rw [e]
    exact hrel u hu
  refine ⟨PresentedGroup.toGroup hlift, fun g hg => ?_⟩
  rw [PresentedGroup.toGroup.of]
  have := hcent (g, true) hg
  rw [show FreeGroup.mk [(g, true)] = FreeGroup.of g from rfl] at this
  rw [this, zl, if_neg (Nat.not_lt.mpr hg : ¬ (g, true).1.val < mb), if_pos rfl, shG,
    shPerm_mod]

theorem dvd_orderOf_of_covAct (ws : List (List (Fin M × Bool))) (hqp : q.Prime) (hN : 0 < N)
    (hpt : ∀ p < N, cpOK A q N mb L mac chk p = true) (hint : List (ℕ × ℕ × ℕ))
    (hsym : symOK q mb L zs mac chk ws hint = true) (g : Fin M) (hg : mb ≤ g.val)
    (hz : zs.getD (g.val - mb) 0 % q ≠ 0) :
    q ∣ orderOf (PresentedGroup.of (rels := {r : FreeGroup (Fin M) | r ∈ ws.map FreeGroup.mk}) g) := by
  have hq := hqp.pos
  obtain ⟨ψ, hψ⟩ := covAct_sound ws hq hpt hint hsym
  have hfact : Fact q.Prime := ⟨hqp⟩
  have hord : orderOf (shG (N := N) hq (zs.getD (g.val - mb) 0)) = q := by
    apply orderOf_eq_prime
    · rw [shG, ← MulOpposite.op_pow, shPerm_pow, shPerm_of_mod hq _ (Nat.mul_mod_right _ _)]
      rfl
    · intro h1'
      have h1 : shPerm (N := N) hq (zs.getD (g.val - mb) 0) = 1 :=
        MulOpposite.op_injective h1'
      have hs0 : (0 : ℕ) < q * N := Nat.mul_pos hq hN
      have := congrArg (fun σ : Equiv.Perm {s : ℕ // s < q * N} => (σ ⟨0, hs0⟩).1) h1
      simp only [shPerm_apply, Equiv.Perm.coe_one, id_eq] at this
      unfold shiftS at this
      rw [Nat.zero_div, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.zero_add] at this
      exact hz this
  have h1 := orderOf_map_dvd ψ (PresentedGroup.of g)
  rw [hψ g hg, hord] at h1
  exact h1

end Main

end CFSG.KC.MiscCoset.CovAct

end
