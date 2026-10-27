module

public import CFSG.Certificates.Kernel.Spor.PK.F42Mat
public import CFSG.Certificates.Kernel.Misc.F42Defs

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.Blueprint.Chevalley

@[expose] def vecCode (w : Fin Tag.F4.rank → ℤ) : ℕ :=
  ∑ t : Fin Tag.F4.rank, (w t + 32).toNat * 64 ^ t.val

theorem offR_eq : offR = vecCode 0 := by
  show 8521760 = ∑ t : Fin 4, ((0 : Fin 4 → ℤ) t + 32).toNat * 64 ^ t.val
  rw [Fin.sum_univ_four]
  simp

theorem codeR_nil : codeR [] = 0 := rfl

private theorem codeR_rec (l : List ℕ) (t : ℕ) :
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih t => Nat.add (Nat.shiftLeft x (Nat.mul 6 t)) (ih (Nat.succ t))) l) t =
      64 ^ t * codeR l := by
  induction l generalizing t with
  | nil => show 0 = 64 ^ t * 0; simp
  | cons x l ih =>
    show x <<< (6 * t) + (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih t => Nat.add (Nat.shiftLeft x (Nat.mul 6 t)) (ih (Nat.succ t))) l) (t + 1) =
      64 ^ t * (x <<< (6 * 0) + (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih t => Nat.add (Nat.shiftLeft x (Nat.mul 6 t)) (ih (Nat.succ t))) l) (0 + 1))
    rw [ih (t + 1), ih (0 + 1), Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have h1 : (2 : ℕ) ^ (6 * t) = 64 ^ t := by
      rw [Nat.pow_mul]
    rw [h1, pow_succ]
    simp
    ring

theorem codeR_cons (x : ℕ) (l : List ℕ) : codeR (x :: l) = x + 64 * codeR l := by
  show x <<< (6 * 0) + (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih t => Nat.add (Nat.shiftLeft x (Nat.mul 6 t)) (ih (Nat.succ t))) l) (0 + 1) = _
  rw [codeR_rec l (0 + 1)]
  simp

private theorem sum4_inj {x y : Fin 4 → ℕ} (hx : ∀ t, x t < 64) (hy : ∀ t, y t < 64)
    (h : ∑ t : Fin 4, x t * 64 ^ t.val = ∑ t : Fin 4, y t * 64 ^ t.val) : x = y := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four] at h
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have g0 := hy 0
  have g1 := hy 1
  have g2 := hy 2
  have g3 := hy 3
  simp at h
  funext t
  fin_cases t <;> simp <;> omega

theorem vecCode_inj {w w' : Fin Tag.F4.rank → ℤ} (hw : ∀ t, -32 ≤ w t ∧ w t ≤ 31)
    (hw' : ∀ t, -32 ≤ w' t ∧ w' t ≤ 31) (h : vecCode w = vecCode w') : w = w' := by
  have key := sum4_inj (x := fun t : Fin 4 => (w t + 32).toNat)
    (y := fun t : Fin 4 => (w' t + 32).toNat)
    (fun t => by have := hw t; omega) (fun t => by have := hw' t; omega) h
  funext t
  have := congrFun key t
  have h1 := hw t
  have h2 := hw' t
  omega

theorem vecCode_add_eq {a b c d : Fin Tag.F4.rank → ℤ} (ha : ∀ t, -32 ≤ a t ∧ a t ≤ 31)
    (hb : ∀ t, -32 ≤ b t ∧ b t ≤ 31) (hc : ∀ t, -32 ≤ c t ∧ c t ≤ 31)
    (hd : ∀ t, -32 ≤ d t ∧ d t ≤ 31) (h : a + b = c + d) :
    vecCode a + vecCode b = vecCode c + vecCode d := by
  unfold vecCode
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← add_mul, ← add_mul]
  congr 1
  have e := congrFun h t
  simp only [Pi.add_apply] at e
  have h1 := ha t
  have h2 := hb t
  have h3 := hc t
  have h4 := hd t
  omega

private theorem nthLLR_eq (L : List (List ℕ)) (k : ℕ) : rootsK.nthLLR L k = L.getD k [] := by
  induction L generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ j =>
      show rootsK.nthLLR xs j = (x :: xs).getD (j + 1) []
      rw [List.getD_cons_succ, ih j]

private theorem lenRec_eq (L : List (List ℕ)) :
    (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L : ℕ) = L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) xs) =
      xs.length + 1
    rw [ih]

theorem rootsK_spec {RL : List (List ℕ)} {RC : List ℕ} (h : rootsK RL RC = true) :
    RL.length = 48 ∧ RC.length = 48 ∧ ∀ k < 48, (RL.getD k []).length = 4 ∧
      (∀ x ∈ RL.getD k [], 24 ≤ x ∧ x ≤ 40) ∧ RC.getD k 0 = codeR (RL.getD k []) := by
  simp only [rootsK, andB_eq, letB_eq, Bool.and_eq_true, Nat.beq_eq, allN_lqt_iff,
    allL_lqt_iff, lenN_misc_eq, lenRec_eq, nthLLR_eq, Nat.ble_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, h1, fun k hk => ?_⟩
  obtain ⟨c1, c2, c3⟩ := h3 k hk
  exact ⟨c2, c3, by rw [← nthV_eq]; exact c1⟩

section Roots

variable {RL : List (List ℕ)} {RC : List ℕ} {R : List (List ℤ)}

theorem roots_length (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) : R.length = 48 := by
  rw [hR, List.length_map]
  exact (rootsK_spec h).1

private theorem getD_roots (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) (k : ℕ) :
    R.getD k [] = (RL.getD k []).map fun n : ℕ => (n : ℤ) - 32 := by
  subst hR
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases RL[k]? <;> rfl

private theorem getD_of_lt {α : Type} (l : List α) (i : ℕ) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

private theorem rootAtG_eq (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) (k : ℕ)
    (t : Fin Tag.F4.rank) :
    rootAtG R k t = (((RL.getD k []).getD t.val 32 : ℕ) : ℤ) - 32 := by
  show (R.getD k []).getD t.val 0 = _
  rw [getD_roots hR]
  generalize RL.getD k [] = l
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[t.val]? <;> simp

theorem rootAtG_bound (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {k : ℕ} (hk : k < 48)
    (t : Fin Tag.F4.rank) : -8 ≤ rootAtG R k t ∧ rootAtG R k t ≤ 8 := by
  obtain ⟨_, _, hk'⟩ := rootsK_spec h
  obtain ⟨hlen, hbnd, -⟩ := hk' k hk
  rw [rootAtG_eq hR]
  have ht : t.val < (RL.getD k []).length := by rw [hlen]; exact t.isLt
  have hmem : (RL.getD k []).getD t.val 32 ∈ RL.getD k [] := by
    rw [getD_of_lt _ _ _ ht]
    exact List.getElem_mem ht
  have := hbnd _ hmem
  omega

theorem roots_ofFn (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {k : ℕ} (hk : k < 48) :
    List.ofFn (rootAtG R k) = R.getD k [] := by
  obtain ⟨_, _, hk'⟩ := rootsK_spec h
  obtain ⟨hlen, -, -⟩ := hk' k hk
  rw [getD_roots hR]
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_map, hlen]
    rfl
  · intro i h1 h2
    have h3 : i < (RL.getD k []).length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map]
    show _ = _
    rw [rootAtG_eq hR, getD_of_lt _ _ _ h3]

theorem rootsK_code (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {k : ℕ} (hk : k < 48) :
    nthV RC k = vecCode (rootAtG R k) := by
  obtain ⟨_, _, hk'⟩ := rootsK_spec h
  obtain ⟨hlen, -, hcode⟩ := hk' k hk
  rw [nthV_eq, hcode]
  have hv : ∀ t : Fin Tag.F4.rank,
      rootAtG R k t = (((RL.getD k []).getD t.val 32 : ℕ) : ℤ) - 32 := rootAtG_eq hR k
  have e : vecCode (rootAtG R k) =
      ∑ t : Fin Tag.F4.rank, ((RL.getD k []).getD t.val 32) * 64 ^ t.val := by
    unfold vecCode
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hv t]
    congr 1
    omega
  rw [e]
  generalize RL.getD k [] = l at hlen ⊢
  match l, hlen with
  | [a, b, c, d], _ =>
    rw [codeR_cons, codeR_cons, codeR_cons, codeR_cons, codeR_nil]
    show _ = ∑ t : Fin 4, [a, b, c, d].getD t.val 32 * 64 ^ t.val
    rw [Fin.sum_univ_four]
    simp
    ring

theorem rootsK_sum (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Nat.sub (Nat.add (nthV RC i) (nthV RC j)) offR = vecCode (rootAtG R i + rootAtG R j) := by
  have hi' := rootAtG_bound h hR hi
  have hj' := rootAtG_bound h hR hj
  have key := vecCode_add_eq (a := rootAtG R i) (b := rootAtG R j)
    (c := rootAtG R i + rootAtG R j) (d := 0)
    (fun t => by have := hi' t; omega) (fun t => by have := hj' t; omega)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.add_apply]; omega)
    (fun t => by simp) (by simp)
  rw [rootsK_code h hR hi, rootsK_code h hR hj, offR_eq]
  show vecCode _ + vecCode _ - vecCode 0 = _
  omega

theorem rootsK_sum12 (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Nat.sub (Nat.add (nthV RC i) (Nat.add (nthV RC j) (nthV RC j))) (Nat.add offR offR) =
      vecCode (rootAtG R i + 2 • rootAtG R j) := by
  have hi' := rootAtG_bound h hR hi
  have hj' := rootAtG_bound h hR hj
  have k1 := vecCode_add_eq (a := rootAtG R i) (b := rootAtG R j)
    (c := rootAtG R i + rootAtG R j) (d := 0)
    (fun t => by have := hi' t; omega) (fun t => by have := hj' t; omega)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.add_apply]; omega)
    (fun t => by simp) (by simp)
  have k2 := vecCode_add_eq (a := rootAtG R i + rootAtG R j) (b := rootAtG R j)
    (c := rootAtG R i + 2 • rootAtG R j) (d := 0)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.add_apply]; omega)
    (fun t => by have := hj' t; omega)
    (fun t => by
      have := hi' t; have := hj' t
      simp only [Pi.add_apply, Pi.smul_apply]; simp only [nsmul_eq_mul, Nat.cast_ofNat]; omega)
    (fun t => by simp) (by ext t; simp; ring)
  rw [rootsK_code h hR hi, rootsK_code h hR hj, offR_eq]
  show vecCode _ + (vecCode _ + vecCode _) - (vecCode 0 + vecCode 0) = _
  omega

theorem rootsK_sum21 (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Nat.sub (Nat.add (Nat.add (nthV RC i) (nthV RC i)) (nthV RC j)) (Nat.add offR offR) =
      vecCode (2 • rootAtG R i + rootAtG R j) := by
  have hi' := rootAtG_bound h hR hi
  have hj' := rootAtG_bound h hR hj
  have k1 := vecCode_add_eq (a := rootAtG R i) (b := rootAtG R j)
    (c := rootAtG R i + rootAtG R j) (d := 0)
    (fun t => by have := hi' t; omega) (fun t => by have := hj' t; omega)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.add_apply]; omega)
    (fun t => by simp) (by simp)
  have k2 := vecCode_add_eq (a := rootAtG R i + rootAtG R j) (b := rootAtG R i)
    (c := 2 • rootAtG R i + rootAtG R j) (d := 0)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.add_apply]; omega)
    (fun t => by have := hi' t; omega)
    (fun t => by
      have := hi' t; have := hj' t
      simp only [Pi.add_apply, Pi.smul_apply]; simp only [nsmul_eq_mul, Nat.cast_ofNat]; omega)
    (fun t => by simp) (by ext t; simp; ring)
  rw [rootsK_code h hR hi, rootsK_code h hR hj, offR_eq]
  show (vecCode _ + vecCode _) + vecCode _ - (vecCode 0 + vecCode 0) = _
  omega

theorem rootsK_diff (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    Nat.sub (Nat.add (nthV RC j) offR) (nthV RC i) = vecCode (rootAtG R j - rootAtG R i) := by
  have hi' := rootAtG_bound h hR hi
  have hj' := rootAtG_bound h hR hj
  have key := vecCode_add_eq (a := rootAtG R j) (b := 0)
    (c := rootAtG R j - rootAtG R i) (d := rootAtG R i)
    (fun t => by have := hj' t; omega) (fun t => by simp)
    (fun t => by have := hi' t; have := hj' t; simp only [Pi.sub_apply]; omega)
    (fun t => by have := hi' t; omega) (by simp)
  rw [rootsK_code h hR hi, rootsK_code h hR hj, offR_eq]
  show vecCode _ + vecCode 0 - vecCode _ = _
  omega

private theorem idxR_rec (RC : List ℕ) (v : ℕ) (i : ℕ) :
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 48)
      (fun x _ ih i => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ i)) i (Nat.beq x v)) RC) i =
      if v ∈ RC then i + RC.idxOf v else 48 := by
  induction RC generalizing i with
  | nil => simp
  | cons x xs ih =>
    show Bool.rec (motive := fun _ => Nat)
      ((List.rec (motive := fun _ => Nat → Nat) (fun _ => 48)
        (fun x _ ih i => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ i)) i (Nat.beq x v)) xs)
          (Nat.succ i)) i (Nat.beq x v) = _
    cases hb : Nat.beq x v with
    | true =>
      have hx : x = v := Nat.eq_of_beq_eq_true hb
      subst hx
      simp
    | false =>
      have hx : x ≠ v := fun e => by rw [e, Nat.beq_refl] at hb; exact Bool.noConfusion hb
      dsimp only
      rw [ih (Nat.succ i)]
      have hx' : ¬ v = x := fun e => hx e.symm
      by_cases hv : v ∈ xs
      · simp [hv, hx, hx', List.idxOf_cons]
        omega
      · simp [hv, hx, hx']

private theorem idxR_eq_rec (RC : List ℕ) (v : ℕ) : idxR RC v =
    (List.rec (motive := fun _ => Nat → Nat) (fun _ => 48)
      (fun x _ ih i => Bool.rec (motive := fun _ => Nat) (ih (Nat.succ i)) i (Nat.beq x v)) RC) 0 :=
  letN_eq _ _

private theorem idxR_eq (hRC : RC.length = 48) (v : ℕ) : idxR RC v = RC.idxOf v := by
  rw [idxR_eq_rec, idxR_rec]
  by_cases hv : v ∈ RC
  · simp [hv]
  · rw [if_neg hv, List.idxOf_eq_length hv, hRC]

private theorem idxOf_congr {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (a0 : α) (b0 : β) (x : α) (y : β) :
    ∀ (A : List α) (B : List β), A.length = B.length →
      (∀ k < A.length, (A.getD k a0 = x ↔ B.getD k b0 = y)) → A.idxOf x = B.idxOf y := by
  intro A
  induction A with
  | nil =>
    intro B hB _
    cases B with
    | nil => rfl
    | cons b B => simp at hB
  | cons a A ih =>
    intro B hB hk
    cases B with
    | nil => simp at hB
    | cons b B =>
      have h0 := hk 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      have hB' : A.length = B.length := by simpa using hB
      have ih' := ih B hB' (fun k hk' => by
        have := hk (k + 1) (by simpa using hk')
        simpa [List.getD_cons_succ] using this)
      rw [List.idxOf_cons, List.idxOf_cons, ih']
      have : (a == x) = (b == y) := by
        rw [Bool.eq_iff_iff]; simpa using h0
      rw [this]

theorem idxR_vecCode (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {w : Fin Tag.F4.rank → ℤ}
    (hw : ∀ t, -32 ≤ w t ∧ w t ≤ 31) : idxR RC (vecCode w) = rootIdxG R w := by
  have hRC := (rootsK_spec h).2.1
  have hR48 := roots_length h hR
  rw [idxR_eq hRC]
  unfold rootIdxG
  refine idxOf_congr 0 [] _ _ RC R (by rw [hRC, hR48]) fun k hk => ?_
  rw [hRC] at hk
  have e1 : RC.getD k 0 = vecCode (rootAtG R k) := by
    rw [← nthV_eq]; exact rootsK_code h hR hk
  rw [e1, ← roots_ofFn h hR hk]
  constructor
  · intro e
    have := vecCode_inj (fun t => by have := rootAtG_bound h hR hk t; omega) hw e
    rw [this]
  · intro e
    have := List.ofFn_injective e
    rw [this]

theorem rootIdxG_lt_iff (hR48 : R.length = 48) (w : Fin Tag.F4.rank → ℤ) :
    rootIdxG R w < 48 ↔ isRootBG R w = true := by
  have := @List.idxOf_lt_length_iff _ _ _ R (List.ofFn w)
  rw [hR48] at this
  unfold rootIdxG isRootBG
  rw [this]
  simp

theorem rootIdxG_le (hR48 : R.length = 48) (w : Fin Tag.F4.rank → ℤ) : rootIdxG R w ≤ 48 := by
  have := @List.idxOf_le_length _ _ _ R (List.ofFn w)
  rw [hR48] at this
  exact this

theorem oppK_iff (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {i j : ℕ} (hi : i < 48) (hj : j < 48) :
    oppK RC i j = true ↔ rootAtG R i + rootAtG R j = 0 := by
  have hi' := rootAtG_bound h hR hi
  have hj' := rootAtG_bound h hR hj
  have k0 := vecCode_add_eq (a := -rootAtG R j) (b := rootAtG R j) (c := 0) (d := 0)
    (fun t => by have := hj' t; simp only [Pi.neg_apply]; omega)
    (fun t => by have := hj' t; omega) (fun t => by simp) (fun t => by simp) (by simp)
  show Nat.beq (nthV RC i + nthV RC j) (offR + offR) = true ↔ _
  rw [Nat.beq_eq, rootsK_code h hR hi, rootsK_code h hR hj, offR_eq]
  constructor
  · intro e
    have e' : vecCode (rootAtG R i) = vecCode (-rootAtG R j) := by omega
    have := vecCode_inj (fun t => by have := hi' t; omega)
      (fun t => by have := hj' t; simp only [Pi.neg_apply]; omega) e'
    rw [this]
    simp
  · intro e
    have := vecCode_add_eq (a := rootAtG R i) (b := rootAtG R j) (c := 0) (d := 0)
      (fun t => by have := hi' t; omega) (fun t => by have := hj' t; omega)
      (fun t => by simp) (fun t => by simp) (by rw [e]; simp)
    exact this

theorem rootsK_sum_eq_iff (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {p q k : ℕ} (hp : p < 48) (hq : q < 48)
    (hk : k < 48) :
    Nat.beq (Nat.sub (Nat.add (nthV RC p) (nthV RC q)) offR) (nthV RC k) = true ↔
      rootAtG R p + rootAtG R q = rootAtG R k := by
  have hp' := rootAtG_bound h hR hp
  have hq' := rootAtG_bound h hR hq
  have hk' := rootAtG_bound h hR hk
  rw [Nat.beq_eq, rootsK_sum h hR hp hq, rootsK_code h hR hk]
  constructor
  · intro e
    exact vecCode_inj (fun t => by have := hp' t; have := hq' t; simp only [Pi.add_apply]; omega)
      (fun t => by have := hk' t; omega) e
  · intro e
    rw [e]

theorem idxR_eq_48_iff (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {w : Fin Tag.F4.rank → ℤ}
    (hw : ∀ t, -32 ≤ w t ∧ w t ≤ 31) :
    Nat.beq (idxR RC (vecCode w)) 48 = true ↔ isRootBG R w = false := by
  rw [idxR_vecCode h hR hw, Nat.beq_eq]
  have hle := rootIdxG_le (roots_length h hR) w
  have hlt := rootIdxG_lt_iff (roots_length h hR) w
  cases hb : isRootBG R w
  · simp only [hb, Bool.false_eq_true, iff_false, not_lt] at hlt
    simp only [iff_true]
    omega
  · simp only [hb, iff_true] at hlt
    simp only [Bool.true_eq_false, iff_false]
    omega

theorem idxR_gt_47_iff (h : rootsK RL RC = true)
    (hR : R = RL.map (List.map fun n : ℕ => (n : ℤ) - 32)) {w : Fin Tag.F4.rank → ℤ}
    (hw : ∀ t, -32 ≤ w t ∧ w t ≤ 31) :
    Nat.blt 47 (idxR RC (vecCode w)) = !isRootBG R w := by
  rw [idxR_vecCode h hR hw]
  have hlt := rootIdxG_lt_iff (roots_length h hR) w
  cases hb : isRootBG R w
  · simp only [hb, Bool.false_eq_true, iff_false, not_lt] at hlt
    show Nat.blt 47 _ = true
    rw [Nat.blt_eq]
    omega
  · simp only [hb, iff_true] at hlt
    show Nat.blt 47 _ = false
    rw [Bool.eq_false_iff]
    intro e
    rw [Nat.blt_eq] at e
    omega

end Roots

end CFSG.KS.PK

end
