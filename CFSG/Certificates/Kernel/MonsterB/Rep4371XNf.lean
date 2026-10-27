module

public import Certificates.Data.Kernel.MonsterB.Rep4371XNf
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XRaw
public import CFSG.Certificates.Kernel.BabyMonster.PktDecode

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Trace6091 CFSG.KC.Rep4371Row CFSG.Monster.B
open CFSG.KC.BM.Pkt

@[expose] def coeffC (c : Nat) : Terms → Int
  | [] => 0
  | e :: L => (if e.1 = c then e.2 else 0) + coeffC c L

theorem coeffC_nil (c : Nat) : coeffC c [] = 0 := rfl

theorem coeffC_cons (c : Nat) (e : Nat × Int) (L : Terms) :
    coeffC c (e :: L) = (if e.1 = c then e.2 else 0) + coeffC c L := rfl

theorem coeffC_append (c : Nat) (L M : Terms) : coeffC c (L ++ M) = coeffC c L + coeffC c M := by
  induction L with
  | nil => rw [List.nil_append, coeffC_nil, Int.zero_add]
  | cons e L ih => rw [List.cons_append, coeffC_cons, coeffC_cons, ih, Int.add_assoc]

theorem coeffC_scaleT (c : Nat) (m : Int) (L : Terms) : coeffC c (scaleT m L) = m * coeffC c L := by
  rw [scaleT_eq]
  induction L with
  | nil => rw [List.map_nil, coeffC_nil, Int.mul_zero]
  | cons e L ih =>
    rw [List.map_cons, coeffC_cons, coeffC_cons, ih, Int.mul_add]
    by_cases h : e.1 = c
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, Int.mul_zero]

theorem actVecT_cons (g : Nat → Terms) (e : Nat × Int) (L : Terms) :
    actVecT g (e :: L) = appT (scaleT e.2 (g e.1)) (actVecT g L) := rfl

theorem coeffC_actVecT_append (c : Nat) (g : Nat → Terms) (L M : Terms) :
    coeffC c (actVecT g (L ++ M)) = coeffC c (actVecT g L) + coeffC c (actVecT g M) := by
  induction L with
  | nil => rw [List.nil_append]
           exact (Int.zero_add _).symm
  | cons e L ih =>
    rw [List.cons_append, actVecT_cons, actVecT_cons, appT_eq, appT_eq, coeffC_append, coeffC_append,
      ih, Int.add_assoc]

theorem coeffC_actVecT_reverse (c : Nat) (g : Nat → Terms) (L : Terms) :
    coeffC c (actVecT g L.reverse) = coeffC c (actVecT g L) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have e0 : actVecT g [] = [] := rfl
    rw [List.reverse_cons, coeffC_actVecT_append, ih, actVecT_cons, actVecT_cons, appT_eq, appT_eq,
      coeffC_append, coeffC_append, e0, coeffC_nil]
    omega

theorem isZI_true {m : Int} (h : isZI m = true) : m = 0 := by
  cases m with
  | ofNat n =>
    have : n = 0 := Nat.eq_of_beq_eq_true h
    rw [this]
    rfl
  | negSucc n => exact Bool.noConfusion h

theorem nilB_eq {L : Terms} (h : nilB L = true) : L = [] := by
  cases L with
  | nil => rfl
  | cons e L => exact Bool.noConfusion h

theorem insT_cons (a : Nat) (m : Int) (e : Nat × Int) (rest : Terms) :
    insT a m (e :: rest) = Bool.rec (motive := fun _ => Terms)
      (Bool.rec (motive := fun _ => Terms) (e :: insT a m rest)
        (Bool.rec (motive := fun _ => Terms) ((a, m + e.2) :: rest) rest (isZI (m + e.2)))
        (Nat.beq a e.1))
      ((a, m) :: e :: rest) (Nat.blt a e.1) := rfl

theorem coeffC_insT (c a : Nat) (m : Int) (L : Terms) :
    coeffC c (insT a m L) = (if a = c then m else 0) + coeffC c L := by
  induction L with
  | nil => rfl
  | cons e rest ih =>
    rw [insT_cons]
    cases hlt : Nat.blt a e.1
    · cases hbeq : Nat.beq a e.1
      · change coeffC c (e :: insT a m rest) = _
        rw [coeffC_cons, ih, coeffC_cons, Int.add_left_comm]
      · have hae : a = e.1 := Nat.eq_of_beq_eq_true hbeq
        cases hz : isZI (m + e.2)
        · change coeffC c ((a, m + e.2) :: rest) = _
          rw [coeffC_cons, coeffC_cons, ← hae, ← Int.add_assoc]
          by_cases h : a = c
          · rw [if_pos h, if_pos h, if_pos h]
          · rw [if_neg h, if_neg h, if_neg h]
            omega
        · change coeffC c rest = _
          have h0 := isZI_true hz
          rw [coeffC_cons, ← hae, ← Int.add_assoc]
          by_cases h : a = c
          · rw [if_pos h, if_pos h, h0]
            omega
          · rw [if_neg h, if_neg h]
            omega
    · rfl

theorem coeffC_nfT (c : Nat) (L : Terms) : coeffC c (nfT L) = coeffC c L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    change coeffC c (strictL e.1 fun a => insT a e.2 (nfT L)) = _
    rw [strictL_eq, coeffC_insT, ih, coeffC_cons]

theorem coeffOf_td (κ : Nat) (L : Terms) : Model.coeffOf (kd κ) (L.map td) = coeffC κ L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.map_cons, coeffC_cons, ← ih]
    change (if kd e.1 = kd κ then e.2 else 0) + Model.coeffOf (kd κ) (L.map td) = _
    by_cases h : e.1 = κ
    · rw [if_pos h, if_pos (congrArg kd h)]
    · rw [if_neg h, if_neg (fun h' => h (kd_inj h'))]

theorem eqModel_of_coeff {D₁ D₂ : Int} {A B : Terms} (h : ∀ c, coeffC c A * D₂ = coeffC c B * D₁) :
    Model.eqModel D₁ (A.map td) D₂ (B.map td) = true := by
  unfold Model.eqModel
  rw [List.all_eq_true]
  have key : ∀ t : Nat × Int,
      (Model.coeffOf (td t).1 (A.map td) * D₂ == Model.coeffOf (td t).1 (B.map td) * D₁) = true := by
    intro t
    change (Model.coeffOf (kd t.1) (A.map td) * D₂ == Model.coeffOf (kd t.1) (B.map td) * D₁) = true
    rw [coeffOf_td, coeffOf_td]
    exact beq_iff_eq.mpr (h t.1)
  intro e he
  rw [List.mem_append, List.mem_map, List.mem_map] at he
  rcases he with ⟨t, -, rfl⟩ | ⟨t, -, rfl⟩ <;> exact key t

theorem eqModel_of_nf {D₁ D₂ : Int} {L₁ L₂ : Terms}
    (h : nfT (scaleT D₂ L₁) = nfT (scaleT D₁ L₂)) :
    Model.eqModel D₁ (L₁.map td) D₂ (L₂.map td) = true := by
  refine eqModel_of_coeff fun c => ?_
  have e := congrArg (coeffC c) h
  rw [coeffC_nfT, coeffC_nfT, coeffC_scaleT, coeffC_scaleT] at e
  rw [Int.mul_comm, e, Int.mul_comm]

@[expose] def rowP (f : Nat → Terms) (TH k : Nat) (R : Terms) : Prop :=
  ∀ c, coeffC c (actVecT f (rawT TH k)) = 8 * coeffC c (actVecT (rawT TH) R)

theorem rowChk_sound {f : Nat → Terms} {TH k : Nat} {R : Terms} (h : rowChk f TH k R = true) :
    rowP f TH k R := by
  intro c
  have h0 : nfT (appT (actVecT f (rawT TH k)) (scaleT (Int.negSucc 7) (actVecT (rawT TH) R))) = [] :=
    nilB_eq h
  have e := coeffC_nfT c (appT (actVecT f (rawT TH k)) (scaleT (Int.negSucc 7) (actVecT (rawT TH) R)))
  rw [h0, coeffC_nil, appT_eq, coeffC_append, coeffC_scaleT] at e
  have e8 : Int.negSucc 7 = -8 := rfl
  rw [e8] at e
  omega

theorem rowP_of_reverse {f : Nat → Terms} {TH k : Nat} {R : Terms} (h : rowP f TH k R.reverse) :
    rowP f TH k R := by
  intro c
  rw [← coeffC_actVecT_reverse c (rawT TH) R]
  exact h c

theorem rowOK_of_rowP {TH : Nat} (hTH : thOK TH = true) {act : Model.Key → List (Model.Key × Int)}
    {f : Nat → Terms} (hf : ∀ κ, act (kd κ) = (f κ).map td) {row : Array (Nat × Int)} {k : Nat}
    (h : rowP f TH k row.toList) : Model.rowOK act row k = true := by
  unfold Model.rowOK
  rw [rawModel_eq hTH, actVecT_eq hf, rowModel_eq hTH]
  refine eqModel_of_coeff fun c => ?_
  rw [h c]
  omega

theorem numT_eq : ∀ c < 8, numT c = CFSG.Monster.B.Native.numOfCode c := by
  decide +kernel

theorem scStep_eq (f : Nat → Terms) (TH : Nat) (st : Nat × Terms × Bool) (v : Nat) :
    scStep f TH st v = Bool.rec (motive := fun _ => Nat × Terms × Bool)
      (st.1, (v % 8192, numT (v / 8192 % 8)) :: st.2.1, st.2.2)
      (st.1 + 1, [], st.2.2 && rowChk f TH st.1 ((v % 8192, numT (v / 8192 % 8)) :: st.2.1))
      (Nat.beq (v / 65536) 1) := by
  obtain ⟨k, acc, ok⟩ := st
  cases ok <;> rfl

theorem scStep_end {f : Nat → Terms} {TH : Nat} {st : Nat × Terms × Bool} {v : Nat}
    (h : v / 65536 = 1) : scStep f TH st v =
      (st.1 + 1, [], st.2.2 && rowChk f TH st.1 ((v % 8192, numT (v / 8192 % 8)) :: st.2.1)) := by
  have hb : Nat.beq (v / 65536) 1 = true := by
    rw [h]
    rfl
  rw [scStep_eq, hb]

theorem scStep_mid {f : Nat → Terms} {TH : Nat} {st : Nat × Terms × Bool} {v : Nat}
    (h : v / 65536 ≠ 1) :
    scStep f TH st v = (st.1, (v % 8192, numT (v / 8192 % 8)) :: st.2.1, st.2.2) := by
  have hb : Nat.beq (v / 65536) 1 = false := by
    cases e : Nat.beq (v / 65536) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h
  rw [scStep_eq, hb]

@[expose] def ScInv (f : Nat → Terms) (TH : Nat) (rr : Array (Array (Nat × Int)) × Array (Nat × Int))
    (st : Nat × Terms × Bool) : Prop :=
  st.1 = rr.1.size ∧ st.2.1 = rr.2.toList.reverse ∧
    (st.2.2 = true → ∀ j < rr.1.size, rowP f TH j (rr.1[j]!).toList)

theorem scInv_step {f : Nat → Terms} {TH : Nat} {rr : Array (Array (Nat × Int)) × Array (Nat × Int)}
    {st : Nat × Terms × Bool} (h : ScInv f TH rr st) (v : Nat) :
    ScInv f TH (entStep rr v) (scStep f TH st v) := by
  obtain ⟨e1, e2, e3⟩ := h
  have ht : numT (v / 8192 % 8) = CFSG.Monster.B.Native.numOfCode (v / 8192 % 8) :=
    numT_eq _ (Nat.mod_lt _ (by decide))
  by_cases hv : v / 65536 = 1
  · rw [scStep_end hv, ht]
    have ex : entStep rr v =
        (rr.1.push (rr.2.push (v % 8192, CFSG.Monster.B.Native.numOfCode (v / 8192 % 8))), #[]) := by
      unfold entStep
      rw [if_pos hv]
    rw [ex]
    refine ⟨by rw [Array.size_push, e1], rfl, ?_⟩
    intro hok j hj
    rw [Bool.and_eq_true] at hok
    obtain ⟨hok1, hok2⟩ := hok
    rw [Array.size_push] at hj
    change rowP f TH j ((rr.1.push _)[j]!).toList
    rw [CFSG.KC.BM.Pkt.getElem!_push]
    by_cases h1 : j < rr.1.size
    · rw [if_pos h1]
      exact e3 hok1 j h1
    · have h2 : j = rr.1.size := by omega
      rw [if_neg h1, if_pos h2]
      apply rowP_of_reverse
      rw [Array.toList_push, List.reverse_append, List.reverse_singleton, List.singleton_append, ← e2,
        h2, ← e1]
      exact rowChk_sound hok2
  · rw [scStep_mid hv, ht]
    have ex : entStep rr v =
        (rr.1, rr.2.push (v % 8192, CFSG.Monster.B.Native.numOfCode (v / 8192 % 8))) := by
      unfold entStep
      rw [if_neg hv]
    rw [ex]
    refine ⟨e1, ?_, e3⟩
    change _ :: st.2.1 = (rr.2.push _).toList.reverse
    rw [Array.toList_push, List.reverse_append, List.reverse_singleton, List.singleton_append, e2]

theorem scInv_foldl {f : Nat → Terms} {TH : Nat} : ∀ (vs : List Nat)
    (rr : Array (Array (Nat × Int)) × Array (Nat × Int)) (st : Nat × Terms × Bool),
    ScInv f TH rr st → ScInv f TH (vs.foldl entStep rr) (vs.foldl (scStep f TH) st)
  | [], _, _, h => h
  | v :: vs, _, _, h => scInv_foldl vs _ _ (scInv_step h v)

theorem scanR_succ (f : Nat → Terms) (TH N i m : Nat) (st : Nat × Terms × Bool) :
    scanR f TH N i (m + 1) st = scStep f TH (scanR f TH N i m st) (entV N (i + m)) := rfl

theorem scanR_foldl (f : Nat → Terms) (TH N : Nat) (st : Nat × Terms × Bool) : ∀ n : Nat,
    scanR f TH N 0 n st = ((List.range n).map (entV N)).foldl (scStep f TH) st
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, ← scanR_foldl f TH N st n, scanR_succ,
      Nat.zero_add]
    rfl

theorem scanR_add (f : Nat → Terms) (TH N i m₁ : Nat) (st : Nat × Terms × Bool) : ∀ m₂ : Nat,
    scanR f TH N i (m₁ + m₂) st = scanR f TH N (i + m₁) m₂ (scanR f TH N i m₁ st)
  | 0 => rfl
  | m₂ + 1 => by
    rw [← Nat.add_assoc, scanR_succ, scanR_succ, scanR_add f TH N i m₁ st m₂, Nat.add_assoc]

theorem chunkOK_eq {f : Nat → Terms} {TH N i m k₀ k₁ : Nat} (h : chunkOK f TH N i m k₀ k₁ = true) :
    scanR f TH N i m (k₀, [], true) = (k₁, [], true) := by
  unfold chunkOK at h
  generalize scanR f TH N i m (k₀, [], true) = st at h ⊢
  obtain ⟨a, L, ok⟩ := st
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false ok (nilB L)) (Nat.beq a k₁) = true at h
  cases hb : Nat.beq a k₁
  · rw [hb] at h
    change false = true at h
    exact Bool.noConfusion h
  rw [hb] at h
  cases hn : nilB L
  · rw [hn] at h
    change false = true at h
    exact Bool.noConfusion h
  rw [hn] at h
  change ok = true at h
  rw [Nat.eq_of_beq_eq_true hb, nilB_eq hn, h]

theorem chunks_scan {f : Nat → Terms} {TH N : Nat} {S K : Nat → Nat} (hS0 : S 0 = 0) (hK0 : K 0 = 0) :
    ∀ n : Nat, (∀ c < n, S c ≤ S (c + 1)) →
      (∀ c < n, chunkOK f TH N (S c) (S (c + 1) - S c) (K c) (K (c + 1)) = true) →
      scanR f TH N 0 (S n) (0, [], true) = (K n, [], true)
  | 0, _, _ => by
    rw [hS0, hK0]
    rfl
  | n + 1, hS, hc => by
    have e := chunks_scan hS0 hK0 n (fun c h => hS c (by omega)) (fun c h => hc c (by omega))
    have hle := hS n (by omega)
    have hsplit : S (n + 1) = S n + (S (n + 1) - S n) := by omega
    rw [hsplit, scanR_add, e, Nat.zero_add]
    exact chunkOK_eq (hc n (by omega))

theorem scan_rows {f : Nat → Terms} {TH : Nat} {p : Nat × Nat}
    (h : scanR f TH p.1 0 (p.2 / 3) (0, [], true) = (4371, [], true)) :
    (lineRows p).size = 4371 ∧ ∀ k < 4371, rowP f TH k ((lineRows p)[k]!).toList := by
  rw [scanR_foldl] at h
  have hI : ScInv f TH (#[], #[]) (0, [], true) :=
    ⟨rfl, rfl, fun _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hF := scInv_foldl ((List.range (p.2 / 3)).map (entV p.1)) _ _ hI
  rw [h] at hF
  obtain ⟨e1, -, e3⟩ := hF
  unfold lineRows
  exact ⟨e1.symm, fun k hk => e3 rfl k (e1 ▸ hk)⟩

theorem genOK_of_scan {TH : Nat} (hTH : thOK TH = true) {act : Model.Key → List (Model.Key × Int)}
    {f : Nat → Terms} (hf : ∀ κ, act (kd κ) = (f κ).map td) {p : Nat × Nat}
    (h : scanR f TH p.1 0 (p.2 / 3) (0, [], true) = (4371, [], true)) :
    Model.genOK act (lineRows p) = true := by
  unfold Model.genOK
  rw [List.all_eq_true]
  intro k hk
  exact rowOK_of_rowP hTH hf ((scan_rows h).2 k (List.mem_range.1 hk))

theorem genOK_of_lineChk {TH : Nat} (hTH : thOK TH = true) {act : Model.Key → List (Model.Key × Int)}
    {f : Nat → Terms} (hf : ∀ κ, act (kd κ) = (f κ).map td) {p : Nat × Nat}
    (h : lineChk f TH p = true) : Model.genOK act (lineRows p) = true :=
  genOK_of_scan hTH hf (chunkOK_eq h)

end CFSG.KC.Rep4371X

end
