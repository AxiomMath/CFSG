module

public import Mathlib.Data.Nat.Notation
public import Certificates.Data.Kernel.LocalQT.PairsH

public section

namespace CFSG.KC.LQT.PHSnd

open CFSG.KC.LQT.PH

private theorem andB_iff {a b : Bool} :
    CFSG.KC.Ord.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [CFSG.KC.Ord.andB]

private theorem orB_iff {a b : Bool} :
    CFSG.KC.Ord.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [CFSG.KC.Ord.orB]

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem allN_iff (m : ℕ) (f : ℕ → Bool) :
    CFSG.KC.LQT.P.allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    change CFSG.KC.Ord.andB (f m) (CFSG.KC.LQT.P.allN m f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hi' : i = m
      · subst hi'
        exact h1
      · exact h2 i (by omega)
    · intro h
      exact ⟨h m (by omega), fun i hi => h i (by omega)⟩

private theorem allL_iff (L : List ℕ) (f : ℕ → Bool) :
    CFSG.KC.LQT.P.allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [CFSG.KC.LQT.P.allL]
  | cons x L ih =>
    change CFSG.KC.Ord.andB (f x) (CFSG.KC.LQT.P.allL L f) = true ↔ _
    rw [andB_iff, ih]
    simp

private theorem getK_syl {α : Type} (l : List α) (i : ℕ) (d : α) :
    CFSG.KC.LQT.Syl.getK l i d = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih i

private theorem getK_nat : ∀ (l : List ℕ) (i : ℕ), CFSG.KC.LQT.S.getK l i = l.getD i 0
  | [], _ => rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => ℕ) (CFSG.KC.LQT.S.getK l (Nat.sub i 1)) x
      (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      change CFSG.KC.LQT.S.getK l (i + 1 - 1) = _
      rw [Nat.add_sub_cancel, getK_nat l i, List.getD_cons_succ]

private theorem lenL_eq : ∀ l : List ℕ, CFSG.KC.LQT.S.lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenL_eq l)

private theorem lenA_eq {α : Type} : ∀ l : List α, CFSG.KC.LQT.L.lenA l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenA_eq l)

private theorem memL_iff (y : ℕ) : ∀ l : List ℕ, CFSG.KC.LQT.S.memL y l = true ↔ y ∈ l
  | [] => by simp [CFSG.KC.LQT.S.memL]
  | x :: l => by
    change CFSG.KC.Ord.orB (Nat.beq y x) (CFSG.KC.LQT.S.memL y l) = true ↔ _
    rw [orB_iff, beq_iff, memL_iff y l, List.mem_cons]

private theorem flatB_nil : flatB [] = [] := rfl

private theorem flatB_cons (b : Blk) (t : List Blk) : flatB (b :: t) = b.2 ++ flatB t := rfl

private theorem memB_sound (y : ℕ) : ∀ B : List Blk, memB y B = true → y ∈ flatB B
  | [], h => by
    have h' : false = true := h
    exact absurd h' Bool.false_ne_true
  | b :: B, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memB y B) (CFSG.KC.LQT.S.memL y b.2)
        (Nat.ble y b.1) = true := h
    rw [flatB_cons, List.mem_append]
    cases hb : Nat.ble y b.1 with
    | false =>
      rw [hb] at h'
      exact Or.inr (memB_sound y B h')
    | true =>
      rw [hb] at h'
      exact Or.inl ((memL_iff y b.2).1 h')

private theorem mem_flatB {y : ℕ} : ∀ B : List Blk, y ∈ flatB B →
    ∃ j < B.length, ∃ i < ((B.getD j (0, [])).2).length,
      ((B.getD j (0, [])).2).getD i 0 = y
  | [], h => by
    rw [flatB_nil] at h
    exact absurd h List.not_mem_nil
  | b :: t, h => by
    rw [flatB_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
      refine ⟨0, Nat.succ_pos _, i, ?_, ?_⟩
      · rw [List.getD_cons_zero]
        exact hi
      · rw [List.getD_cons_zero]
        simp [hi]
    · obtain ⟨j, hj, i, hi, e⟩ := mem_flatB t h
      refine ⟨j + 1, Nat.succ_lt_succ hj, i, ?_, ?_⟩
      · rw [List.getD_cons_succ]
        exact hi
      · rw [List.getD_cons_succ]
        exact e

private noncomputable def sincR (l : List ℕ) : Option ℕ → Bool :=
  List.rec (motive := fun _ => Option ℕ → Bool) (fun _ => true)
    (fun x _ ih o => CFSG.KC.Ord.andB (Option.rec (motive := fun _ => Bool) true
      (fun y => Nat.blt y x) o) (ih (some x))) l

private theorem sincR_pairwise : ∀ (l : List ℕ) (o : Option ℕ), sincR l o = true →
    l.Pairwise (· < ·) ∧ ∀ y ∈ o, ∀ x ∈ l, y < x
  | [], _, _ => ⟨List.Pairwise.nil, fun _ _ _ hx => absurd hx List.not_mem_nil⟩
  | x :: l, o, h => by
    have h' : CFSG.KC.Ord.andB (Option.rec (motive := fun _ => Bool) true
        (fun y => Nat.blt y x) o) (sincR l (some x)) = true := h
    rw [andB_iff] at h'
    obtain ⟨hl, hlt⟩ := sincR_pairwise l (some x) h'.2
    refine ⟨List.Pairwise.cons (fun z hz => hlt x rfl z hz) hl, ?_⟩
    intro y hy z hz
    cases o with
    | none => exact absurd hy (by simp)
    | some y' =>
      have hy' : y' = y := Option.some.inj hy
      subst hy'
      have hyx : y' < x := blt_iff.mp h'.1
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hyx
      · exact Nat.lt_trans hyx (hlt x rfl z hz)

private noncomputable def lenOK (s : ℕ) (B : List Blk) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b t ih => CFSG.KC.Ord.andB (Bool.rec (motive := fun _ => Bool)
      (Nat.beq (CFSG.KC.LQT.S.lenL b.2) s) (Nat.ble (CFSG.KC.LQT.S.lenL b.2) s)
      (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t)) ih) B

private theorem lenOK_nil {s : ℕ} {b : Blk} (h : lenOK s [b] = true) : b.2.length ≤ s := by
  have h' : CFSG.KC.Ord.andB (Nat.ble (CFSG.KC.LQT.S.lenL b.2) s) true = true := h
  rw [andB_iff, lenL_eq] at h'
  exact Nat.le_of_ble_eq_true h'.1

private theorem lenOK_cons {s : ℕ} {b c : Blk} {t : List Blk} (h : lenOK s (b :: c :: t) = true) :
    b.2.length = s ∧ lenOK s (c :: t) = true := by
  have h' : CFSG.KC.Ord.andB (Nat.beq (CFSG.KC.LQT.S.lenL b.2) s) (lenOK s (c :: t)) = true := h
  rw [andB_iff, beq_iff, lenL_eq] at h'
  exact h'

private theorem shape {s : ℕ} : ∀ (B : List Blk), lenOK s B = true → ∀ p < (flatB B).length,
    0 < s ∧ p / s < B.length ∧ p % s < ((B.getD (p / s) (0, [])).2).length
  | [], _, p, hp => by
    rw [flatB_nil, List.length_nil] at hp
    exact absurd hp (Nat.not_lt_zero p)
  | [b], h, p, hp => by
    have hb := lenOK_nil h
    have hp' : p < b.2.length := by
      rw [flatB_cons, flatB_nil, List.append_nil] at hp
      exact hp
    have h0 : p / s = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : p % s = p := Nat.mod_eq_of_lt (by omega)
    rw [h0, h1]
    refine ⟨by omega, by simp, ?_⟩
    rw [List.getD_cons_zero]
    exact hp'
  | b :: c :: t, h, p, hp => by
    obtain ⟨hb, h'⟩ := lenOK_cons h
    rw [flatB_cons, List.length_append] at hp
    by_cases hps : p < s
    · have h0 : p / s = 0 := Nat.div_eq_of_lt hps
      have h1 : p % s = p := Nat.mod_eq_of_lt hps
      rw [h0, h1]
      refine ⟨by omega, by simp, ?_⟩
      rw [List.getD_cons_zero, hb]
      exact hps
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + s := ⟨p - s, by omega⟩
      have hq : q < (flatB (c :: t)).length := by omega
      obtain ⟨hs, h2, h3⟩ := shape (c :: t) h' q hq
      rw [Nat.add_div_right q hs, Nat.add_mod_right q s]
      refine ⟨hs, Nat.succ_lt_succ h2, ?_⟩
      rw [List.getD_cons_succ]
      exact h3

private theorem zipB_spec (f : ℕ → ℕ × ℕ × ℕ → Bool) :
    ∀ (l : List ℕ) (t : List (ℕ × ℕ × ℕ)), zipB l t f = true →
      l.length = t.length ∧ ∀ i < l.length, f (l.getD i 0) (t.getD i (0, 0, 0)) = true
  | [], t, h => by
    cases t with
    | nil => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | cons e t =>
      have h' : false = true := h
      exact absurd h' Bool.false_ne_true
  | x :: l, t, h => by
    cases t with
    | nil =>
      have h' : false = true := h
      exact absurd h' Bool.false_ne_true
    | cons e t =>
      have h' : CFSG.KC.Ord.andB (f x e) (zipB l t f) = true := h
      rw [andB_iff] at h'
      obtain ⟨hlen, hall⟩ := zipB_spec f l t h'.2
      refine ⟨congrArg Nat.succ hlen, fun i hi => ?_⟩
      cases i with
      | zero =>
        rw [List.getD_cons_zero, List.getD_cons_zero]
        exact h'.1
      | succ i =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact hall i (Nat.lt_of_succ_lt_succ hi)

private theorem getB_eq (B : List Blk) (s p : ℕ) :
    getB B s p = ((B.getD (p / s) (0, [])).2).getD (p % s) 0 := by
  show CFSG.KC.LQT.S.getK (CFSG.KC.LQT.Syl.getK B (p / s) (0, [])).2 (p % s) = _
  rw [getK_syl, getK_nat]

private theorem getT_eq (T : List (List (ℕ × ℕ × ℕ))) (s p : ℕ) :
    getT T s p = (T.getD (p / s) []).getD (p % s) (0, 0, 0) := by
  show CFSG.KC.LQT.Syl.getK (CFSG.KC.LQT.Syl.getK T (p / s) []) (p % s) (0, 0, 0) = _
  rw [getK_syl, getK_syl]

private noncomputable def entOK (op : ℕ → ℕ → ℕ) (z : ℕ) (G : List ℕ) (s N : ℕ) (B : List Blk)
    (T : List (List (ℕ × ℕ × ℕ))) (x : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  CFSG.KC.Ord.andB (CFSG.KC.LQT.P.allL G fun g => memB (op g x) B)
    (Bool.rec (motive := fun _ => Bool)
      (CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt e.1 N)
          (Nat.blt e.2.1 (CFSG.KC.LQT.S.lenL G)))
        (CFSG.KC.Ord.andB (Nat.beq (op (CFSG.KC.LQT.S.getK G e.2.1) (getB B s e.1)) x)
          (Nat.beq (Nat.succ (getT T s e.1).2.2) e.2.2)))
      (Nat.beq x z) (Nat.beq e.2.2 0))

private abbrev Good (op : ℕ → ℕ → ℕ) (z : ℕ) (G : List ℕ) (s N : ℕ) (B : List Blk)
    (T : List (List (ℕ × ℕ × ℕ))) (x : ℕ) (e : ℕ × ℕ × ℕ) : Prop :=
  (∀ g ∈ G, memB (op g x) B = true) ∧ (e.2.2 = 0 → x = z) ∧
    (e.2.2 ≠ 0 → e.1 < N ∧ e.2.1 < G.length ∧
      op (G.getD e.2.1 0) (((B.getD (e.1 / s) (0, [])).2).getD (e.1 % s) 0) = x ∧
      ((T.getD (e.1 / s) []).getD (e.1 % s) (0, 0, 0)).2.2 + 1 = e.2.2)

private theorem ent_spec {op : ℕ → ℕ → ℕ} {z : ℕ} {G : List ℕ} {s N : ℕ} {B : List Blk}
    {T : List (List (ℕ × ℕ × ℕ))} {x : ℕ} {e : ℕ × ℕ × ℕ}
    (h : entOK op z G s N B T x e = true) : Good op z G s N B T x e := by
  unfold entOK at h
  rw [andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨(allL_iff _ _).1 h1, fun hd => ?_, fun hd => ?_⟩
  · have hb : Nat.beq e.2.2 0 = true := beq_iff.2 hd
    rw [hb] at h2
    exact beq_iff.1 h2
  · cases hb : Nat.beq e.2.2 0 with
    | true => exact absurd (beq_iff.1 hb) hd
    | false =>
      rw [hb] at h2
      have h2' : CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt e.1 N)
          (Nat.blt e.2.1 (CFSG.KC.LQT.S.lenL G)))
          (CFSG.KC.Ord.andB (Nat.beq (op (CFSG.KC.LQT.S.getK G e.2.1) (getB B s e.1)) x)
            (Nat.beq (Nat.succ (getT T s e.1).2.2) e.2.2)) = true := h2
      rw [andB_iff, andB_iff, andB_iff, blt_iff, blt_iff, beq_iff, beq_iff, lenL_eq] at h2'
      obtain ⟨⟨h3, h4⟩, h5, h6⟩ := h2'
      rw [getK_nat, getB_eq] at h5
      rw [getT_eq] at h6
      exact ⟨h3, h4, h5, h6⟩

private theorem blkOK_spec {op : ℕ → ℕ → ℕ} {z : ℕ} {G : List ℕ} {s N : ℕ} {B : List Blk}
    {T : List (List (ℕ × ℕ × ℕ))} {j : ℕ} (h : blkOK op z G s N B T j = true) :
    ∀ i < ((B.getD j (0, [])).2).length,
      Good op z G s N B T (((B.getD j (0, [])).2).getD i 0) ((T.getD j []).getD i (0, 0, 0)) := by
  have h' : zipB (CFSG.KC.LQT.Syl.getK B j (0, [])).2 (CFSG.KC.LQT.Syl.getK T j [])
      (entOK op z G s N B T) = true := h
  rw [getK_syl, getK_syl] at h'
  obtain ⟨-, hall⟩ := zipB_spec _ _ _ h'
  exact fun i hi => ent_spec (hall i hi)

private theorem reach {op : ℕ → ℕ → ℕ} {z : ℕ} {G : List ℕ} {s N : ℕ} {B : List Blk}
    {T : List (List (ℕ × ℕ × ℕ))} (hN : N = (flatB B).length) (hlen : lenOK s B = true)
    (hblk : ∀ j < B.length, blkOK op z G s N B T j = true) :
    ∀ d j : ℕ, j < B.length → ∀ i < ((B.getD j (0, [])).2).length,
      ((T.getD j []).getD i (0, 0, 0)).2.2 = d →
      ∃ w : List ℕ, (∀ k ∈ w, k < G.length) ∧
        w.foldr (fun k y => op (G.getD k 0) y) z = ((B.getD j (0, [])).2).getD i 0 := by
  subst hN
  intro d
  induction d with
  | zero =>
    intro j hj i hi hd
    obtain ⟨-, h2, -⟩ := blkOK_spec (hblk j hj) i hi
    exact ⟨[], fun k hk => absurd hk List.not_mem_nil, (h2 hd).symm⟩
  | succ d ih =>
    intro j hj i hi hd
    obtain ⟨-, -, h3⟩ := blkOK_spec (hblk j hj) i hi
    obtain ⟨hp, hl, hop, hdep⟩ := h3 (by omega)
    obtain ⟨-, hj', hi'⟩ := shape B hlen _ hp
    obtain ⟨w, hw, hwe⟩ := ih _ hj' _ hi' (by omega)
    refine ⟨((T.getD j []).getD i (0, 0, 0)).2.1 :: w, ?_, ?_⟩
    · intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact hl
      · exact hw k hk
    · rw [List.foldr_cons, hwe]
      exact hop

theorem orbit_cert {op : ℕ → ℕ → ℕ} {z : ℕ} {G : List ℕ} {s K : ℕ} {B : List Blk}
    {T : List (List (ℕ × ℕ × ℕ))} (hS : sortedB s B = true) (hz : memB z B = true)
    (hb : ∀ k < K, blkRange op z G s (CFSG.KC.LQT.S.lenL (flatB B)) B T (k * 8) 8 = true)
    (hK : CFSG.KC.LQT.L.lenA B ≤ K * 8) :
    (flatB B).Pairwise (· < ·) ∧ z ∈ flatB B ∧
      (∀ y ∈ flatB B, ∀ g ∈ G, op g y ∈ flatB B) ∧
      ∀ y ∈ flatB B, ∃ w : List ℕ, (∀ i ∈ w, i < G.length) ∧
        w.foldr (fun i y => op (G.getD i 0) y) z = y := by
  have hS' := hS
  unfold sortedB at hS'
  rw [andB_iff, andB_iff] at hS'
  obtain ⟨h1, -, h3⟩ := hS'
  have hlen : lenOK s B = true := h3
  have hblk : ∀ j < B.length,
      blkOK op z G s (CFSG.KC.LQT.S.lenL (flatB B)) B T j = true := by
    intro j hj
    have hA : CFSG.KC.LQT.L.lenA B = B.length := lenA_eq B
    have h8 : blkRange op z G s (CFSG.KC.LQT.S.lenL (flatB B)) B T (j / 8 * 8) 8 = true :=
      hb (j / 8) (by omega)
    unfold blkRange at h8
    rw [allN_iff] at h8
    have h9 : blkOK op z G s (CFSG.KC.LQT.S.lenL (flatB B)) B T
        (Nat.add (j / 8 * 8) (j % 8)) = true := h8 (j % 8) (by omega)
    have e : Nat.add (j / 8 * 8) (j % 8) = j := by
      show j / 8 * 8 + j % 8 = j
      omega
    rwa [e] at h9
  have hN : CFSG.KC.LQT.S.lenL (flatB B) = (flatB B).length := lenL_eq _
  refine ⟨(sincR_pairwise (flatB B) none h1).1, memB_sound z B hz, ?_, ?_⟩
  · intro y hy g hg
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_flatB B hy
    exact memB_sound _ B ((blkOK_spec (hblk j hj) i hi).1 g hg)
  · intro y hy
    obtain ⟨j, hj, i, hi, rfl⟩ := mem_flatB B hy
    exact reach hN hlen hblk _ j hj i hi rfl

end CFSG.KC.LQT.PHSnd

end
