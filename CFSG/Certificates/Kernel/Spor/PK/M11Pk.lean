module

public import CFSG.Certificates.Kernel.Spor.PK.Congr
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11

@[expose] def m11Bs : List Nat := [0, 1, 2, 3]

@[expose] def m11Run (LT i : Nat) : BS :=
  BS.run (letF 11 4 LT) (lvAt (letF 11 4 LT) 12 m11Bs i) 11 i

theorem m11Lev_eq {LT : Nat} (hL : ∀ l < 12, IsPermN 11 (letF 11 4 LT l))
    (k : Nat → Nat → Nat → Nat → Nat → Nat) :
    m11Lev LT k = k (recBS 11 4 (letF 11 4 LT) (m11Run LT 0) (levMaskAt 11 4 LT 12 m11Bs 0))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 1) (levMaskAt 11 4 LT 12 m11Bs 1))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 2) (levMaskAt 11 4 LT 12 m11Bs 2))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 3) (levMaskAt 11 4 LT 12 m11Bs 3))
      (levMaskAt 11 4 LT 12 m11Bs 4) := by
  have hLV : ∀ LV : Nat, ∀ l ∈ maskL 12 LV, IsPermN 11 (letF 11 4 LT l) := fun LV l hl =>
    hL l (List.mem_range.mp (List.mem_filter.mp hl).1)
  have hb : ∀ i < 4, bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44)
      (nat_lit 17592186044415) (pidn (nat_lit 11) (nat_lit 4)) LT (nat_lit 12)
      (levMaskAt 11 4 LT 12 m11Bs i) i =
      recBS 11 4 (letF 11 4 LT) (m11Run LT i) (levMaskAt 11 4 LT 12 m11Bs i) := by
    intro i hi
    have h1 := bfs_eq (n := 11) (w := 4) (LT := LT) (NL := 12) (LV := levMaskAt 11 4 LT 12 m11Bs i)
      (r := i) (by decide) (by decide) (by omega) (hLV _)
    have h2 : maskL 12 (levMaskAt 11 4 LT 12 m11Bs i) = lvAt (letF 11 4 LT) 12 m11Bs i := by
      rw [maskL_levMaskAt]
      congr 1
      have : m11Bs.length = 4 := rfl
      omega
    rw [h2] at h1
    exact h1
  have key : m11Lev LT k = k
      (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44)
        (nat_lit 17592186044415) (pidn (nat_lit 11) (nat_lit 4)) LT (nat_lit 12)
        (levMaskAt 11 4 LT 12 m11Bs 0) 0)
      (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44)
        (nat_lit 17592186044415) (pidn (nat_lit 11) (nat_lit 4)) LT (nat_lit 12)
        (levMaskAt 11 4 LT 12 m11Bs 1) 1)
      (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44)
        (nat_lit 17592186044415) (pidn (nat_lit 11) (nat_lit 4)) LT (nat_lit 12)
        (levMaskAt 11 4 LT 12 m11Bs 2) 2)
      (bfs (nat_lit 11) (nat_lit 4) (nat_lit 15) (nat_lit 44)
        (nat_lit 17592186044415) (pidn (nat_lit 11) (nat_lit 4)) LT (nat_lit 12)
        (levMaskAt 11 4 LT 12 m11Bs 3) 3)
      (levMaskAt 11 4 LT 12 m11Bs 4) := by
    unfold m11Lev
    simp only [strictN_eq]
    rfl
  rw [key, hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)]

private theorem m11_itr_lt {w n : Nat} (hw : n ≤ 2 ^ w) (g k : Nat) {x : Nat} (hx : x < n) :
    itr (fd w g) k x < 2 ^ w := by
  cases k with
  | zero => exact Nat.lt_of_lt_of_le hx hw
  | succ k => exact fd_lt w g _

private theorem m11_ordR_succ (n w m idn g k p : Nat) :
    ordR n w m idn g (k + 1) p =
      if Nat.beq p idn = true then false else ordR n w m idn g k (pcomp n w m g p) := by
  show Bool.rec (motive := fun _ => Bool) (strictB (pcomp n w m g p) (ordR n w m idn g k)) false
    (Nat.beq p idn) = _
  rw [strictB_eq]
  cases Nat.beq p idn <;> rfl

private theorem m11_enc_eq_id {n w : Nat} (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) {f : Nat → Nat}
    (hf : ∀ x < n, f x < 2 ^ w) :
    Nat.beq (enc w f n) (pidn n w) = true ↔ ∀ x < n, f x = x := by
  rw [Nat.beq_eq, pidn_eq hn24 hw]
  constructor
  · intro h x hx
    have h1 : fd w (enc w f n) x = fd w (enc w (fun i => i) n) x := by rw [h]
    rwa [fd_enc hf hx, fd_enc (fun i hi => Nat.lt_of_lt_of_le hi hw) hx] at h1
  · intro h
    exact enc_congr h

private theorem m11_ordR_spec {n w : Nat} (hn32 : n < 2 ^ 32) (hn24 : n ≤ 2 ^ 24)
    (hw : n ≤ 2 ^ w) (g : Nat) :
    ∀ (k j : Nat), ordR n w (mask w) (pidn n w) g k (enc w (itr (fd w g) j) n) = true ↔
      (∀ t < k, ¬ ∀ x < n, itr (fd w g) (j + t) x = x) ∧
        ∀ x < n, itr (fd w g) (j + k) x = x := by
  intro k
  induction k with
  | zero =>
    intro j
    show Nat.beq (enc w (itr (fd w g) j) n) (pidn n w) = true ↔ _
    rw [m11_enc_eq_id hn24 hw (fun x hx => m11_itr_lt hw g j hx)]
    exact ⟨fun h => ⟨fun t ht => absurd ht (Nat.not_lt_zero t), h⟩, fun h => h.2⟩
  | succ k ih =>
    intro j
    rw [m11_ordR_succ]
    by_cases hid : ∀ x < n, itr (fd w g) j x = x
    · have hb : Nat.beq (enc w (itr (fd w g) j) n) (pidn n w) = true :=
        (m11_enc_eq_id hn24 hw (fun x hx => m11_itr_lt hw g j hx)).2 hid
      rw [if_pos hb]
      constructor
      · intro h
        exact absurd h Bool.false_ne_true
      · rintro ⟨h1, _⟩
        exact absurd hid (h1 0 (Nat.succ_pos k))
    · have hb : ¬ Nat.beq (enc w (itr (fd w g) j) n) (pidn n w) = true := fun h =>
        hid ((m11_enc_eq_id hn24 hw (fun x hx => m11_itr_lt hw g j hx)).1 h)
      rw [if_neg hb]
      have hp : pcomp n w (mask w) g (enc w (itr (fd w g) j) n) =
          enc w (itr (fd w g) (j + 1)) n := by
        rw [pcomp_eq hn32]
        refine enc_congr fun i hi => ?_
        rw [fd_enc (fun x hx => m11_itr_lt hw g j hx) hi]
        rfl
      rw [hp, ih (j + 1)]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => ?_, ?_⟩
        · cases t with
          | zero => exact hid
          | succ t =>
            have e : j + (t + 1) = j + 1 + t := by omega
            rw [e]
            exact h1 t (by omega)
        · have e : j + (k + 1) = j + 1 + k := by omega
          rw [e]
          exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => ?_, ?_⟩
        · have e : j + 1 + t = j + (t + 1) := by omega
          rw [e]
          exact h1 (t + 1) (by omega)
        · have e : j + 1 + k = j + (k + 1) := by omega
          rw [e]
          exact h2

private theorem m11_isPermN_itr {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) (k : Nat) :
    IsPermN n (itr f k) := by
  induction k with
  | zero => exact isPermN_id n
  | succ k ih => exact hf.comp ih

theorem ordIs_iff {g k : Nat} (hg : g < 2 ^ (4 * 11)) (hgp : IsPermN 11 (fd 4 g)) :
    CFSG.KS.M11.ordIs 11 4 15 (pidn 11 4) g k = true ↔ orderOf (permOf 11 (fd 4 g)) = k + 1 := by
  have hspec := m11_ordR_spec (n := 11) (w := 4) (by decide) (by decide) (by decide) g k 1
  have hg1 : enc 4 (itr (fd 4 g) 1) 11 = g := enc_fd hg
  rw [hg1] at hspec
  have h1 : CFSG.KS.M11.ordIs 11 4 15 (pidn 11 4) g k = true ↔
      (∀ t < k, ¬ ∀ x < 11, itr (fd 4 g) (1 + t) x = x) ∧ ∀ x < 11, itr (fd 4 g) (1 + k) x = x :=
    hspec
  rw [h1, orderOf_eq_iff (Nat.succ_pos k)]
  have hpow : ∀ m, permOf 11 (fd 4 g) ^ m = 1 ↔ ∀ x < 11, itr (fd 4 g) m x = x := fun m => by
    rw [permOf_pow hgp m, permOf_eq_one_iff (m11_isPermN_itr hgp m)]
  simp only [ne_eq, hpow]
  constructor
  · rintro ⟨h1, h2⟩
    have e : k.succ = 1 + k := by omega
    refine ⟨by rw [e]; exact h2, fun m hm hm0 => ?_⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = 1 + t := ⟨m - 1, by omega⟩
    exact h1 t (by omega)
  · rintro ⟨h1, h2⟩
    have e : k.succ = 1 + k := by omega
    refine ⟨fun t ht => ?_, by rw [← e]; exact h1⟩
    exact h2 (1 + t) (by omega) (by omega)

@[expose] def prodsA (F : Nat → Nat → Nat) (s0 s1 s2 s3 : BS) : List Nat :=
  (List.range s0.pts.length).flatMap fun k0 => (List.range s1.pts.length).flatMap fun k1 =>
    (List.range s2.pts.length).flatMap fun k2 => (List.range s3.pts.length).map fun k3 =>
      enc 4 (fun x => BS.trans F s0 k0 (BS.trans F s1 k1 (BS.trans F s2 k2 (BS.trans F s3 k3 x)))) 11

private theorem m11_foldl_congr {α β : Type} {l : List β} {F G : α → β → α}
    (h : ∀ a, ∀ b ∈ l, F a b = G a b) (s : α) : l.foldl F s = l.foldl G s := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, List.foldl_cons, h s b List.mem_cons_self]
    exact ih (fun a b' hb' => h a b' (List.mem_cons_of_mem _ hb')) _

private theorem m11_pcomp_enc {p q : Nat → Nat} (hp : ∀ x < 11, p x < 11)
    (hq : ∀ x < 11, q x < 11) :
    pcomp 11 4 15 (enc 4 p 11) (enc 4 q 11) = enc 4 (fun x => p (q x)) 11 := by
  have h : (15 : Nat) = mask 4 := rfl
  have hq' : ∀ j < 11, q j < 2 ^ 4 := fun j hj => by have := hq j hj; omega
  have hp' : ∀ j < 11, p j < 2 ^ 4 := fun j hj => by have := hp j hj; omega
  rw [h, pcomp_eq (by decide)]
  refine enc_congr fun i hi => ?_
  rw [fd_enc hq' hi, fd_enc hp' (hq i hi)]

private theorem m11_recBS_ok {F : Nat → Nat → Nat} {s : BS} (hs : GoodBS 11 F s) :
    RecOK 11 4 s.pts.length (fun k => s.pts.getD k 0) (posBS 4 s)
      (fun k => if k < s.pts.length then enc 4 (BS.trans F s k) 11 else 0)
      (fun k => if k < s.pts.length then enc 4 (finv 11 (BS.trans F s k)) 11 else 0) := by
  obtain ⟨hpos, hle, -, hlt, hperm⟩ := hs
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro k _
    show s.pts.getD k 0 < 2 ^ 4
    by_cases h : k < s.pts.length
    · rw [← List.getElem_eq_getD 0 (h := h)]
      have := hlt _ (List.getElem_mem h)
      omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      decide
  · intro x _
    show posBS 4 s x < 2 ^ 4
    unfold posBS
    split
    · rename_i hx
      have := List.idxOf_lt_length_iff.mpr hx
      omega
    · rw [mask_eq]
      decide
  · intro k _
    show (if k < s.pts.length then enc 4 (BS.trans F s k) 11 else 0) < 2 ^ (11 * 4)
    split
    · rename_i hk
      rw [Nat.mul_comm 11 4]
      exact enc_lt fun i hi => by have := (hperm k hk).1 i hi; omega
    · exact Nat.two_pow_pos _
  · intro k _
    show (if k < s.pts.length then enc 4 (finv 11 (BS.trans F s k)) 11 else 0) < 2 ^ (11 * 4)
    split
    · rw [Nat.mul_comm 11 4]
      exact enc_lt fun i hi => by have := finv_lt (by omega : 0 < 11) (BS.trans F s k) i; omega
    · exact Nat.two_pow_pos _

private theorem m11_ltr {F : Nat → Nat → Nat} {s : BS} (hs : GoodBS 11 F s) (V : Nat) {k : Nat}
    (hk : k < s.pts.length) :
    ltr 44 17592186044415 (recBS 11 4 F s V) k = enc 4 (BS.trans F s k) 11 := by
  have h : ltr (11 * 4) (mask (11 * 4)) (recBS 11 4 F s V) k =
      if k < s.pts.length then enc 4 (BS.trans F s k) 11 else 0 :=
    ltr_recOf (m11_recBS_ok hs) (Nat.lt_of_lt_of_le hk hs.2.1)
  rw [if_pos hk] at h
  exact h

private theorem m11_lcnt {F : Nat → Nat → Nat} {s : BS} (hs : GoodBS 11 F s) (V : Nat) :
    lcnt (recBS 11 4 F s V) = s.pts.length :=
  lcnt_recBS (by decide) (by decide) hs V

theorem enumFold_eq {F : Nat → Nat → Nat} {s0 s1 s2 s3 : BS} (h0 : GoodBS 11 F s0)
    (h1 : GoodBS 11 F s1) (h2 : GoodBS 11 F s2) (h3 : GoodBS 11 F s3) (V0 V1 V2 V3 : Nat)
    (f : Nat → Nat → Nat) (s : Nat) :
    enumFold 11 4 15 44 17592186044415 (recBS 11 4 F s0 V0) (recBS 11 4 F s1 V1)
        (recBS 11 4 F s2 V2) (recBS 11 4 F s3 V3) f s =
      (prodsA F s0 s1 s2 s3).foldl (fun s g => f g s) s := by
  unfold enumFold
  simp only [foldUp_eq, strictN_eq, m11_lcnt h0 V0, m11_lcnt h1 V1, m11_lcnt h2 V2,
    m11_lcnt h3 V3]
  unfold prodsA
  simp only [List.foldl_flatMap, List.foldl_map]
  refine m11_foldl_congr (fun s k0 hk0 => ?_) s
  rw [List.mem_range] at hk0
  refine m11_foldl_congr (fun s k1 hk1 => ?_) s
  rw [List.mem_range] at hk1
  refine m11_foldl_congr (fun s k2 hk2 => ?_) s
  rw [List.mem_range] at hk2
  refine m11_foldl_congr (fun s k3 hk3 => ?_) s
  rw [List.mem_range] at hk3
  have p0 := h0.2.2.2.2 k0 hk0
  have p1 := h1.2.2.2.2 k1 hk1
  have p2 := h2.2.2.2.2 k2 hk2
  have p3 := h3.2.2.2.2 k3 hk3
  rw [m11_ltr h0 V0 hk0, m11_ltr h1 V1 hk1, m11_ltr h2 V2 hk2, m11_ltr h3 V3 hk3,
    m11_pcomp_enc p0.1 p1.1,
    m11_pcomp_enc (p := fun x => BS.trans F s0 k0 (BS.trans F s1 k1 x)) (p0.comp p1).1 p2.1,
    m11_pcomp_enc (p := fun x => BS.trans F s0 k0 (BS.trans F s1 k1 (BS.trans F s2 k2 x)))
      ((p0.comp (p1.comp p2))).1 p3.1]

@[expose] noncomputable def pairsOf (G : List Nat) : List (Nat × Nat) :=
  G.map fun g => (g, pinvS 11 4 15 g)

private def m11_eL (L : List (Nat × Nat)) (i : Nat) : Nat :=
  (L.getD i (0, 0)).1 + (L.getD i (0, 0)).2 * 2 ^ 44

private theorem m11_ent_lt {g gi : Nat} (hg : g < 2 ^ 44) (hgi : gi < 2 ^ 44) :
    g + gi * 2 ^ 44 < 2 ^ 88 := by
  calc g + gi * 2 ^ 44 < 2 ^ 44 + gi * 2 ^ 44 := Nat.add_lt_add_right hg _
    _ = (gi + 1) * 2 ^ 44 := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ 2 ^ 44 * 2 ^ 44 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hgi)
    _ = 2 ^ 88 := by rw [← Nat.pow_add]

private theorem m11_ent_inj {g gi h hi : Nat} (hg : g < 2 ^ 44) (hh : h < 2 ^ 44)
    (e : g + gi * 2 ^ 44 = h + hi * 2 ^ 44) : g = h ∧ gi = hi := by
  have h1 : g = h := by
    have e' : (g + gi * 2 ^ 44) % 2 ^ 44 = (h + hi * 2 ^ 44) % 2 ^ 44 := by rw [e]
    rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg,
      Nat.mod_eq_of_lt hh] at e'
  refine ⟨h1, ?_⟩
  subst h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 44) (Nat.add_left_cancel e)

private theorem m11_getD_eq {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem m11_packP_cons (g gi : Nat) (L : List (Nat × Nat)) (c : Nat) :
    packP ((g, gi) :: L) c =
      ((g ||| (gi <<< 44)) <<< (16 + 88 * c)) ||| packP L (c + 1) := rfl

private theorem m11_enc_cons (w : Nat) (f : Nat → Nat) (len : Nat) :
    enc w f (len + 1) = f 0 + enc w (fun i => f (i + 1)) len * 2 ^ w := by
  have h := enc_add w f 1 len
  have e1 : enc w f 1 = f 0 := by
    rw [show (1 : Nat) = 0 + 1 from rfl, enc_succ, enc_zero, Nat.mul_zero, Nat.pow_zero,
      Nat.mul_one, Nat.zero_add]
  rw [Nat.add_comm len 1, h, e1, Nat.mul_one]
  rw [enc_congr (f := fun i => f (1 + i)) (g := fun i => f (i + 1))
    (fun i _ => by rw [Nat.add_comm])]

private theorem m11_packP_eq : ∀ (L : List (Nat × Nat)) (c : Nat),
    (∀ p ∈ L, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44) →
      packP L c = enc 88 (m11_eL L) L.length * 2 ^ (16 + 88 * c)
  | [], c, _ => by
    show (0 : Nat) = enc 88 (m11_eL []) 0 * 2 ^ (16 + 88 * c)
    rw [enc_zero, Nat.zero_mul]
  | (g, gi) :: L, c, h => by
    have hg : g < 2 ^ 44 := (h (g, gi) List.mem_cons_self).1
    have hgi : gi < 2 ^ 44 := (h (g, gi) List.mem_cons_self).2
    have ih := m11_packP_eq L (c + 1) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    have hlt : (g + gi * 2 ^ 44) * 2 ^ (16 + 88 * c) < 2 ^ (16 + 88 * (c + 1)) :=
      calc (g + gi * 2 ^ 44) * 2 ^ (16 + 88 * c) < 2 ^ 88 * 2 ^ (16 + 88 * c) :=
            Nat.mul_lt_mul_of_pos_right (m11_ent_lt hg hgi) (Nat.two_pow_pos _)
        _ = 2 ^ (16 + 88 * (c + 1)) := by
            rw [← Nat.pow_add]
            congr 1
            omega
    rw [m11_packP_cons, ih, lor_shiftLeft_eq_add hg, Nat.shiftLeft_eq,
      lor_eq_add_of_lt_of_dvd hlt (Nat.dvd_mul_left _ _), List.length_cons, m11_enc_cons]
    have e0 : m11_eL ((g, gi) :: L) 0 = g + gi * 2 ^ 44 := rfl
    have e1 : (fun i => m11_eL ((g, gi) :: L) (i + 1)) = m11_eL L := by
      funext i
      simp [m11_eL, List.getD_cons_succ]
    rw [e0, e1]
    ring

private theorem m11_lenRec {α : Type} (L : List α) :
    (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L) = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show Nat.succ _ = _
    rw [ih]
    rfl

private theorem m11_packPairs_eq {L : List (Nat × Nat)} (hlen : L.length < 2 ^ 16)
    (h : ∀ p ∈ L, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44) :
    packPairs L = L.length + enc 88 (m11_eL L) L.length * 2 ^ 16 := by
  show Nat.lor (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L)
    (packP L 0) = _
  rw [m11_lenRec, m11_packP_eq L 0 h, Nat.mul_zero, Nat.add_zero]
  exact lor_eq_add_of_lt_of_dvd hlen (Nat.dvd_mul_left _ _)

private theorem m11_allRec_iff (L : List (Nat × Nat)) :
    (List.rec (motive := fun _ => Bool) true (fun p _ ih => Prod.rec (motive := fun _ => Bool)
      (fun g gi => bAnd(Nat.blt g (Nat.shiftLeft (nat_lit 1) 44),
        bAnd(Nat.blt gi (Nat.shiftLeft (nat_lit 1) 44), ih))) p) L) = true ↔
      ∀ p ∈ L, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44 := by
  have e : Nat.shiftLeft (nat_lit 1) 44 = 2 ^ 44 := rfl
  induction L with
  | nil => exact ⟨fun _ p hp => absurd hp List.not_mem_nil, fun _ => rfl⟩
  | cons p L ih =>
    obtain ⟨g, gi⟩ := p
    show bAnd(Nat.blt g (Nat.shiftLeft (nat_lit 1) 44),
        bAnd(Nat.blt gi (Nat.shiftLeft (nat_lit 1) 44), _)) = true ↔ _
    rw [e, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩ q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨h1, h2⟩
      · exact ih.1 h3 q hq
    · intro hall
      exact ⟨(hall (g, gi) List.mem_cons_self).1, (hall (g, gi) List.mem_cons_self).2,
        ih.2 (fun q hq => hall q (List.mem_cons_of_mem _ hq))⟩

private theorem m11_pairsBdd_iff (L : List (Nat × Nat)) :
    pairsBdd 44 L = true ↔ L.length < 2 ^ 16 ∧ ∀ p ∈ L, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44 := by
  unfold pairsBdd
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, m11_lenRec, m11_allRec_iff]
  rfl

private theorem m11_packPairs_snoc {L : List (Nat × Nat)} {x : Nat × Nat}
    (hlen : L.length + 1 < 2 ^ 16) (h : ∀ p ∈ L, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44)
    (hx : x.1 < 2 ^ 44 ∧ x.2 < 2 ^ 44) :
    packPairs (L ++ [x]) = packPairs L + 1 +
      ((x.1 ||| (x.2 <<< 44)) <<< (16 + 88 * (packPairs L &&& 65535))) := by
  have hL16 : L.length < 2 ^ 16 := by omega
  have hh : ∀ p ∈ L ++ [x], p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact h p hp
    · rw [List.mem_singleton] at hp
      rw [hp]
      exact hx
  have hlen' : (L ++ [x]).length < 2 ^ 16 := by simpa using hlen
  rw [m11_packPairs_eq hlen' hh, m11_packPairs_eq hL16 h]
  have hand : (L.length + enc 88 (m11_eL L) L.length * 2 ^ 16) &&& 65535 = L.length := by
    have e : (65535 : Nat) = 2 ^ 16 - 1 := by decide
    rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hL16]
  have e2 : ∀ i < L.length, m11_eL (L ++ [x]) i = m11_eL L i := by
    intro i hi
    simp only [m11_eL, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have e3 : m11_eL (L ++ [x]) L.length = x.1 + x.2 * 2 ^ 44 := by
    simp only [m11_eL, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    simp
  rw [hand, lor_shiftLeft_eq_add hx.1, Nat.shiftLeft_eq, List.length_append,
    List.length_singleton, enc_succ, enc_congr e2, e3]
  ring

private theorem m11_foldl_col {f : Nat → Nat → Nat} (pred : Nat → Bool)
    (hf : ∀ g s, f g s = if pred g = true then
      s + 1 + ((g ||| (pinvS 11 4 15 g <<< 44)) <<< (16 + 88 * (s &&& 65535))) else s) :
    ∀ (Q L0 : List Nat) (s : Nat), (∀ g ∈ Q, g < 2 ^ 44 ∧ pinvS 11 4 15 g < 2 ^ 44) →
      (∀ g ∈ L0, g < 2 ^ 44 ∧ pinvS 11 4 15 g < 2 ^ 44) → s = packPairs (pairsOf L0) →
      L0.length + Q.length < 2 ^ 16 →
      Q.foldl (fun s g => f g s) s = packPairs (pairsOf (L0 ++ Q.filter pred)) := by
  intro Q
  induction Q with
  | nil =>
    intro L0 s _ _ hs _
    rw [List.foldl_nil, List.filter_nil, List.append_nil]
    exact hs
  | cons g Q ih =>
    intro L0 s hQ hL0 hs hlen
    have hg := hQ g List.mem_cons_self
    have hQ' : ∀ g' ∈ Q, g' < 2 ^ 44 ∧ pinvS 11 4 15 g' < 2 ^ 44 := fun g' hg' =>
      hQ g' (List.mem_cons_of_mem _ hg')
    rw [List.foldl_cons, hf]
    by_cases hp : pred g = true
    · rw [if_pos hp, List.filter_cons_of_pos hp]
      have hpl : ∀ p ∈ pairsOf L0, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44 := by
        intro p hp
        obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hp
        exact hL0 g' hg'
      have hlen1 : (pairsOf L0).length + 1 < 2 ^ 16 := by
        simp only [pairsOf, List.length_map, List.length_cons] at hlen ⊢
        omega
      have hnew : s + 1 + ((g ||| (pinvS 11 4 15 g <<< 44)) <<<
          (16 + 88 * (s &&& 65535))) = packPairs (pairsOf (L0 ++ [g])) := by
        have e : pairsOf (L0 ++ [g]) = pairsOf L0 ++ [(g, pinvS 11 4 15 g)] := by
          simp [pairsOf]
        rw [e, m11_packPairs_snoc hlen1 hpl hg, ← hs]
      rw [hnew]
      have hL0' : ∀ g' ∈ L0 ++ [g], g' < 2 ^ 44 ∧ pinvS 11 4 15 g' < 2 ^ 44 := by
        intro g' hg'
        rcases List.mem_append.1 hg' with hg' | hg'
        · exact hL0 g' hg'
        · rw [List.mem_singleton] at hg'
          rw [hg']
          exact hg
      have hlen2 : (L0 ++ [g]).length + Q.length < 2 ^ 16 := by
        simp only [List.length_append, List.length_singleton, List.length_cons,
          List.length_nil] at hlen ⊢
        omega
      rw [ih (L0 ++ [g]) _ hQ' hL0' rfl hlen2]
      simp
    · rw [if_neg hp, List.filter_cons_of_neg hp]
      exact ih L0 s hQ' hL0 hs (by simp only [List.length_cons] at hlen; omega)

private theorem m11_pinvS_enc {G : Nat → Nat} (hG : IsPermN 11 G) :
    pinvS 11 4 15 (enc 4 G 11) = enc 4 (finv 11 G) 11 := by
  have hGw : ∀ i < 11, G i < 2 ^ 4 := fun i hi => by have := hG.1 i hi; omega
  have h15 : (15 : Nat) = mask 4 := rfl
  rw [h15]
  refine pinvS_eq (by decide) (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
  · rw [fd_enc hGw hi]
    exact hG.1 i hi
  · obtain ⟨h1, h2⟩ := finv_spec hG hj
    rw [fd_enc hGw h1]
    exact ⟨h1, h2⟩
  · rw [fd_enc hGw hi]
    exact finv_apply hG hi

private theorem m11_prodsA_bdd {F : Nat → Nat → Nat} {s0 s1 s2 s3 : BS} (h0 : GoodBS 11 F s0)
    (h1 : GoodBS 11 F s1) (h2 : GoodBS 11 F s2) (h3 : GoodBS 11 F s3) :
    ∀ g ∈ prodsA F s0 s1 s2 s3, g < 2 ^ 44 ∧ pinvS 11 4 15 g < 2 ^ 44 := by
  intro g hg
  simp only [prodsA, List.mem_flatMap, List.mem_map, List.mem_range] at hg
  obtain ⟨k0, hk0, k1, hk1, k2, hk2, k3, hk3, rfl⟩ := hg
  have hG : IsPermN 11 (fun x => BS.trans F s0 k0 (BS.trans F s1 k1
      (BS.trans F s2 k2 (BS.trans F s3 k3 x)))) :=
    (h0.2.2.2.2 k0 hk0).comp ((h1.2.2.2.2 k1 hk1).comp
      ((h2.2.2.2.2 k2 hk2).comp (h3.2.2.2.2 k3 hk3)))
  rw [m11_pinvS_enc hG]
  have hlt : ∀ G : Nat → Nat, IsPermN 11 G → enc 4 G 11 < 2 ^ 44 := fun G hG =>
    enc_lt (w := 4) (len := 11) fun i hi => by have := hG.1 i hi; omega
  exact ⟨hlt _ hG, hlt _ hG.finv⟩

private theorem m11_length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (c : Nat)
    (h : ∀ a ∈ l, (f a).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
      h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    omega

private theorem m11_prodsA_length {F : Nat → Nat → Nat} {s0 s1 s2 s3 : BS}
    (h0 : GoodBS 11 F s0) (h1 : GoodBS 11 F s1) (h2 : GoodBS 11 F s2) (h3 : GoodBS 11 F s3) :
    (prodsA F s0 s1 s2 s3).length < 2 ^ 16 := by
  unfold prodsA
  rw [m11_length_flatMap_const _ _ (s1.pts.length * (s2.pts.length * s3.pts.length)),
    List.length_range]
  · have : s0.pts.length * (s1.pts.length * (s2.pts.length * s3.pts.length)) ≤
        11 * (11 * (11 * 11)) :=
      Nat.mul_le_mul h0.2.1 (Nat.mul_le_mul h1.2.1 (Nat.mul_le_mul h2.2.1 h3.2.1))
    omega
  · intro k0 _
    rw [m11_length_flatMap_const _ _ (s2.pts.length * s3.pts.length), List.length_range]
    intro k1 _
    rw [m11_length_flatMap_const _ _ s3.pts.length, List.length_range]
    intro k2 _
    rw [List.length_map, List.length_range]

theorem m11Col_eq {tA tB : List Nat} {W : List (List Int)} (k : Nat)
    (hL : ∀ l < 12, IsPermN 11 (letF 11 4 (m11LT tA tB W) l)) :
    m11Col tA tB W k = packPairs (pairsOf ((prodsA (letF 11 4 (m11LT tA tB W))
      (m11Run (m11LT tA tB W) 0) (m11Run (m11LT tA tB W) 1) (m11Run (m11LT tA tB W) 2)
      (m11Run (m11LT tA tB W) 3)).filter
        fun g => CFSG.KS.M11.ordIs 11 4 15 (pidn 11 4) g k)) := by
  unfold m11Col
  rw [strictN_eq]
  generalize m11LT tA tB W = LT at hL ⊢
  rw [m11Lev_eq hL]
  have hG : ∀ i < 4, GoodBS 11 (letF 11 4 LT) (m11Run LT i) := fun i hi =>
    goodBS_run (by omega) (fun l hl => hL l (lvAt_sub _ _ _ _ l hl))
  have h0 := hG 0 (by decide)
  have h1 := hG 1 (by decide)
  have h2 := hG 2 (by decide)
  have h3 := hG 3 (by decide)
  rw [enumFold_eq h0 h1 h2 h3]
  have := m11_foldl_col (pred := fun g => CFSG.KS.M11.ordIs 11 4 15 (pidn 11 4) g k)
    (f := fun g s => nIf(CFSG.KS.M11.ordIs 11 4 15 (pidn 11 4) g k,
      strictN (Nat.land s 65535) (fun c => Nat.add (Nat.add s 1)
        (Nat.shiftLeft (Nat.lor g (Nat.shiftLeft (pinvS 11 4 15 g) 44))
          (Nat.add 16 (Nat.mul 88 c)))), s))
    (fun g s => by
      rw [nIf_eq, strictN_eq]
      rfl)
    (prodsA (letF 11 4 LT) (m11Run LT 0) (m11Run LT 1) (m11Run LT 2) (m11Run LT 3)) [] 0
    (m11_prodsA_bdd h0 h1 h2 h3) (by simp) rfl
    (by simpa using m11_prodsA_length h0 h1 h2 h3)
  simpa using this

theorem packPairs_inj {L L' : List (Nat × Nat)} (h : pairsBdd 44 L = true)
    (h' : pairsBdd 44 L' = true) (he : packPairs L = packPairs L') : L = L' := by
  obtain ⟨hl, hb⟩ := (m11_pairsBdd_iff L).1 h
  obtain ⟨hl', hb'⟩ := (m11_pairsBdd_iff L').1 h'
  rw [m11_packPairs_eq hl hb, m11_packPairs_eq hl' hb'] at he
  have hlen : L.length = L'.length := by
    have e' : (L.length + enc 88 (m11_eL L) L.length * 2 ^ 16) % 2 ^ 16 =
        (L'.length + enc 88 (m11_eL L') L'.length * 2 ^ 16) % 2 ^ 16 := by rw [he]
    rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_of_lt hl'] at e'
  have hX : enc 88 (m11_eL L) L.length = enc 88 (m11_eL L') L'.length := by
    rw [hlen] at he
    have := Nat.add_left_cancel he
    rw [← hlen] at this
    rw [hlen] at this ⊢
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos 16) this
  have hbd : ∀ (M : List (Nat × Nat)), (∀ p ∈ M, p.1 < 2 ^ 44 ∧ p.2 < 2 ^ 44) → ∀ i < M.length,
      m11_eL M i < 2 ^ 88 := by
    intro M hM i hi
    have hm : M.getD i (0, 0) ∈ M := by
      rw [m11_getD_eq hi]
      exact List.getElem_mem hi
    exact m11_ent_lt (hM _ hm).1 (hM _ hm).2
  apply List.ext_getElem hlen
  intro i h1 h2
  have e1 : m11_eL L i = m11_eL L' i := by
    have this : fd 88 (enc 88 (m11_eL L) L.length) i = fd 88 (enc 88 (m11_eL L') L'.length) i := by
      rw [hX]
    rw [fd_enc (hbd L hb) h1, fd_enc (hbd L' hb') h2] at this
    exact this
  have hmem : L[i] ∈ L := List.getElem_mem h1
  have hmem' : L'[i] ∈ L' := List.getElem_mem h2
  unfold m11_eL at e1
  rw [m11_getD_eq h1, m11_getD_eq h2] at e1
  obtain ⟨a1, a2⟩ := m11_ent_inj (hb _ hmem).1 (hb' _ hmem').1 e1
  exact Prod.ext a1 a2

end CFSG.KS.PK

end
