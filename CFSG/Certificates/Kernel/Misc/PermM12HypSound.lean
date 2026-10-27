module

public import Certificates.Data.Kernel.Misc.PermM12Hyp
public import CFSG.GH74.M12.HypCoreInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.Misc.M12Hyp

open CFSG.GH74.M12.Hyp CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_iff {a : Bool} : notB a = true ↔ ¬ a = true := by
  cases a <;> simp [notB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem brec_iff {b c : Bool} :
    Bool.rec (motive := fun _ => Bool) (notB c) c b = true ↔ (b = true ↔ c = true) := by
  cases b <;> cases c <;> simp [notB]

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by
  rw [Nat.beq_eq]

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allL_iff (l : List ℕ) (f : ℕ → Bool) : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons x t ih =>
    change andB (f x) (allL t f) = true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

theorem anyL_iff (l : List ℕ) (f : ℕ → Bool) : anyL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | cons x t ih =>
    change orB (f x) (anyL t f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem memL_iff (c : ℕ) (l : List ℕ) : memL c l = true ↔ c ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons x t ih =>
    change orB (Nat.beq c x) (memL c t) = true ↔ _
    rw [orB_iff, beq_iff, ih, List.mem_cons]

theorem lenL_eq (l : List ℕ) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenL t) = _
    rw [ih, List.length_cons]

theorem nodupL_iff (l : List ℕ) : nodupL l = true → l.Nodup := by
  induction l with
  | nil => exact fun _ => List.nodup_nil
  | cons x t ih =>
    intro h
    change andB (notB (memL x t)) (nodupL t) = true at h
    rw [andB_iff, notB_iff, memL_iff] at h
    exact List.nodup_cons.mpr ⟨h.1, ih h.2⟩

theorem allBs_cons (b : Bool) (l : List Bool) : allBs (b :: l) = andB b (allBs l) := rfl

theorem allBs_nil : allBs [] = true := rfl

theorem img_eq (s i : ℕ) : img s i = s / 32 ^ i % 32 := by
  change (s >>> (5 * i)) &&& (2 ^ 5 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem encT_cons (x : ℕ) (t : List ℕ) : encT (x :: t) = x + 32 * encT t := rfl

theorem img_encT {t : List ℕ} (ht : ∀ x ∈ t, x < 32) (i : ℕ) : img (encT t) i = t.getD i 0 := by
  rw [img_eq]
  induction t generalizing i with
  | nil =>
    change 0 / 32 ^ i % 32 = _
    simp
  | cons x r ih =>
    have hx := ht x (List.mem_cons_self ..)
    rw [encT_cons]
    cases i with
    | zero =>
      rw [List.getD_cons_zero, Nat.pow_zero, Nat.div_one]
      omega
    | succ i =>
      rw [List.getD_cons_succ, ← ih (fun y hy => ht y (List.mem_cons_of_mem _ hy)) i,
        Nat.pow_succ', ← Nat.div_div_eq_div_mul]
      congr 2
      omega

theorem encT_snoc (l : List ℕ) (y : ℕ) : encT (l ++ [y]) = encT l + 32 ^ l.length * y := by
  induction l with
  | nil =>
    change y + 32 * 0 = 0 + 1 * y
    omega
  | cons x t ih =>
    rw [List.cons_append, encT_cons, encT_cons, ih, List.length_cons, Nat.pow_succ',
      Nat.mul_assoc, Nat.mul_add]
    omega

theorem ofFn_eq (n : ℕ) (g : ℕ → ℕ) : ofFn n g = encT ((List.range n).map g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ofFn n g + Nat.shiftLeft (g n) (5 * n) = _
    rw [ih, List.range_succ, List.map_append, List.map_cons, List.map_nil, encT_snoc,
      List.length_map, List.length_range, shl_eq, Nat.pow_mul, Nat.mul_comm (g n)]

theorem table_eq (t : List ℕ) : (List.range t.length).map (fun i => t.getD i 0) = t := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem _ _ h2

theorem img_ofFn {n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 32) {i : ℕ} (hi : i < n) :
    img (ofFn n g) i = g i := by
  rw [ofFn_eq, img_encT, List.getD_eq_getElem _ _ (by simpa using hi)]
  · simp
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hg j (List.mem_range.mp hj)

def V (t : List ℕ) : Prop := t.length = 12 ∧ (∀ x ∈ t, x < 12) ∧ t.Nodup

theorem V.lt32 {t : List ℕ} (h : V t) : ∀ x ∈ t, x < 32 := fun x hx => by
  have := h.2.1 x hx
  omega

theorem V.img_enc {t : List ℕ} (h : V t) (i : ℕ) : img (encT t) i = t.getD i 0 := img_encT h.lt32 i

theorem V.table {t : List ℕ} (h : V t) : (List.range 12).map (fun i => t.getD i 0) = t := by
  have := table_eq t
  rwa [h.1] at this

theorem V.getD_lt {t : List ℕ} (h : V t) {i : ℕ} (hi : i < 12) : t.getD i 0 < 12 := by
  rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact hi)]
  exact h.2.1 _ (List.getElem_mem _)

theorem V.mem {t : List ℕ} (h : V t) {j : ℕ} (hj : j < 12) : j ∈ t := by
  have hs : t.toFinset ⊆ Finset.range 12 := by
    intro x hx
    exact Finset.mem_range.mpr (h.2.1 x (List.mem_toFinset.mp hx))
  have hc : (Finset.range 12).card ≤ t.toFinset.card := by
    rw [List.toFinset_card_of_nodup h.2.2, h.1, Finset.card_range]
  have := Finset.eq_of_subset_of_card_le hs hc
  rw [← List.mem_toFinset, this]
  exact Finset.mem_range.mpr hj

theorem V.idxOf_lt {t : List ℕ} (h : V t) {j : ℕ} (hj : j < 12) : t.idxOf j < 12 := by
  have := List.idxOf_lt_length_of_mem (h.mem hj)
  rwa [h.1] at this

theorem V.idxOf_getD {t : List ℕ} (h : V t) {i : ℕ} (hi : i < 12) : t.idxOf (t.getD i 0) = i := by
  rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact hi)]
  exact h.2.2.idxOf_getElem i _

theorem V.getD_idxOf {t : List ℕ} (h : V t) {j : ℕ} (hj : j < 12) : t.getD (t.idxOf j) 0 = j := by
  have hl := List.idxOf_lt_length_of_mem (h.mem hj)
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_idxOf hl

theorem V.inj {s t : List ℕ} (hs : V s) (ht : V t) (h : encT s = encT t) : s = t := by
  rw [← hs.table, ← ht.table]
  apply List.map_congr_left
  intro i _
  rw [← hs.img_enc, ← ht.img_enc, h]

theorem V.beq {s t : List ℕ} (hs : V s) (ht : V t) : Nat.beq (encT s) (encT t) = true ↔ s = t :=
  ⟨fun h => hs.inj ht (beq_iff.mp h), fun h => h ▸ Nat.beq_refl _⟩

theorem V.enc_ofFn {t : List ℕ} (h : V t) : encT t = ofFn 12 (fun i => t.getD i 0) := by
  rw [ofFn_eq, h.table]

theorem v_tid : V tid := by
  refine ⟨List.length_range, fun x hx => List.mem_range.mp hx, List.nodup_range⟩

theorem one_eq : one 12 = encT tid := by
  unfold one
  rw [ofFn_eq, List.map_id']
  rfl

theorem V.mul' {s t : List ℕ} (hs : V s) (ht : V t) : V (tmul s t) := by
  refine ⟨by unfold CFSG.GH74.M12.Hyp.tmul; rw [List.length_map, ht.1], ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hs.getD_lt (ht.2.1 j hj)
  · refine List.Nodup.map_on ?_ ht.2.2
    intro x hx y hy hxy
    rw [← hs.idxOf_getD (ht.2.1 x hx), ← hs.idxOf_getD (ht.2.1 y hy), hxy]

theorem V.inv' {s : List ℕ} (hs : V s) : V (tinv s) := by
  refine ⟨by unfold CFSG.GH74.M12.Hyp.tinv; rw [List.length_map, List.length_range], ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hs.idxOf_lt (List.mem_range.mp hj)
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    rw [← hs.getD_idxOf (List.mem_range.mp hx), ← hs.getD_idxOf (List.mem_range.mp hy)]
    exact congrArg (fun k => s.getD k 0) hxy

theorem V.comm' {s t : List ℕ} (hs : V s) (ht : V t) : V (tcomm s t) :=
  (hs.mul' ht).inv'.mul' (ht.mul' hs)

theorem mul_enc {s t : List ℕ} (hs : V s) (ht : V t) :
    mul 12 (encT s) (encT t) = encT (tmul s t) := by
  unfold mul
  rw [ofFn_eq]
  congr 1
  unfold CFSG.GH74.M12.Hyp.tmul
  conv => rhs; rw [← ht.table]
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [Function.comp_apply, hs.img_enc, ht.img_enc]

theorem m_enc {s t : List ℕ} (hs : V s) (ht : V t) : m (encT s) (encT t) = encT (tmul s t) :=
  mul_enc hs ht

private theorem inv_sum (s n : ℕ) :
    inv n s = ∑ i ∈ Finset.range n, Nat.shiftLeft i (5 * img s i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change inv n s + Nat.shiftLeft n (5 * img s n) = _
    rw [Finset.sum_range_succ, ih]

private theorem ofFn_sum (g : ℕ → ℕ) (n : ℕ) :
    ofFn n g = ∑ i ∈ Finset.range n, Nat.shiftLeft (g i) (5 * i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ofFn n g + Nat.shiftLeft (g n) (5 * n) = _
    rw [Finset.sum_range_succ, ih]

theorem inv_enc {s : List ℕ} (hs : V s) : inv 12 (encT s) = encT (tinv s) := by
  have e2 : encT (tinv s) = ofFn 12 (fun j => s.idxOf j) := by
    unfold CFSG.GH74.M12.Hyp.tinv
    rw [← ofFn_eq]
  rw [inv_sum, e2, ofFn_sum]
  apply Finset.sum_nbij' (fun i => s.getD i 0) (fun j => s.idxOf j)
  · intro i hi
    exact Finset.mem_range.mpr (hs.getD_lt (Finset.mem_range.mp hi))
  · intro j hj
    exact Finset.mem_range.mpr (hs.idxOf_lt (Finset.mem_range.mp hj))
  · intro i hi
    exact hs.idxOf_getD (Finset.mem_range.mp hi)
  · intro j hj
    exact hs.getD_idxOf (Finset.mem_range.mp hj)
  · intro i hi
    rw [hs.img_enc, hs.idxOf_getD (Finset.mem_range.mp hi)]

theorem V.of_validT {t : List ℕ} (h : validT t = true) : V t := by
  unfold validT at h
  rw [andB_iff, andB_iff, beq_iff, beq_iff, lenL_eq] at h
  obtain ⟨hl, hlt, hm⟩ := h
  have hlt' : ∀ x ∈ t, x < 12 := by
    clear hm hl
    induction t with
    | nil => exact fun _ h => absurd h List.not_mem_nil
    | cons x r ih =>
      change andB (Nat.blt x 12) _ = true at hlt
      rw [andB_iff] at hlt
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_of_ble_eq_true hlt.1
      · exact ih hlt.2 y hy
  refine ⟨hl, hlt', ?_⟩
  have h32 : ∀ x ∈ t, x < 32 := fun x hx => by
    have := hlt' x hx
    omega
  have key : ∀ i < 12, img (inv 12 (encT t)) (t.getD i 0) = i := by
    intro i hi
    have := congrArg (fun c => img c i) hm
    unfold mul one at this
    rw [img_ofFn (fun _ _ => by rw [img_eq]; exact Nat.mod_lt _ (by decide)) hi,
      img_ofFn (fun j hj => by omega) hi, img_encT h32] at this
    exact this
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hi : i.1 < 12 := hl ▸ i.2
  have hj : j.1 < 12 := hl ▸ j.2
  apply Fin.ext
  rw [← key i.1 hi, ← key j.1 hj, List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2]
  exact congrArg _ hij

theorem V.of_validL : ∀ {l : List (List ℕ)}, validL l = true → ∀ t ∈ l, V t
  | [], _, _, ht => absurd ht List.not_mem_nil
  | u :: r, hv, t, ht => by
    change andB (validT u) (validL r) = true at hv
    rw [andB_iff] at hv
    rcases List.mem_cons.mp ht with rfl | ht
    · exact V.of_validT hv.1
    · exact V.of_validL hv.2 t ht

theorem tmul_assoc' {a b c : List ℕ} (h : ∀ j ∈ c, j < b.length) :
    tmul (tmul a b) c = tmul a (tmul b c) := by
  unfold CFSG.GH74.M12.Hyp.tmul
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  rw [Function.comp_apply, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h j hj),
    List.getElem_map, List.getD_eq_getElem _ _ (h j hj)]

theorem V.mul'_tid {s : List ℕ} (hs : V s) : tmul s tid = s := hs.table

theorem V.tid_tmul {s : List ℕ} (hs : V s) : tmul tid s = s := by
  unfold CFSG.GH74.M12.Hyp.tmul
  conv => rhs; rw [← List.map_id s]
  apply List.map_congr_left
  intro j hj
  have := hs.2.1 j hj
  rw [List.getD_eq_getElem _ _ (by unfold tid; rw [List.length_range]; exact this)]
  unfold tid
  rw [List.getElem_range]
  rfl

theorem V.pw {s : List ℕ} (hs : V s) : ∀ k, V (CFSG.GH74.M12.Hyp.tpow s k)
  | 0 => v_tid
  | k + 1 => hs.mul' (hs.pw k)

theorem V.pw_succ {s : List ℕ} (hs : V s) :
    ∀ k, CFSG.GH74.M12.Hyp.tpow s (k + 1) = tmul (CFSG.GH74.M12.Hyp.tpow s k) s
  | 0 => by
    change tmul s tid = tmul tid s
    rw [hs.mul'_tid, hs.tid_tmul]
  | k + 1 => by
    change tmul s (CFSG.GH74.M12.Hyp.tpow s (k + 1)) = tmul (tmul s (CFSG.GH74.M12.Hyp.tpow s k)) s
    rw [hs.pw_succ k, tmul_assoc']
    intro j hj
    rw [(hs.pw k).1]
    exact hs.2.1 j hj

theorem pow_enc {s : List ℕ} (hs : V s) : ∀ k, pow 12 (encT s) k = encT (CFSG.GH74.M12.Hyp.tpow s k)
  | 0 => one_eq
  | k + 1 => by
    change mul 12 (pow 12 (encT s) k) (encT s) = _
    rw [pow_enc hs k, mul_enc (hs.pw k) hs, hs.pw_succ k]

theorem tcK_enc {s t : List ℕ} (hs : V s) (ht : V t) : tcK (encT s) (encT t) = encT (tcomm s t) := by
  unfold tcK tcomm
  rw [m_enc hs ht, m_enc ht hs, inv_enc (hs.mul' ht), m_enc (hs.mul' ht).inv' (ht.mul' hs)]

theorem oneJ_iff {J s : List ℕ} (hJ : V J) (hs : V s) :
    oneJ (encT J) (encT s) = true ↔ s = tid ∨ s = J := by
  unfold oneJ
  rw [orB_iff, one_eq, hs.beq v_tid, hs.beq hJ]

theorem memE {L : List (List ℕ)} (hL : ∀ u ∈ L, V u) {t : List ℕ} (ht : V t) :
    memL (encT t) (L.map encT) = true ↔ t ∈ L := by
  rw [memL_iff, List.mem_map]
  constructor
  · rintro ⟨u, hu, e⟩
    exact (hL u hu).inj ht e ▸ hu
  · exact fun h => ⟨t, h, rfl⟩

theorem allE (L : List (List ℕ)) (f : ℕ → Bool) :
    allL (L.map encT) f = true ↔ ∀ t ∈ L, f (encT t) = true := by
  rw [allL_iff, List.forall_mem_map]

theorem anyE (L : List (List ℕ)) (f : ℕ → Bool) :
    anyL (L.map encT) f = true ↔ ∃ t ∈ L, f (encT t) = true := by
  rw [anyL_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨_, List.mem_map_of_mem ht, h⟩

theorem lenE (L : List (List ℕ)) : lenL (L.map encT) = L.length := by
  rw [lenL_eq, List.length_map]

theorem nodupE {L : List (List ℕ)} (h : nodupL (L.map encT) = true) : L.Nodup :=
  (nodupL_iff _ h).of_map _

theorem mulClE {L : List (List ℕ)} (hL : ∀ u ∈ L, V u) (h : mulCl (L.map encT) = true) :
    ∀ s ∈ L, ∀ t ∈ L, tmul s t ∈ L := by
  unfold mulCl at h
  rw [allE] at h
  intro s hs t ht
  have h := h s hs
  rw [allE] at h
  have h := h t ht
  rw [m_enc (hL s hs) (hL t ht), memE hL ((hL s hs).mul' (hL t ht))] at h
  exact h

theorem invClE {L : List (List ℕ)} (hL : ∀ u ∈ L, V u) (h : invCl (L.map encT) = true) :
    ∀ s ∈ L, tinv s ∈ L := by
  unfold invCl at h
  rw [allE] at h
  intro s hs
  have h := h s hs
  rw [inv_enc (hL s hs), memE hL (hL s hs).inv'] at h
  exact h

theorem normByE {H L : List (List ℕ)} (hH : ∀ u ∈ H, V u) (hL : ∀ u ∈ L, V u)
    (h : normBy (H.map encT) (L.map encT) = true) :
    ∀ c ∈ H, ∀ q ∈ L, tmul (tmul c q) (tinv c) ∈ L := by
  unfold normBy at h
  rw [allE] at h
  intro c hc q hq
  have h := h c hc
  rw [allE] at h
  have h := h q hq
  have vc := hH c hc
  have vq := hL q hq
  rw [m_enc vc vq, inv_enc vc, m_enc (vc.mul' vq) vc.inv',
    memE hL ((vc.mul' vq).mul' vc.inv')] at h
  exact h

theorem take5 {t : List ℕ} (ht : V t) {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 12) (h1 : a1 < 12)
    (h2 : a2 < 12) (h3 : a3 < 12) (h4 : a4 < 12)
    (h : Nat.beq (Nat.land (encT t) 33554431) (key5 a0 a1 a2 a3 a4) = true) :
    t.take 5 = [a0, a1, a2, a3, a4] := by
  rw [beq_iff] at h
  have hk : key5 a0 a1 a2 a3 a4 = a0 + 32 * (a1 + 32 * (a2 + 32 * (a3 + 32 * a4))) := rfl
  have hl : Nat.land (encT t) 33554431 = encT t % 2 ^ 25 := by
    change encT t &&& (2 ^ 25 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [hk, hl] at h
  obtain ⟨hlen, hlt, -⟩ := ht
  match t, hlen, hlt with
  | t0 :: t1 :: t2 :: t3 :: t4 :: r, _, hlt =>
    have b0 := hlt t0 (by simp)
    have b1 := hlt t1 (by simp)
    have b2 := hlt t2 (by simp)
    have b3 := hlt t3 (by simp)
    have b4 := hlt t4 (by simp)
    rw [encT_cons, encT_cons, encT_cons, encT_cons, encT_cons] at h
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    omega

theorem s5135 {Hs Qs Q1s Q2s Bs Gs : List (List Nat)} {Js Es Ns Fs Xs : List Nat}
    {H Q Q1 Q2 B G : List Nat} {J E N F X : Nat}
    (hv : validL (Hs ++ Qs ++ Q1s ++ Q2s ++ Bs ++ Gs ++ [Js, Es, Ns, Fs, Xs]) = true)
    (hH : Hs.map encT = H) (hQ : Qs.map encT = Q) (h1 : Q1s.map encT = Q1)
    (h2 : Q2s.map encT = Q2) (hB : Bs.map encT = B) (hG : Gs.map encT = G)
    (hJ : encT Js = J) (hE : encT Es = E) (hN : encT Ns = N) (hF : encT Fs = F)
    (hX : encT Xs = X) (hk : c5135 H Q Q1 Q2 B G J E N F X = true) :
    ((∀ g ∈ Gs, tmul Js g = tmul g Js) ∧
      (Hs.length = 192) ∧
      (Hs.Nodup) ∧
      (Js ∈ Hs))
      ∧ ((∀ a0 ∈ List.range 4, ∀ a1 ∈ List.range 4, ∀ a2 ∈ List.range 4,
           ∀ a3 ∈ List.range 4, ∀ a4 ∈ List.range 12, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 →
             a1 ≠ a3 → a2 ≠ a3 → 4 ≤ a4 → ∃ t ∈ Hs, t.take 5 = [a0, a1, a2, a3, a4]))
      ∧ ((∀ t ∈ Hs, (∀ s ∈ Hs, tmul t s = tmul s t) → t = tid ∨ t = Js) ∧
      (∃ c ∈ Hs, ∃ d ∈ Hs, tcomm c d ≠ tid) ∧
      (Qs.length = 32) ∧
      (tid ∈ Qs) ∧
      (Js ∈ Qs) ∧
      (∀ s ∈ Qs, ∀ t ∈ Qs, tmul s t ∈ Qs))
      ∧ ((∀ s ∈ Qs, tinv s ∈ Qs) ∧
      (∀ c ∈ Hs, ∀ q ∈ Qs, tmul (tmul c q) (tinv c) ∈ Qs) ∧
      (∀ s ∈ Qs, ((∀ t ∈ Qs, tmul s t = tmul t s) ↔ (s = tid ∨ s = Js))) ∧
      (∀ s ∈ Qs, ∀ t ∈ Qs, tcomm s t = tid ∨ tcomm s t = Js) ∧
      (∀ s ∈ Qs, tmul s s = tid ∨ tmul s s = Js) ∧
      (∃ s ∈ Qs, s ≠ tid ∧ s ≠ Js))
      ∧ ((∃ c ∈ Hs, ∃ d ∈ Hs, tcomm c d ∉ Qs) ∧
      (∀ x ∈ Hs, tmul x (tmul x x) = tid → x ≠ tid →
           ∀ q ∈ Qs, tmul q x = tmul x q → q = tid ∨ q = Js) ∧
      (Xs ∈ Qs) ∧
      (Xs ≠ Js) ∧
      (Q1s.length = 8) ∧
      (Q2s.length = 8))
      ∧ ((Q1s.Nodup) ∧
      (Q2s.Nodup) ∧
      (∀ t ∈ Q1s, t ∈ Qs) ∧
      (∀ t ∈ Q2s, t ∈ Qs) ∧
      (tid ∈ Q1s) ∧
      (tid ∈ Q2s))
      ∧ ((∀ s ∈ Q1s, ∀ t ∈ Q1s, tmul s t ∈ Q1s) ∧
      (∀ s ∈ Q2s, ∀ t ∈ Q2s, tmul s t ∈ Q2s) ∧
      (∀ s ∈ Q1s, tinv s ∈ Q1s) ∧
      (∀ s ∈ Q2s, tinv s ∈ Q2s) ∧
      (∀ c ∈ Hs, ∀ q ∈ Q1s, tmul (tmul c q) (tinv c) ∈ Q1s) ∧
      (∀ c ∈ Hs, ∀ q ∈ Q2s, tmul (tmul c q) (tinv c) ∈ Q2s))
      ∧ ((∀ x ∈ Qs, ∀ y ∈ Qs, tpow x 4 = tid → tpow x 2 ≠ tid →
           tmul y y = tpow x 2 → tmul y x = tmul (tpow x 3) y →
             (x ∈ Q1s ∧ y ∈ Q1s) ∨ (x ∈ Q2s ∧ y ∈ Q2s)))
      ∧ ((Bs.length = 64) ∧
      (Bs.Nodup) ∧
      (tid ∈ Bs) ∧
      (∀ s ∈ Bs, ∀ t ∈ Bs, tmul s t ∈ Bs) ∧
      (∀ s ∈ Bs, tinv s ∈ Bs) ∧
      (∀ t ∈ Bs, t ∈ Hs))
      ∧ ((Es ∈ Bs) ∧
      (Ns ∈ Bs) ∧
      (Fs ∈ Bs) ∧
      (Js ∈ Bs) ∧
      (Xs ∈ Bs) ∧
      (∀ s ∈ Bs, (∀ t ∈ Bs, tmul s t = tmul t s) →
           tmul s s = tid → s ≠ tid → s = Js)) := by
  subst hH hQ h1 h2 hB hG hJ hE hN hF hX
  have hvall := V.of_validL hv
  have vH : ∀ u ∈ Hs, V u := fun u hu => hvall u (by simp [hu])
  have vQ : ∀ u ∈ Qs, V u := fun u hu => hvall u (by simp [hu])
  have vQ1 : ∀ u ∈ Q1s, V u := fun u hu => hvall u (by simp [hu])
  have vQ2 : ∀ u ∈ Q2s, V u := fun u hu => hvall u (by simp [hu])
  have vB : ∀ u ∈ Bs, V u := fun u hu => hvall u (by simp [hu])
  have vG : ∀ u ∈ Gs, V u := fun u hu => hvall u (by simp [hu])
  have vJ : V Js := hvall Js (by simp)
  have vE : V Es := hvall Es (by simp)
  have vN : V Ns := hvall Ns (by simp)
  have vF : V Fs := hvall Fs (by simp)
  have vX : V Xs := hvall Xs (by simp)
  clear hvall hv
  unfold c5135 at hk
  simp only [allBs_cons, allBs_nil, andB_iff, and_true] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19,
    k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38,
    k39, k40, k41, k42, k43, k44, k45, k46, k47, k48⟩ := hk
  rw [one_eq] at k9 k28 k29 k39
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro g hg
    rw [allE] at k1
    have k := k1 g hg
    rw [m_enc vJ (vG g hg), m_enc (vG g hg) vJ, (vJ.mul' (vG g hg)).beq ((vG g hg).mul' vJ)] at k
    exact k
  · rw [beq_iff, lenE] at k2
    exact k2
  · exact nodupE k3
  · exact (memE vH vJ).mp k4
  · intro a0 ha0 a1 ha1 a2 ha2 a3 ha3 a4 ha4 n01 n02 n03 n12 n13 n23 h4
    rw [List.mem_range] at ha0 ha1 ha2 ha3 ha4
    simp only [allN_iff, impB_iff, notB_iff, beq_iff, Nat.ble_eq] at k5
    have k := k5 a0 ha0 a1 ha1 a2 ha2 a3 ha3 a4 ha4 n01 n02 n03 n12 n13 n23 h4
    rw [anyE] at k
    obtain ⟨t, ht, hkey⟩ := k
    exact ⟨t, ht, take5 (vH t ht) (by omega) (by omega) (by omega) (by omega) ha4 hkey⟩
  · intro t ht hc
    rw [allE] at k6
    have k := k6 t ht
    rw [impB_iff, oneJ_iff vJ (vH t ht), allE] at k
    refine k fun s hs => ?_
    rw [m_enc (vH t ht) (vH s hs), m_enc (vH s hs) (vH t ht),
      ((vH t ht).mul' (vH s hs)).beq ((vH s hs).mul' (vH t ht))]
    exact hc s hs
  · rw [anyE] at k7
    obtain ⟨c, hc, k⟩ := k7
    rw [anyE] at k
    obtain ⟨d, hd, k⟩ := k
    rw [notB_iff, tcK_enc (vH c hc) (vH d hd), one_eq,
      ((vH c hc).comm' (vH d hd)).beq v_tid] at k
    exact ⟨c, hc, d, hd, k⟩
  · rw [beq_iff, lenE] at k8
    exact k8
  · exact (memE vQ v_tid).mp k9
  · exact (memE vQ vJ).mp k10
  · exact mulClE vQ k11
  · exact invClE vQ k12
  · exact normByE vH vQ k13
  · intro s hs
    rw [allE] at k14
    have k := k14 s hs
    rw [brec_iff, oneJ_iff vJ (vQ s hs), allE] at k
    rw [← k]
    apply forall₂_congr
    intro t ht
    rw [m_enc (vQ s hs) (vQ t ht), m_enc (vQ t ht) (vQ s hs),
      ((vQ s hs).mul' (vQ t ht)).beq ((vQ t ht).mul' (vQ s hs))]
  · intro s hs t ht
    rw [allE] at k15
    have k := k15 s hs
    rw [allE] at k
    have k := k t ht
    rw [tcK_enc (vQ s hs) (vQ t ht), oneJ_iff vJ ((vQ s hs).comm' (vQ t ht))] at k
    exact k
  · intro s hs
    rw [allE] at k16
    have k := k16 s hs
    rw [m_enc (vQ s hs) (vQ s hs), oneJ_iff vJ ((vQ s hs).mul' (vQ s hs))] at k
    exact k
  · rw [anyE] at k17
    obtain ⟨s, hs, k⟩ := k17
    rw [andB_iff, notB_iff, notB_iff, one_eq, (vQ s hs).beq v_tid, (vQ s hs).beq vJ] at k
    exact ⟨s, hs, k⟩
  · rw [anyE] at k18
    obtain ⟨c, hc, k⟩ := k18
    rw [anyE] at k
    obtain ⟨d, hd, k⟩ := k
    rw [notB_iff, tcK_enc (vH c hc) (vH d hd), memE vQ ((vH c hc).comm' (vH d hd))] at k
    exact ⟨c, hc, d, hd, k⟩
  · intro x hx h3 hne q hq hqx
    rw [allE] at k19
    have vx := vH x hx
    have k := k19 x hx
    rw [impB_iff, impB_iff, m_enc vx vx, m_enc vx (vx.mul' vx), one_eq,
      (vx.mul' (vx.mul' vx)).beq v_tid, notB_iff, vx.beq v_tid, allE] at k
    have k := k h3 hne q hq
    rw [impB_iff, m_enc (vQ q hq) vx, m_enc vx (vQ q hq), ((vQ q hq).mul' vx).beq (vx.mul' (vQ q hq)),
      oneJ_iff vJ (vQ q hq)] at k
    exact k hqx
  · exact (memE vQ vX).mp k20
  · rw [notB_iff, vX.beq vJ] at k21
    exact k21
  · rw [beq_iff, lenE] at k22
    exact k22
  · rw [beq_iff, lenE] at k23
    exact k23
  · exact nodupE k24
  · exact nodupE k25
  · intro t ht
    rw [allE] at k26
    exact (memE vQ (vQ1 t ht)).mp (k26 t ht)
  · intro t ht
    rw [allE] at k27
    exact (memE vQ (vQ2 t ht)).mp (k27 t ht)
  · exact (memE vQ1 v_tid).mp k28
  · exact (memE vQ2 v_tid).mp k29
  · exact mulClE vQ1 k30
  · exact mulClE vQ2 k31
  · exact invClE vQ1 k32
  · exact invClE vQ2 k33
  · exact normByE vH vQ1 k34
  · exact normByE vH vQ2 k35
  · intro x hx y hy hx4 hx2 hyy hyx
    rw [allE] at k36
    have vx := vQ x hx
    have vy := vQ y hy
    have k := k36 x hx
    rw [allE] at k
    have k := k y hy
    rw [impB_iff, impB_iff, impB_iff, impB_iff, orB_iff, andB_iff, andB_iff, memE vQ1 vx,
      memE vQ1 vy, memE vQ2 vx, memE vQ2 vy, pow_enc vx, pow_enc vx, pow_enc vx, one_eq,
      (vx.pw 4).beq v_tid, notB_iff, (vx.pw 2).beq v_tid, m_enc vy vy,
      (vy.mul' vy).beq (vx.pw 2), m_enc vy vx, m_enc (vx.pw 3) vy,
      (vy.mul' vx).beq ((vx.pw 3).mul' vy)] at k
    exact k hx4 hx2 hyy hyx
  · rw [beq_iff, lenE] at k37
    exact k37
  · exact nodupE k38
  · exact (memE vB v_tid).mp k39
  · exact mulClE vB k40
  · exact invClE vB k41
  · intro t ht
    rw [allE] at k42
    exact (memE vH (vB t ht)).mp (k42 t ht)
  · exact (memE vB vE).mp k43
  · exact (memE vB vN).mp k44
  · exact (memE vB vF).mp k45
  · exact (memE vB vJ).mp k46
  · exact (memE vB vX).mp k47
  · intro s hs hc hss hne
    rw [allE] at k48
    have vs := vB s hs
    have k := k48 s hs
    rw [impB_iff, impB_iff, impB_iff, allE, m_enc vs vs, one_eq, (vs.mul' vs).beq v_tid, notB_iff,
      vs.beq v_tid, vs.beq vJ] at k
    refine k (fun t ht => ?_) hss hne
    rw [m_enc vs (vB t ht), m_enc (vB t ht) vs, (vs.mul' (vB t ht)).beq ((vB t ht).mul' vs)]
    exact hc t ht

end CFSG.KC.Misc.M12Hyp

end
