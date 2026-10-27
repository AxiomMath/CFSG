module

public import Certificates.Data.Kernel.Spor.Fi24TwinK
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.Fi24TwinK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24TwinK CFSG.KC.Benes CFSG.KS.Fi24ThreeO Finset

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

theorem ent_eq (T i : Nat) : ent T i = T / 2 ^ (11 * i) % 2048 := by
  change (T >>> (i * 11)) &&& 2047 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm, show (2047 : Nat) = 2 ^ 11 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem ent_lt (T i : Nat) : ent T i < 2048 := by
  rw [ent_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem digits_sum (f : Nat → Nat) (hf : ∀ j, f j < 2048) : ∀ n,
    ∑ j ∈ range n, f j * 2048 ^ j < 2048 ^ n ∧
      ∀ i < n, (∑ j ∈ range n, f j * 2048 ^ j) / 2048 ^ i % 2048 = f i
  | 0 => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1 => by
    obtain ⟨hb, hd⟩ := digits_sum f hf n
    rw [sum_range_succ]
    refine ⟨?_, fun i hi => ?_⟩
    · have h1 : f n * 2048 ^ n ≤ 2047 * 2048 ^ n := Nat.mul_le_mul_right _ (by have := hf n; omega)
      rw [pow_succ]
      omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have e : 2048 ^ n = 2048 ^ i * (2048 * 2048 ^ (n - i - 1)) := by
          rw [← pow_succ', ← pow_add]
          congr 1
          omega
        rw [e, ← Nat.mul_assoc, Nat.mul_comm (f n), Nat.mul_assoc, Nat.add_mul_div_left _ _
          (Nat.pow_pos (by norm_num)), Nat.add_mod, Nat.mul_left_comm, Nat.mul_mod_right,
          Nat.add_zero, Nat.mod_mod, hd i hi]
      · rw [Nat.mul_comm (f i), Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num)),
          Nat.div_eq_of_lt hb, Nat.zero_add, Nat.mod_eq_of_lt (hf i)]

theorem hiOf_ok (m : Nat) : m ≤ 64 * hiOf m := by
  change m ≤ 64 * Nat.succ (m >>> 6)
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem ent_mkT {m : Nat} {f : Nat → Nat} (hf : ∀ j < m, f j < 2048) {i : Nat} (hi : i < m) :
    ent (mkT m f) i = f i := by
  let g : Nat → Nat := fun j => if j < m then f j else 0
  have hg : ∀ j, g j < 2048 := fun j => by
    simp only [g]
    split_ifs with h
    · exact hf j h
    · norm_num
  have e : mkT m f = ∑ j ∈ range m, g j * 2048 ^ j := by
    unfold mkT
    rw [CFSG.KC.Fi24FixS.sumBelow_eq _ _ _ (hiOf_ok m)]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < m := mem_range.1 hj
    simp only [g, hj', if_true]
    change f j <<< (j * 11) = _
    rw [Nat.shiftLeft_eq, pow_mul', show (2 : Nat) ^ 11 = 2048 by norm_num]
  rw [e, ent_eq, show (2 : Nat) ^ (11 * i) = 2048 ^ i by rw [pow_mul]; norm_num,
    (digits_sum g hg m).2 i hi]
  simp only [g, hi, if_true]

theorem ent_cmpT {m A B : Nat} {i : Nat} (hi : i < m) : ent (cmpT m A B) i = ent A (ent B i) :=
  ent_mkT (fun j _ => ent_lt A _) hi

theorem ent_idT {m i : Nat} (hm : m ≤ 2048) (hi : i < m) : ent (idT m) i = i :=
  ent_mkT (fun j hj => by omega) hi

@[expose] noncomputable def wF (L : List Nat) (u : List Nat) (i : Nat) : Nat :=
  u.foldr (fun l f j => ent (nthL 0 L l) (f j)) id i

theorem wF_cons (L : List Nat) (l : Nat) (u : List Nat) (i : Nat) :
    wF L (l :: u) i = ent (nthL 0 L l) (wF L u i) := rfl

theorem wF_lt {m : Nat} {L : List Nat} (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) :
    ∀ (u : List Nat) {i : Nat}, i < m → wF L u i < m
  | [], _, hi => hi
  | l :: u, _, hi => by
    rw [wF_cons]
    exact hL l _ (wF_lt hL u hi)

theorem ent_wT {m : Nat} (hm : m ≤ 2048) {L : List Nat} (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) :
    ∀ (u : List Nat) {i : Nat}, i < m → ent (wT m L u) i = wF L u i
  | [], _, hi => ent_idT hm hi
  | l :: u, i, hi => by
    change ent (strictN (wT m L u) (fun t => cmpT m (nthL 0 L l) t)) i = _
    rw [CFSG.KS.Fi24NetPt.strictN_eq, ent_cmpT hi, ent_wT hm hL u hi, wF_cons]

theorem nthP_mem {C : List (Nat × Nat)} {i : Nat} (hi : i < C.length) : nthP C i ∈ C := by
  induction C generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a C ih =>
    cases i with
    | zero => exact List.mem_cons_self
    | succ i => exact List.mem_cons_of_mem a (ih (by simpa using hi))

theorem lenL_eq {α : Type} (l : List α) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change Nat.succ (lenL l) = _
    rw [ih, List.length_cons]

theorem cBuild_mem_aux {m n : Nat} (P : Nat × Nat → Prop)
    (hstep : ∀ x y, P x → P y → P (ent x.2 y.1, cmpT m (cmpT m x.2 y.2) x.2)) :
    ∀ (cd : List (Nat × Nat)) (C : List (Nat × Nat)) (j : Nat), (∀ e ∈ C, P e) →
      C.length = n + j →
      allI (fun k e => andB (Nat.blt e.1 (Nat.add n k)) (Nat.blt e.2 (Nat.add n k))) cd j = true →
        ∀ e ∈ cBuild m C cd, P e := by
  intro cd
  induction cd with
  | nil => exact fun C _ hC _ _ => hC
  | cons d cd ih =>
    intro C j hC hlen hok
    obtain ⟨h0, hrest⟩ := andB_true hok
    obtain ⟨h1, h2⟩ := andB_true h0
    have hx : d.1 < C.length := by
      rw [hlen]
      exact Nat.blt_eq.mp h1
    have hy : d.2 < C.length := by
      rw [hlen]
      exact Nat.blt_eq.mp h2
    change ∀ e ∈ cBuild m (C ++ [(ent (nthP C d.1).2 (nthP C d.2).1,
      cmpT m (cmpT m (nthP C d.1).2 (nthP C d.2).2) (nthP C d.1).2)]) cd, P e
    refine ih _ (Nat.succ j) (fun e he => ?_) ?_ hrest
    · rcases List.mem_append.1 he with he | he
      · exact hC e he
      · rw [List.mem_singleton.1 he]
        exact hstep _ _ (hC _ (nthP_mem hx)) (hC _ (nthP_mem hy))
    · rw [List.length_append, List.length_singleton, hlen]
      rfl

theorem cBuild_mem {m : Nat} (P : Nat × Nat → Prop)
    (hstep : ∀ x y, P x → P y → P (ent x.2 y.1, cmpT m (cmpT m x.2 y.2) x.2))
    {cd : List (Nat × Nat)} {C : List (Nat × Nat)} (hC : ∀ e ∈ C, P e)
    (hok : cdOK C.length cd = true) : ∀ e ∈ cBuild m C cd, P e :=
  cBuild_mem_aux P hstep cd C 0 hC rfl hok

private theorem tka_sum_pow_lt (p : Nat → Nat) :
    ∀ (m K : Nat), (∀ i < m, p i < K) → (∀ i j, i < j → j < m → p i < p j) →
      ∑ i ∈ range m, 2 ^ p i < 2 ^ K
  | 0, K, _, _ => by
    rw [Finset.sum_range_zero]
    exact Nat.two_pow_pos K
  | m + 1, K, hlt, hinc => by
    have hpm : p m < K := hlt m (by omega)
    have hlt' : ∀ i < m, p i < p m := fun i hi => hinc i m (by omega) (by omega)
    have hinc' : ∀ i j, i < j → j < m → p i < p j :=
      fun i j hij hj => hinc i j hij (by omega)
    have ih := tka_sum_pow_lt p m (p m) hlt' hinc'
    rw [Finset.sum_range_succ]
    calc ∑ i ∈ range m, 2 ^ p i + 2 ^ p m
        < 2 ^ p m + 2 ^ p m := by omega
      _ = 2 ^ (p m + 1) := by rw [pow_succ']; ring
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem tka_testBit_sum_pow (p : Nat → Nat) :
    ∀ (m : Nat), (∀ i j, i < j → j < m → p i < p j) →
      ∀ x, (∑ i ∈ range m, 2 ^ p i).testBit x = true ↔ ∃ i < m, p i = x
  | 0, _, x => by
    rw [Finset.sum_range_zero]
    simp
  | m + 1, hinc, x => by
    have hinc' : ∀ i j, i < j → j < m → p i < p j :=
      fun i j hij hj => hinc i j hij (by omega)
    have ih := tka_testBit_sum_pow p m hinc' x
    have hlt : ∑ i ∈ range m, 2 ^ p i < 2 ^ p m :=
      tka_sum_pow_lt p m (p m) (fun i hi => hinc i m (by omega) (by omega)) hinc'
    rw [Finset.sum_range_succ]
    have e : ∑ i ∈ range m, 2 ^ p i + 2 ^ p m =
        2 ^ p m * 1 + ∑ i ∈ range m, 2 ^ p i := by
      rw [Nat.mul_one, Nat.add_comm]
    rw [e, Nat.testBit_two_pow_mul_add 1 hlt x]
    by_cases hx : x < p m
    · rw [if_pos hx, ih]
      constructor
      · rintro ⟨i, hi, hpi⟩
        exact ⟨i, by omega, hpi⟩
      · rintro ⟨i, hi, hpi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hie
        · exact ⟨i, hi', hpi⟩
        · rw [hie] at hpi
          omega
    · rw [if_neg hx]
      have h1 : (1 : Nat).testBit (x - p m) = decide (x - p m = 0) := by
        rw [show (1 : Nat) = 2 ^ 0 by norm_num, Nat.testBit_two_pow]
        simp [eq_comm]
      rw [h1, decide_eq_true_iff]
      constructor
      · intro hz
        exact ⟨m, by omega, by omega⟩
      · rintro ⟨i, hi, hpi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hie
        · have := hinc i m hi' (by omega)
          omega
        · rw [hie] at hpi
          omega

private theorem tka_mono {p : Nat → Nat} {m : Nat}
    (h : ∀ k < m - 1, p k < p (Nat.succ k)) :
    ∀ j, j < m → ∀ i < j, p i < p j := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    have hj' : j < m := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hij | hie
    · exact lt_trans (ih hj' i hij) (h j (by omega))
    · rw [hie]
      exact h j (by omega)

theorem plF_testBit {m F : Nat} (hinc : ∀ i j, i < j → j < m → pt F i < pt F j) (x : Nat) :
    (plF m F).testBit x = true ↔ ∃ i < m, pt F i = x := by
  have h : plF m F = ∑ i ∈ range m, 2 ^ (pt F i) := by
    change sumBelow m (hiOf m) (fun i => 1 <<< pt F i) = ∑ i ∈ range m, 2 ^ (pt F i)
    rw [CFSG.KC.Fi24FixS.sumBelow_eq m (hiOf m) (fun i => 1 <<< pt F i) (hiOf_ok m)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h]
  exact tka_testBit_sum_pow (pt F) m hinc x

theorem fsOK_spec (hV : VN NW NT) {w : List Nat} {m F : Nat} (h : fsOK NW NT w m F = true) :
    1 ≤ m ∧ m ≤ 2048 ∧ pt F 0 = 0 ∧ (∀ i j, i < j → j < m → pt F i < pt F j) ∧
      (∀ x, (plF m F).testBit x = true ↔ ∃ i < m, pt F i = x) ∧
      ∀ x, (x < 306936 ∧ cP NW NT w x = x) ↔ ∃ i < m, pt F i = x := by
  unfold fsOK at h
  obtain ⟨hA, h⟩ := CFSG.KC.Benes.andB_true h
  obtain ⟨hB, h⟩ := CFSG.KC.Benes.andB_true h
  obtain ⟨hC, h⟩ := CFSG.KC.Benes.andB_true h
  obtain ⟨hD, hE⟩ := CFSG.KC.Benes.andB_true h
  have hAeq : plF m F = fixC NW NT w := Nat.eq_of_beq_eq_true hA
  have hm2048 : m ≤ 2048 := Nat.le_of_ble_eq_true hD
  have h1m : 1 ≤ m := Nat.le_of_ble_eq_true hE
  have h0 : pt F 0 = 0 := Nat.eq_of_beq_eq_true hC
  have hadj : ∀ i < m - 1, pt F i < pt F (Nat.succ i) := by
    intro i hi
    have hm : m - 1 ≤ 64 * hiOf m := by have := hiOf_ok m; omega
    have := CFSG.KC.Fi24FixS.allBelow_spec hB hm i hi
    rwa [Nat.blt_eq] at this
  have hinc : ∀ i j, i < j → j < m → pt F i < pt F j :=
    fun i j hij hj => tka_mono hadj j hj i hij
  refine ⟨h1m, hm2048, h0, hinc, plF_testBit hinc, fun x => ?_⟩
  rw [← plF_testBit hinc x, hAeq]
  exact (testBit_fixC hV w x).symm

private theorem tkb_pt_lt (F i : Nat) : pt F i < 524288 := by
  rw [show (524288 : Nat) = 2 ^ 19 by norm_num]
  exact Nat.and_lt_two_pow _ (by norm_num)

private theorem tkb_mask_testBit (s : Finset Nat) (j : Nat) :
    (∑ i ∈ s, 2 ^ i).testBit j = decide (j ∈ s) := by
  have h := Finset.toFinset_bitIndices_sum_two_pow s
  have hiff : (∑ i ∈ s, 2 ^ i).testBit j = true ↔ j ∈ s := by
    rw [← Nat.mem_bitIndices, ← List.mem_toFinset, h]
  cases hb : (∑ i ∈ s, 2 ^ i).testBit j <;> by_cases hj : j ∈ s <;>
    simp [hb, hj] at hiff ⊢

private theorem tkb_bitN_eq (n k : Nat) : bitN n k = (n.testBit k).toNat := by
  unfold bitN
  change (n >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

private theorem tkb_decide_bitN (n k : Nat) : decide (bitN n k = 1) = n.testBit k := by
  rw [tkb_bitN_eq]
  cases h : n.testBit k <;> rfl

private theorem tkb_jk_testBit {m F T k i : Nat}
    (hinc : ∀ a b, a < b → b < m → pt F a < pt F b) (hi : i < m) :
    (jk m F T k).testBit (pt F i) = (ent T i).testBit k := by
  have hinj : ∀ a < m, ∀ b < m, pt F a = pt F b → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (Nat.ne_of_lt (hinc a b h hb))
    · exact h
    · exact absurd hab.symm (Nat.ne_of_lt (hinc b a h ha))
  set S : Finset Nat := (Finset.range m).filter (fun a => bitN (ent T a) k = 1) with hS
  have hf : ∀ a, nIf(Nat.beq (bitN (ent T a) k) 1, 1 <<< pt F a, 0)
      = if bitN (ent T a) k = 1 then 2 ^ pt F a else 0 := by
    intro a
    simp only [CFSG.Certificates.LceP.brec_eq, Nat.beq_eq, Nat.one_shiftLeft]
  have hsum : jk m F T k = ∑ e ∈ S.image (pt F), 2 ^ e := by
    unfold jk
    rw [CFSG.KC.Fi24FixS.sumBelow_eq _ _ _ (hiOf_ok m)]
    have hinjS : Set.InjOn (pt F) ↑S := by
      intro a ha b hb hab
      have haS : a ∈ S := by simpa using ha
      have hbS : b ∈ S := by simpa using hb
      have ha' : a < m := by
        rw [hS, Finset.mem_filter] at haS
        exact Finset.mem_range.1 haS.1
      have hb' : b < m := by
        rw [hS, Finset.mem_filter] at hbS
        exact Finset.mem_range.1 hbS.1
      exact hinj a ha' b hb' hab
    calc ∑ a ∈ Finset.range m, nIf(Nat.beq (bitN (ent T a) k) 1, 1 <<< pt F a, 0)
        = ∑ a ∈ Finset.range m,
            (if bitN (ent T a) k = 1 then 2 ^ pt F a else 0) :=
          Finset.sum_congr rfl (fun a _ => hf a)
      _ = ∑ a ∈ S, 2 ^ pt F a := by
          rw [hS]
          exact (Finset.sum_filter (fun a => bitN (ent T a) k = 1)
            (fun a => 2 ^ pt F a)).symm
      _ = ∑ e ∈ S.image (pt F), 2 ^ e :=
          (Finset.sum_image (s := S) (g := pt F) hinjS).symm
  rw [hsum]
  have hmem : pt F i ∈ S.image (pt F) ↔ bitN (ent T i) k = 1 := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hap⟩
      have haS : a ∈ S := ha
      have ha' : a < m ∧ bitN (ent T a) k = 1 := by
        rw [hS, Finset.mem_filter] at haS
        exact ⟨Finset.mem_range.1 haS.1, haS.2⟩
      have hEq : a = i := hinj a ha'.1 i hi hap
      rw [hEq] at ha'
      exact ha'.2
    · intro hbit
      refine ⟨i, ?_, rfl⟩
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_range.2 hi, hbit⟩
  simp only [tkb_mask_testBit, hmem, tkb_decide_bitN]

theorem tabOK_spec (hV : VN NW NT) {m F : Nat} (hm : m ≤ 2048)
    (hinc : ∀ i j, i < j → j < m → pt F i < pt F j) {cs : List Nat} {T : Nat}
    (h : tabOK NW NT m F cs T = true) :
    ∀ i < m, ent T i < m ∧ cP NW NT cs (pt F i) = pt F (ent T i) := by
  unfold tabOK at h
  rw [CFSG.Certificates.LceP.letB_eq, CFSG.Certificates.LceP.letB_eq,
    CFSG.Certificates.LceP.andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hP : Nat.land (wkC NW NT cs (plF m F)) (plF m F) = plF m F :=
    Nat.eq_of_beq_eq_true h1
  intro i hi
  have hPpt : (plF m F).testBit (pt F i) = true :=
    (plF_testBit hinc (pt F i)).2 ⟨i, hi, rfl⟩
  have hPq : (plF m F).testBit (cP NW NT cs (pt F i)) = true := by
    have hland : (Nat.land (wkC NW NT cs (plF m F)) (plF m F)).testBit (pt F i) = true := by
      rw [hP]
      exact hPpt
    rw [Nat.land_eq, Nat.testBit_and, testBit_wkC hV cs (plF m F) (tkb_pt_lt F i), hPpt,
      Bool.and_true] at hland
    exact hland
  obtain ⟨j, hj, hpj⟩ := (plF_testBit hinc (cP NW NT cs (pt F i))).1 hPq
  have hbits : ∀ k < 11, j.testBit k = (ent T i).testBit k := by
    intro k hk11
    have hk : Nat.land (wkC NW NT cs (jk m F (idT m) k)) (plF m F) = jk m F T k :=
      Nat.eq_of_beq_eq_true (CFSG.KC.Fi24FixS.allBelow_spec h2 (by norm_num) k hk11)
    have hL : (Nat.land (wkC NW NT cs (jk m F (idT m) k)) (plF m F)).testBit (pt F i)
        = (jk m F (idT m) k).testBit (pt F j) := by
      rw [Nat.land_eq, Nat.testBit_and, testBit_wkC hV cs (jk m F (idT m) k) (tkb_pt_lt F i),
        ← hpj, hPpt, Bool.and_true]
    have e1 : (Nat.land (wkC NW NT cs (jk m F (idT m) k)) (plF m F)).testBit (pt F i)
        = (jk m F T k).testBit (pt F i) := by rw [hk]
    have e2 : (jk m F (idT m) k).testBit (pt F j) = (ent (idT m) j).testBit k :=
      tkb_jk_testBit hinc hj
    have e3 : (jk m F T k).testBit (pt F i) = (ent T i).testBit k :=
      tkb_jk_testBit hinc hi
    rw [hL, e2, ent_idT hm hj] at e1
    rw [e3] at e1
    exact e1
  have hjeq : ent T i = j := by
    apply Eq.symm
    apply Nat.eq_of_testBit_eq
    intro k
    rcases lt_or_ge k 11 with hk | hk
    · exact hbits k hk
    · have hle : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have hj2 : j < 2 ^ 11 := by
        rw [show (2 : Nat) ^ 11 = 2048 by norm_num]
        omega
      have he2 : ent T i < 2 ^ 11 := by
        rw [show (2 : Nat) ^ 11 = 2048 by norm_num]
        exact ent_lt T i
      rw [Nat.testBit_lt_two_pow (show j < 2 ^ k by omega),
        Nat.testBit_lt_two_pow (show ent T i < 2 ^ k by omega)]
  refine ⟨?_, ?_⟩
  · rw [hjeq]; exact hj
  · rw [hjeq]; exact hpj.symm

private theorem tkc_notB_true {a : Bool} (h : notB a = true) : a = false := by
  cases a <;> simp_all [notB]

private theorem tkc_orB_false_left {b : Bool} (h : orB false b = true) : b = true := by
  simpa [orB] using h

private theorem tkc_eqB_true {a b : Bool} (h : eqB a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [eqB, notB]

private theorem tkc_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem tkc_nthL_eq {α : Type} (d : α) (l : List α) (i : Nat) :
    nthL d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem rowOK_spec {m T0 p T : Nat} (h : rowOK m T0 p T = true) :
    ent T0 p ≠ p ∧ ∀ i < m, i ≠ 0 → i ≠ p → (ent T0 i = i ↔ ent T i = i) := by
  unfold rowOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  have hb : Nat.beq (ent T0 p) p = false := tkc_notB_true h1
  refine ⟨?_, fun i hi hi0 hip => ?_⟩
  · intro he
    have ht : Nat.beq (ent T0 p) p = true := by
      rw [Nat.beq_eq]
      exact he
    rw [hb] at ht
    exact Bool.noConfusion ht
  · have hf := CFSG.KC.Fi24FixS.allBelow_spec h2 (hiOf_ok m) i hi
    dsimp only at hf
    rw [tkc_beq_false hi0, tkc_beq_false hip] at hf
    have heq : eqB (Nat.beq (ent T0 i) i) (Nat.beq (ent T i) i) = true :=
      tkc_orB_false_left (tkc_orB_false_left hf)
    have hbeq := tkc_eqB_true heq
    constructor
    · intro he
      have ht : Nat.beq (ent T i) i = true := by
        rw [← hbeq, Nat.beq_eq]
        exact he
      exact Nat.eq_of_beq_eq_true ht
    · intro he
      have ht : Nat.beq (ent T0 i) i = true := by
        rw [hbeq, Nat.beq_eq]
        exact he
      exact Nat.eq_of_beq_eq_true ht

private theorem tkd_beq_bitN (x k : Nat) : Nat.beq (bitN x k) 1 = x.testBit k := by
  unfold bitN
  change Nat.beq ((x >>> k) &&& 1) 1 = x.testBit k
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> rw [h] <;> decide

private theorem tkd_testBit_land (a b q : Nat) :
    (Nat.land a b).testBit q = (a.testBit q && b.testBit q) := by
  change (a &&& b).testBit q = _
  rw [Nat.testBit_land]

private theorem tkd_testBit_lor (a b q : Nat) :
    (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) := by
  change (a ||| b).testBit q = _
  rw [Nat.testBit_lor]

private theorem tkd_testBit_xor (a b q : Nat) :
    (Nat.xor a b).testBit q = (a.testBit q ^^ b.testBit q) := by
  change (a ^^^ b).testBit q = _
  rw [Nat.testBit_xor]

private theorem tkd_testBit_shiftLeft_one (n m : Nat) :
    (Nat.shiftLeft 1 n).testBit m = decide (n = m) := by
  change (1 <<< n).testBit m = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem tkd_notB_false {a : Bool} (h : notB a = true) : a = false := by
  cases a
  · rfl
  · simp [notB] at h

private theorem tkd_nbeq_ne {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := by
  have hb := tkd_notB_false h
  intro e
  rw [e, Nat.beq_refl] at hb
  exact Bool.noConfusion hb

private theorem tkd_pt_lt (F i : Nat) : pt F i < 524288 := by
  unfold pt
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

private theorem tkd_plC_testBit (F : Nat) : ∀ (C : List (Nat × Nat)) (x : Nat),
    (plC F C).testBit x = true ↔ ∃ e ∈ C, pt F e.1 = x
  | [], x => by
    change (0 : Nat).testBit x = true ↔ _
    simp
  | e :: C, x => by
    change (Nat.lor (Nat.shiftLeft 1 (pt F e.1)) (plC F C)).testBit x = true ↔ _
    rw [tkd_testBit_lor, Bool.or_eq_true, tkd_plC_testBit F C x,
      tkd_testBit_shiftLeft_one, decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact ⟨e, List.mem_cons_self, h⟩
      · obtain ⟨e', he', hpt⟩ := h
        exact ⟨e', List.mem_cons_of_mem e he', hpt⟩
    · rintro ⟨e', he', hpt⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact Or.inl hpt
      · exact Or.inr ⟨e', he', hpt⟩

private theorem tkd_foldA_testBit (B : Nat) (g : List Nat → Nat) (p : Nat) :
    ∀ xt : List (List Nat), B.testBit p = true →
      (∀ W ∈ xt, (g W).testBit p = true) →
      (List.rec (motive := fun _ => Nat) B
        (fun W _ ih => strictN ih (fun a => Nat.land a (g W))) xt).testBit p = true
  | [], hb, _ => hb
  | W :: t, hb, hg => by
    change (strictN (List.rec (motive := fun _ => Nat) B
      (fun W _ ih => strictN ih (fun a => Nat.land a (g W))) t)
        (fun a => Nat.land a (g W))).testBit p = true
    rw [CFSG.KS.Fi24NetPt.strictN_eq, tkd_testBit_land,
      tkd_foldA_testBit B g p t hb (fun V hV => hg V (List.mem_cons_of_mem W hV)),
      hg W List.mem_cons_self]
    rfl

theorem k2OK_spec_ (hV : VN NW NT) {m F : Nat} (hm : m ≤ 2048)
    (hinc : ∀ i j, i < j → j < m → pt F i < pt F j) {xt : List (List Nat)} {C : List (Nat × Nat)}
    (hxt : ∀ W ∈ xt, ∀ i < m, cP NW NT (invC W) (pt F i) < 306936)
    (h : k2OK NW NT m F xt C = true) :
    (∀ W ∈ xt, cP NW NT W 0 ≠ 0 ∧ cP NW NT [26] (cP NW NT W 0) = cP NW NT W 0 ∧
      ∃ i < m, pt F i = cP NW NT W 0) ∧
    ∀ i < m, cP NW NT [26] (pt F i) ≠ pt F i →
      (∀ W ∈ xt, cP NW NT [26] (cP NW NT (invC W) (pt F i)) = cP NW NT (invC W) (pt F i)) →
        ∃ e ∈ C, pt F e.1 = pt F i := by
  unfold k2OK at h
  simp only [CFSG.KS.Fi24Net.letB_eq'] at h
  obtain ⟨hAll, hAok⟩ := andB_true h
  constructor
  · intro W hW
    obtain ⟨hbits, hne⟩ := andB_true (allL_spec hAll W hW)
    obtain ⟨hbitFT, hbitP⟩ := andB_true hbits
    have hFTt : (fixC NW NT [26]).testBit (ptC NW NT W 0) = true := by
      rw [← tkd_beq_bitN]
      exact hbitFT
    have hPt : (plF m F).testBit (ptC NW NT W 0) = true := by
      rw [← tkd_beq_bitN]
      exact hbitP
    obtain ⟨_, hfix⟩ := (testBit_fixC hV [26] (ptC NW NT W 0)).1 hFTt
    have ht : cP NW NT W 0 = ptC NW NT W 0 := (ptC_eq NW NT W 0).symm
    have hPt' : (plF m F).testBit (cP NW NT W 0) = true := by
      rwa [ht]
    obtain ⟨i, hi, hpi⟩ := (plF_testBit hinc (cP NW NT W 0)).1 hPt'
    exact ⟨by rw [ht]; exact tkd_nbeq_ne hne, by simpa [ht] using hfix, ⟨i, hi, hpi⟩⟩
  · intro i hi hTmove hfixW
    have hptlt : pt F i < 524288 := tkd_pt_lt F i
    have hPbit : (plF m F).testBit (pt F i) = true :=
      (plF_testBit hinc (pt F i)).2 ⟨i, hi, rfl⟩
    have hFTfalse : (fixC NW NT [26]).testBit (pt F i) = false := by
      cases hb : (fixC NW NT [26]).testBit (pt F i) with
      | false => rfl
      | true => exact absurd ((testBit_fixC hV [26] (pt F i)).1 hb).2 hTmove
    have hB : (Nat.xor (plF m F) (Nat.land (plF m F) (fixC NW NT [26]))).testBit
        (pt F i) = true := by
      rw [tkd_testBit_xor, tkd_testBit_land, hPbit, hFTfalse]
      rfl
    have hct : ∀ W ∈ xt,
        (ctP NW NT (fixC NW NT [26]) W).testBit (pt F i) = true := by
      intro W hW
      unfold ctP
      rw [testBit_wkC hV (invC W) (fixC NW NT [26]) hptlt]
      exact (testBit_fixC hV [26] (cP NW NT (invC W) (pt F i))).2
        ⟨hxt W hW i hi, hfixW W hW⟩
    have hA := tkd_foldA_testBit
      (Nat.xor (plF m F) (Nat.land (plF m F) (fixC NW NT [26])))
      (fun W => ctP NW NT (fixC NW NT [26]) W) (pt F i) xt hB hct
    have hEq := Nat.eq_of_beq_eq_true hAok
    have hpl : (plC F C).testBit (pt F i) = true := by
      have hbit := congrArg (fun n => n.testBit (pt F i)) hEq
      rw [tkd_testBit_land, hA] at hbit
      simpa using hbit
    exact (tkd_plC_testBit F C (pt F i)).1 hpl

@[expose] noncomputable def gF (L : List Nat) (gw : List (List Nat)) (k : Nat) (i : Nat) : Nat :=
  wF L (nthL [] gw k) i

@[expose] noncomputable def gFI (L : List Nat) (gw : List (List Nat)) (k : Nat) (i : Nat) : Nat :=
  wF L (nthL [] gw k).reverse i

@[expose] noncomputable def sF (L : List Nat) (gw : List (List Nat)) (v : List Nat) (i : Nat) : Nat :=
  v.foldr (fun e f j => (if e % 2 = 0 then gF L gw (e / 2) else gFI L gw (e / 2)) (f j)) id i

private theorem tke_nthL_eq {α : Type} (d : α) (l : List α) (i : Nat) :
    nthL d l i = l.getD i d := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => change nthL d l i = _; rw [ih]; rfl

private noncomputable def tke_pk (m : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun t _ ih k => Nat.lor (Nat.shiftLeft t (Nat.mul k (Nat.mul m 11))) (ih (Nat.succ k)))

private theorem tke_zero_mul (n : Nat) : Nat.mul 0 n = 0 := Nat.zero_mul n

private theorem tke_shiftLeft_zero (n : Nat) : Nat.shiftLeft n 0 = n := by
  simpa using (Nat.shiftLeft_zero (n := n))

private theorem tke_pk_shift {m : Nat} (ts : List Nat) (k : Nat) :
    tke_pk m ts k = tke_pk m ts 0 <<< (k * (m * 11)) := by
  induction ts generalizing k with
  | nil =>
    rw [show tke_pk m [] = fun _ => 0 from rfl, Nat.zero_shiftLeft]
  | cons t ts ih =>
    have h0 : tke_pk m (t :: ts) 0 = t ||| tke_pk m ts 1 := by
      change Nat.lor (Nat.shiftLeft t (Nat.mul 0 (Nat.mul m 11)))
        (tke_pk m ts (Nat.succ 0)) = Nat.lor t (tke_pk m ts 1)
      rw [tke_zero_mul, tke_shiftLeft_zero]
    rw [h0]
    change Nat.lor (Nat.shiftLeft t (Nat.mul k (Nat.mul m 11)))
        (tke_pk m ts (Nat.succ k)) = (t ||| tke_pk m ts 1) <<< (k * (m * 11))
    rw [ih (k + 1), ih 1, Nat.shiftLeft_or_distrib]
    congr 1
    rw [← Nat.shiftLeft_add]
    congr 1
    ring

private theorem tke_gPack_eq_pk (m : Nat) (ts : List Nat) : gPack m ts = tke_pk m ts 0 := rfl

private theorem tke_gPack_cons (m t : Nat) (ts : List Nat) :
    gPack m (t :: ts) = t ||| (gPack m ts <<< (m * 11)) := by
  rw [tke_gPack_eq_pk m (t :: ts), tke_gPack_eq_pk m ts]
  change Nat.lor (Nat.shiftLeft t (Nat.mul 0 (Nat.mul m 11)))
      (tke_pk m ts (Nat.succ 0)) = t ||| (tke_pk m ts 0 <<< (m * 11))
  rw [tke_pk_shift ts 1, show (1 : Nat) * (m * 11) = m * 11 by rw [Nat.one_mul],
    tke_zero_mul, tke_shiftLeft_zero]
  rfl

private theorem tke_gAt_eq (m G k : Nat) :
    gAt m G k = G / 2 ^ (k * (m * 11)) % 2 ^ (m * 11) := by
  change (G >>> (k * (m * 11))) &&& CFSG.KC.MonsterConv.Perm.ones (m * 11) = _
  rw [Nat.shiftRight_eq_div_pow, ones_eq, Nat.and_two_pow_sub_one_eq_mod]

private theorem tke_gAt_succ (m G k : Nat) :
    gAt m G (k + 1) = gAt m (G >>> (m * 11)) k := by
  change (G >>> ((k + 1) * (m * 11))) &&& CFSG.KC.MonsterConv.Perm.ones (m * 11) =
    ((G >>> (m * 11)) >>> (k * (m * 11))) &&& CFSG.KC.MonsterConv.Perm.ones (m * 11)
  rw [show (k + 1) * (m * 11) = (m * 11) + k * (m * 11) by ring, Nat.shiftRight_add]

private theorem tke_gAt_or_shift {m t P : Nat} (ht : t < 2 ^ (m * 11)) :
    gAt m (t ||| (P <<< (m * 11))) 0 = t := by
  rw [tke_gAt_eq]
  rw [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
  rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt ht]
  have hP : (P <<< (m * 11)) % 2 ^ (m * 11) = 0 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_mod_left P (2 ^ (m * 11))
  rw [hP, Nat.or_zero]

private theorem tke_gAt_or_shift_succ {m t P k : Nat} (ht : t < 2 ^ (m * 11)) :
    gAt m (t ||| (P <<< (m * 11))) (k + 1) = gAt m P k := by
  have hdiv : (t ||| (P <<< (m * 11))) >>> (m * 11) = P := by
    rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight,
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ht, Nat.zero_or]
  rw [tke_gAt_succ, tke_gAt_eq, tke_gAt_eq, hdiv]

private theorem tke_gAt_gPack {m : Nat} {ts : List Nat}
    (h : ∀ t ∈ ts, t < 2 ^ (m * 11)) {k : Nat} (hk : k < ts.length) :
    gAt m (gPack m ts) k = nthL 0 ts k := by
  induction ts generalizing k with
  | nil => exact absurd hk (by simp)
  | cons t ts ih =>
    have ht : t < 2 ^ (m * 11) := h t List.mem_cons_self
    have hts : ∀ s ∈ ts, s < 2 ^ (m * 11) := fun s hs => h s (List.mem_cons_of_mem t hs)
    rw [tke_gPack_cons]
    cases k with
    | zero => exact tke_gAt_or_shift ht
    | succ k =>
      rw [tke_gAt_or_shift_succ ht]
      exact ih hts (by simpa using hk)

private theorem tke_mkT_lt {m : Nat} {f : Nat → Nat} (hf : ∀ j < m, f j < 2048) :
    mkT m f < 2 ^ (m * 11) := by
  let g : Nat → Nat := fun j => if j < m then f j else 0
  have hg : ∀ j, g j < 2048 := fun j => by
    simp only [g]
    split_ifs with h
    · exact hf j h
    · norm_num
  have e : mkT m f = ∑ j ∈ range m, g j * 2048 ^ j := by
    unfold mkT
    rw [CFSG.KC.Fi24FixS.sumBelow_eq _ _ _ (hiOf_ok m)]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < m := mem_range.1 hj
    simp only [g, hj', if_true]
    change f j <<< (j * 11) = _
    rw [Nat.shiftLeft_eq, pow_mul', show (2 : Nat) ^ 11 = 2048 by norm_num]
  rw [e, show (2 : Nat) ^ (m * 11) = 2048 ^ m by rw [pow_mul']; norm_num]
  exact (digits_sum g hg m).1

private theorem tke_wT_ent_lt {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) (u : List Nat) {i : Nat} (hi : i < m) :
    ent (wT m L u) i < m := by
  rw [ent_wT hm hL u hi]
  exact wF_lt hL u hi

private theorem tke_wT_lt {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) (u : List Nat) :
    wT m L u < 2 ^ (m * 11) := by
  induction u with
  | nil =>
    change mkT m (fun i => i) < 2 ^ (m * 11)
    exact tke_mkT_lt (fun j hj => by omega)
  | cons l u ih =>
    have e : wT m L (l :: u) = cmpT m (nthL 0 L l) (wT m L u) := by
      change strictN (wT m L u) (fun t => cmpT m (nthL 0 L l) t) = _
      rw [CFSG.KS.Fi24NetPt.strictN_eq]
    rw [e]
    exact tke_mkT_lt (fun i hi => by
      have h1 : ent (wT m L u) i < m := tke_wT_ent_lt hm hL u hi
      have := hL l _ h1
      omega)

private theorem tke_revL_eq (u : List Nat) : revL u = u.reverse := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    change revL u ++ [a] = _
    rw [ih, List.reverse_cons]

private theorem tke_gTabs_eq (m : Nat) (L : List Nat) (gw : List (List Nat)) :
    gTabs m L gw = gw.map (fun u => wT m L u) := by
  induction gw with
  | nil => rfl
  | cons u gw ih =>
    change wT m L u :: gTabs m L gw = wT m L u :: gw.map (fun u => wT m L u)
    rw [ih]

private theorem tke_gTabsI_eq (m : Nat) (L : List Nat) (gw : List (List Nat)) :
    gTabsI m L gw = gw.map (fun u => wT m L (revL u)) := by
  induction gw with
  | nil => rfl
  | cons u gw ih =>
    change wT m L (revL u) :: gTabsI m L gw = wT m L (revL u) :: gw.map (fun u => wT m L (revL u))
    rw [ih]

private theorem tke_gTabs_nthL (m : Nat) (L : List Nat) (gw : List (List Nat)) {k : Nat}
    (hk : k < gw.length) :
    nthL 0 (gTabs m L gw) k = wT m L (nthL [] gw k) := by
  induction gw generalizing k with
  | nil => exact absurd hk (by simp)
  | cons u gw ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (by simpa using hk)

private theorem tke_gTabsI_nthL (m : Nat) (L : List Nat) (gw : List (List Nat)) {k : Nat}
    (hk : k < gw.length) :
    nthL 0 (gTabsI m L gw) k = wT m L (revL (nthL [] gw k)) := by
  induction gw generalizing k with
  | nil => exact absurd hk (by simp)
  | cons u gw ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (by simpa using hk)

private theorem tke_ent_gAt_gTabs {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) (gw : List (List Nat)) {k i : Nat}
    (hk : k < gw.length) (hi : i < m) :
    ent (gAt m (gPack m (gTabs m L gw)) k) i = gF L gw k i := by
  have h : ∀ t ∈ gTabs m L gw, t < 2 ^ (m * 11) := by
    intro t ht
    rw [tke_gTabs_eq] at ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 ht
    exact tke_wT_lt hm hL u
  have hk' : k < (gTabs m L gw).length := by rw [tke_gTabs_eq, List.length_map]; exact hk
  rw [tke_gAt_gPack h hk', tke_gTabs_nthL m L gw hk, ent_wT hm hL (nthL [] gw k) hi]
  rfl

private theorem tke_ent_gAt_gTabsI {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) (gw : List (List Nat)) {k i : Nat}
    (hk : k < gw.length) (hi : i < m) :
    ent (gAt m (gPack m (gTabsI m L gw)) k) i = gFI L gw k i := by
  have h : ∀ t ∈ gTabsI m L gw, t < 2 ^ (m * 11) := by
    intro t ht
    rw [tke_gTabsI_eq] at ht
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 ht
    exact tke_wT_lt hm hL (revL u)
  have hk' : k < (gTabsI m L gw).length := by rw [tke_gTabsI_eq, List.length_map]; exact hk
  rw [tke_gAt_gPack h hk', tke_gTabsI_nthL m L gw hk, ent_wT hm hL (revL (nthL [] gw k)) hi,
    tke_revL_eq]
  rfl

private theorem tke_shiftRight_one (e : Nat) : Nat.shiftRight e 1 = e / 2 := by
  change e >>> 1 = e / 2
  rw [Nat.shiftRight_eq_div_pow]

private theorem tke_allI_nthL {α : Type} {d : α} {f : Nat → α → Bool} {l : List α}
    (h : allI f l 0 = true) (j : Nat) (hj : j < l.length) :
    f j (nthL d l j) = true := by
  have h0 := allI_spec h j hj
  simp only [Nat.zero_add] at h0
  rw [← List.getD_eq_getElem (l := l) (d := d) (n := j) hj, ← tke_nthL_eq d l j] at h0
  exact h0

private theorem tke_ent_nIf (c : Bool) (a b j : Nat) :
    ent (nIf(c, a, b)) j = nIf(c, ent a j, ent b j) := by
  cases c <;> rfl

private theorem tke_land_one (e : Nat) : Nat.land e 1 = e % 2 := by
  simpa using (Nat.and_one_is_mod e)

private theorem tke_ent_nIf_beq (e : Nat) (a b j : Nat) :
    ent (nIf(Nat.beq (Nat.land e 1) 0, a, b)) j =
      (if e % 2 = 0 then ent a j else ent b j) := by
  rw [tke_ent_nIf]
  by_cases he : e % 2 = 0
  · have hc : Nat.beq (Nat.land e 1) 0 = true := by
      rw [Nat.beq_eq, tke_land_one]
      exact he
    rw [hc, if_pos he]
  · have hc : Nat.beq (Nat.land e 1) 0 = false := by
      cases hb : Nat.beq (Nat.land e 1) 0 with
      | false => rfl
      | true =>
        rw [Nat.beq_eq, tke_land_one] at hb
        exact absurd hb he
    rw [hc, if_neg he]

private theorem tke_sF_lt {m : Nat} {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) (gw : List (List Nat)) (v : List Nat) :
    ∀ {i : Nat}, i < m → sF L gw v i < m := by
  induction v with
  | nil => intro i hi; simpa [sF] using hi
  | cons e v ih =>
    intro i hi
    have h1 : sF L gw v i < m := ih hi
    rw [show sF L gw (e :: v) i =
        (if e % 2 = 0 then gF L gw (e / 2) else gFI L gw (e / 2)) (sF L gw v i) from rfl]
    by_cases he : e % 2 = 0
    · rw [if_pos he]
      exact wF_lt hL (nthL [] gw (e / 2)) h1
    · rw [if_neg he]
      exact wF_lt hL ((nthL [] gw (e / 2)).reverse) h1

private theorem tke_sT_eq {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {G GI : Nat}
    (hG : ∀ k, k < gw.length → ∀ i < m, ent (gAt m G k) i = gF L gw k i)
    (hGI : ∀ k, k < gw.length → ∀ i < m, ent (gAt m GI k) i = gFI L gw k i) :
    ∀ (v : List Nat), (∀ e ∈ v, e / 2 < gw.length) → ∀ i < m,
      ent (sT m G GI v) i = sF L gw v i := by
  intro v
  induction v with
  | nil =>
    intro _ i hi
    rw [show sT m G GI [] = idT m from rfl, ent_idT hm hi]
    rfl
  | cons e v ih =>
    intro hv i hi
    have hv' : ∀ e' ∈ v, e' / 2 < gw.length := fun e' he' => hv e' (List.mem_cons_of_mem e he')
    have h1 : ent (sT m G GI v) i = sF L gw v i := ih hv' i hi
    have hlt : sF L gw v i < m := tke_sF_lt hL gw v hi
    have hv2 : e / 2 < gw.length := hv e List.mem_cons_self
    rw [show sT m G GI (e :: v) =
        cmpT m (nIf(Nat.beq (Nat.land e 1) 0, gAt m G (e / 2), gAt m GI (e / 2)))
          (sT m G GI v) from by
      change strictN (sT m G GI v) (fun t => cmpT m
        (nIf(Nat.beq (Nat.land e 1) 0, gAt m G (e / 2), gAt m GI (e / 2))) t) = _
      rw [CFSG.KS.Fi24NetPt.strictN_eq]]
    rw [ent_cmpT hi, h1, tke_ent_nIf_beq,
      show sF L gw (e :: v) i =
        (if e % 2 = 0 then gF L gw (e / 2) else gFI L gw (e / 2)) (sF L gw v i) from rfl]
    by_cases he : e % 2 = 0
    · rw [if_pos he, if_pos he, hG (e / 2) hv2 _ hlt]
    · rw [if_neg he, if_neg he, hGI (e / 2) hv2 _ hlt]

theorem nmChk_spec {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {nw : List (List (List Nat))}
    (h : nmChk m L gw nw = true) :
    nw.length ≤ L.length ∧ ∀ c < nw.length, (nthL [] nw c).length = gw.length ∧
      ∀ k < gw.length, (∀ e ∈ nthL [] (nthL [] nw c) k, e / 2 < gw.length) ∧
        ∀ i < m, ent (nthL 0 L c) (gF L gw k (ent (nthL 0 L c) i)) =
          sF L gw (nthL [] (nthL [] nw c) k) i := by
  unfold nmChk at h
  rw [CFSG.Certificates.LceP.letB_eq, CFSG.Certificates.LceP.letB_eq,
    CFSG.Certificates.LceP.andB_iff, Nat.ble_eq] at h
  obtain ⟨hle, hok⟩ := h
  refine ⟨by simpa only [lenL_eq] using hle, fun c hc => ?_⟩
  unfold nmOK at hok
  have hrow := tke_allI_nthL (d := []) hok c hc
  rw [CFSG.Certificates.LceP.andB_iff, CFSG.Certificates.LceP.letB_eq] at hrow
  obtain ⟨hlen, hk2⟩ := hrow
  have hlen' : (nthL [] nw c).length = gw.length := by
    rw [Nat.beq_eq, lenL_eq, lenL_eq] at hlen
    exact hlen
  refine ⟨hlen', fun k hk => ?_⟩
  have hk'' : k < (nthL [] nw c).length := by omega
  have hkrow := tke_allI_nthL (d := []) hk2 k hk''
  rw [CFSG.Certificates.LceP.andB_iff] at hkrow
  obtain ⟨hall, hbeq⟩ := hkrow
  have hall' : ∀ e ∈ nthL [] (nthL [] nw c) k, e / 2 < gw.length := by
    intro e he
    have h := allL_spec hall e he
    rw [Nat.blt_eq, tke_shiftRight_one] at h
    simpa [lenL_eq] using h
  refine ⟨hall', fun i hi => ?_⟩
  have heq := Nat.eq_of_beq_eq_true hbeq
  have hLc : ent (nthL 0 L c) i < m := hL c i hi
  have hG : ∀ k', k' < gw.length → ∀ i' < m,
      ent (gAt m (gPack m (gTabs m L gw)) k') i' = gF L gw k' i' :=
    fun k' hk' i' hi' => tke_ent_gAt_gTabs hm hL gw hk' hi'
  have hGI : ∀ k', k' < gw.length → ∀ i' < m,
      ent (gAt m (gPack m (gTabsI m L gw)) k') i' = gFI L gw k' i' :=
    fun k' hk' i' hi' => tke_ent_gAt_gTabsI hm hL gw hk' hi'
  have hsT := tke_sT_eq hm hL hG hGI (nthL [] (nthL [] nw c) k) hall' i hi
  have hcomp : ent (cmpT m (cmpT m (nthL 0 L c) (gAt m (gPack m (gTabs m L gw)) k))
      (nthL 0 L c)) i = ent (nthL 0 L c) (gF L gw k (ent (nthL 0 L c) i)) := by
    rw [ent_cmpT (A := cmpT m (nthL 0 L c) (gAt m (gPack m (gTabs m L gw)) k))
        (B := nthL 0 L c) hi,
      ent_cmpT (A := nthL 0 L c) (B := gAt m (gPack m (gTabs m L gw)) k) hLc,
      tke_ent_gAt_gTabs hm hL gw hk hLc]
  rw [← hcomp, heq]
  exact hsT

private theorem tke_ent_cmpT_apply {m : Nat} {A B : Nat} {f g : Nat → Nat} {x : Nat}
    (hx : x < m) (hgx : g x < m)
    (hA : ∀ y < m, ent A y = f y) (hB : ∀ y < m, ent B y = g y) :
    ent (cmpT m A B) x = f (g x) := by
  rw [ent_cmpT hx, hA (ent B x) (by rw [hB x hx]; exact hgx), hB x hx]

private theorem tke_ent_cmpT_gFG {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {G : Nat}
    (hG : ∀ k, k < gw.length → ∀ y < m, ent (gAt m G k) y = gF L gw k y) {i j x : Nat}
    (hi : i < gw.length) (hj : j < gw.length) (hx : x < m) :
    ent (cmpT m (gAt m G i) (gAt m G j)) x = gF L gw i (gF L gw j x) :=
  tke_ent_cmpT_apply hx (wF_lt hL (nthL [] gw j) hx) (hG i hi) (hG j hj)

private theorem tke_ent_cmpT_gFI {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {GI : Nat}
    (hGI : ∀ k, k < gw.length → ∀ y < m, ent (gAt m GI k) y = gFI L gw k y) {i j x : Nat}
    (hi : i < gw.length) (hj : j < gw.length) (hx : x < m) :
    ent (cmpT m (gAt m GI i) (gAt m GI j)) x = gFI L gw i (gFI L gw j x) :=
  tke_ent_cmpT_apply hx (wF_lt hL ((nthL [] gw j).reverse) hx) (hGI i hi) (hGI j hj)

private theorem tke_ent_cmpT_Cij {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {G GI : Nat}
    (hG : ∀ k, k < gw.length → ∀ y < m, ent (gAt m G k) y = gF L gw k y)
    (hGI : ∀ k, k < gw.length → ∀ y < m, ent (gAt m GI k) y = gFI L gw k y)
    {i j : Nat} (hi : i < gw.length) (hj : j < gw.length) {y : Nat} (hy : y < m) :
    ent (cmpT m (cmpT m (gAt m GI i) (gAt m GI j)) (cmpT m (gAt m G i) (gAt m G j))) y =
      gFI L gw i (gFI L gw j (gF L gw i (gF L gw j y))) := by
  refine tke_ent_cmpT_apply (x := y) hy ?_
    (fun y hy => tke_ent_cmpT_gFI hm hL hGI hi hj hy)
    (fun y hy => tke_ent_cmpT_gFG hm hL hG hi hj hy)
  exact wF_lt hL (nthL [] gw i) (wF_lt hL (nthL [] gw j) hy)

theorem c2Chk_spec_ {m : Nat} (hm : m ≤ 2048) {L : List Nat}
    (hL : ∀ l, ∀ j < m, ent (nthL 0 L l) j < m) {gw : List (List Nat)} {ab : Bool}
    (hg : gw.length ≤ 64) (h : c2Chk m L gw ab = true) :
    (ab = true → ∀ i < gw.length, ∀ j < gw.length, ∀ x < m,
      gF L gw i (gF L gw j x) = gF L gw j (gF L gw i x)) ∧
    (ab = false → ∀ i < gw.length, ∀ j < gw.length, i < j → ∀ l < gw.length, ∀ x < m,
      gFI L gw i (gFI L gw j (gF L gw i (gF L gw j (gF L gw l x)))) =
        gF L gw l (gFI L gw i (gFI L gw j (gF L gw i (gF L gw j x))))) := by
  cases ab with
  | true =>
    refine ⟨fun _ => ?_, fun hfalse => absurd hfalse (by decide)⟩
    unfold c2Chk at h
    rw [CFSG.Certificates.LceP.letB_eq, CFSG.Certificates.LceP.letB_eq, lenL_eq] at h
    unfold c2OK at h
    have hb : gw.length ≤ 64 * 1 := by omega
    have hG : ∀ k, k < gw.length → ∀ y < m,
        ent (gAt m (gPack m (gTabs m L gw)) k) y = gF L gw k y :=
      fun k hk y hy => tke_ent_gAt_gTabs hm hL gw hk hy
    have pair : ∀ i j, i < gw.length → j < gw.length → ¬ j ≤ i →
        cmpT m (gAt m (gPack m (gTabs m L gw)) i) (gAt m (gPack m (gTabs m L gw)) j) =
          cmpT m (gAt m (gPack m (gTabs m L gw)) j) (gAt m (gPack m (gTabs m L gw)) i) := by
      intro i j hi hj hji
      have hi' := CFSG.KC.Fi24FixS.allBelow_spec h hb i hi
      have hj' := CFSG.KC.Fi24FixS.allBelow_spec hi' hb j hj
      rw [CFSG.Certificates.LceP.orB_iff] at hj'
      rcases hj' with hle | hbif
      · exact absurd (Nat.le_of_ble_eq_true hle) hji
      · have hbeq : Nat.beq (cmpT m (gAt m (gPack m (gTabs m L gw)) i)
            (gAt m (gPack m (gTabs m L gw)) j))
            (cmpT m (gAt m (gPack m (gTabs m L gw)) j)
            (gAt m (gPack m (gTabs m L gw)) i)) = true := by
          simpa using hbif
        exact Nat.eq_of_beq_eq_true hbeq
    have hcmp : ∀ i j, i < gw.length → j < gw.length → ¬ j ≤ i → ∀ x < m,
        gF L gw i (gF L gw j x) = gF L gw j (gF L gw i x) := by
      intro i j hi hj hji x hx
      have h1 := tke_ent_cmpT_gFG hm hL hG hi hj hx
      have h2 := tke_ent_cmpT_gFG hm hL hG hj hi hx
      rw [pair i j hi hj hji] at h1
      rw [h2] at h1
      exact h1.symm
    intro i hi j hj x hx
    by_cases hji : j ≤ i
    · rcases lt_or_eq_of_le hji with hlt | heq
      · exact (hcmp j i hj hi (by omega) x hx).symm
      · subst heq
        rfl
    · exact hcmp i j hi hj hji x hx
  | false =>
    refine ⟨fun htrue => absurd htrue (by decide), fun _ => ?_⟩
    unfold c2Chk at h
    rw [CFSG.Certificates.LceP.letB_eq, CFSG.Certificates.LceP.letB_eq, lenL_eq] at h
    unfold c2OK at h
    have hb : gw.length ≤ 64 * 1 := by omega
    have hG : ∀ k, k < gw.length → ∀ y < m,
        ent (gAt m (gPack m (gTabs m L gw)) k) y = gF L gw k y :=
      fun k hk y hy => tke_ent_gAt_gTabs hm hL gw hk hy
    have hGI : ∀ k, k < gw.length → ∀ y < m,
        ent (gAt m (gPack m (gTabsI m L gw)) k) y = gFI L gw k y :=
      fun k hk y hy => tke_ent_gAt_gTabsI hm hL gw hk hy
    intro i hi j hj hij l hl x hx
    have hi' := CFSG.KC.Fi24FixS.allBelow_spec h hb i hi
    have hj' := CFSG.KC.Fi24FixS.allBelow_spec hi' hb j hj
    rw [CFSG.Certificates.LceP.orB_iff] at hj'
    rcases hj' with hle | hbif
    · have hji : j ≤ i := Nat.le_of_ble_eq_true hle
      omega
    · have hlet : (letB (cmpT m (cmpT m (gAt m (gPack m (gTabsI m L gw)) i)
            (gAt m (gPack m (gTabsI m L gw)) j))
            (cmpT m (gAt m (gPack m (gTabs m L gw)) i)
              (gAt m (gPack m (gTabs m L gw)) j)))
          (fun Cij => allBelow gw.length 1 (fun l =>
            Nat.beq (cmpT m Cij (gAt m (gPack m (gTabs m L gw)) l))
              (cmpT m (gAt m (gPack m (gTabs m L gw)) l) Cij)))) = true := by
        simpa using hbif
      rw [CFSG.Certificates.LceP.letB_eq] at hlet
      have hl' := CFSG.KC.Fi24FixS.allBelow_spec hlet hb l hl
      have heq := Nat.eq_of_beq_eq_true hl'
      have hCij : ∀ {y : Nat}, y < m →
          ent (cmpT m (cmpT m (gAt m (gPack m (gTabsI m L gw)) i)
            (gAt m (gPack m (gTabsI m L gw)) j))
            (cmpT m (gAt m (gPack m (gTabs m L gw)) i)
              (gAt m (gPack m (gTabs m L gw)) j))) y =
          gFI L gw i (gFI L gw j (gF L gw i (gF L gw j y))) :=
        fun hy => tke_ent_cmpT_Cij hm hL hG hGI hi hj hy
      have hleft : ent (cmpT m (cmpT m (cmpT m (gAt m (gPack m (gTabsI m L gw)) i)
            (gAt m (gPack m (gTabsI m L gw)) j))
            (cmpT m (gAt m (gPack m (gTabs m L gw)) i)
              (gAt m (gPack m (gTabs m L gw)) j)))
            (gAt m (gPack m (gTabs m L gw)) l)) x =
          gFI L gw i (gFI L gw j (gF L gw i (gF L gw j (gF L gw l x)))) := by
        refine tke_ent_cmpT_apply hx (wF_lt hL (nthL [] gw l) hx)
          (fun y hy => hCij hy) (fun y hy => hG l hl y hy)
      have hgy : gFI L gw i (gFI L gw j (gF L gw i (gF L gw j x))) < m :=
        wF_lt hL ((nthL [] gw i).reverse)
          (wF_lt hL ((nthL [] gw j).reverse)
            (wF_lt hL (nthL [] gw i) (wF_lt hL (nthL [] gw j) hx)))
      have hright : ent (cmpT m (gAt m (gPack m (gTabs m L gw)) l)
            (cmpT m (cmpT m (gAt m (gPack m (gTabsI m L gw)) i)
              (gAt m (gPack m (gTabsI m L gw)) j))
              (cmpT m (gAt m (gPack m (gTabs m L gw)) i)
                (gAt m (gPack m (gTabs m L gw)) j)))) x =
          gF L gw l (gFI L gw i (gFI L gw j (gF L gw i (gF L gw j x)))) := by
        refine tke_ent_cmpT_apply hx hgy (fun y hy => hG l hl y hy)
          (fun y hy => hCij hy)
      have e := congrArg (fun t => ent t x) heq
      rw [hleft, hright] at e
      exact e

theorem gtOK_spec (hV : VN NW NT) {F : Nat} {C : List (Nat × Nat)} {gt : List (List Nat)}
    (h : gtOK NW NT F C gt = true) :
    gt.length + 1 = C.length ∧ ∀ k < gt.length,
      cP NW NT (nthL [] gt k) 0 = 0 ∧ cP NW NT (nthL [] gt k) (pt F (nthP C (k + 1)).1) = 305530 := by
  unfold gtOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  have hlen : gt.length + 1 = C.length := by
    have e := Nat.eq_of_beq_eq_true h1
    rw [lenL_eq, lenL_eq] at e
    omega
  refine ⟨hlen, fun k hk => ?_⟩
  have hf := CFSG.KS.Fi24ThreeO.allI_spec h2 k hk
  simp only [Nat.zero_add] at hf
  have hget : gt[k] = nthL [] gt k := by
    rw [tkc_nthL_eq, List.getElem_eq_getD]
  rw [hget] at hf
  obtain ⟨ha, hb⟩ := andB_true hf
  constructor
  · rw [CFSG.KS.Fi24ThreeO.ptC_eq] at ha
    exact Nat.eq_of_beq_eq_true ha
  · rw [CFSG.KS.Fi24ThreeO.ptC_eq] at hb
    exact Nat.eq_of_beq_eq_true hb

end CFSG.KS.Fi24TwinK

end
