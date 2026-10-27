module

public import CFSG.Quasithin.Background.B3Facts
public import Certificates.Data.Kernel.B3Mask
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.KC.B3M

open CFSG.Quasithin CFSG.Quasithin.B3

@[expose] def mIdx : Mod → ℕ
  | .u => 0
  | .u0 => 1
  | .ut => 2
  | .ut0 => 3

namespace Dat

variable (d : Dat)

@[expose] noncomputable def tl (i : ℕ) : Tab := (List.range d.n).map (fun p => pt (d.tab i) p)

@[expose] noncomputable def TL : List Tab := (List.range d.nT).map d.tl

@[expose] noncomputable def mL (M : ℕ) : List Tab :=
  ((List.range d.nT).filter (fun y => bit M y)).map d.tl

@[expose] noncomputable def DL (j : ℕ) : List Tab := d.mL (d.dm j)

@[expose] noncomputable def bas (j : ℕ) : List Tab := (lget d.Db j []).map d.tl

@[expose] noncomputable def DD : List (List Tab) := (List.range d.nD).map d.DL

@[expose] noncomputable def ix (i : ℕ) : ℕ := lget d.nmw i 0

end Dat

@[expose] def RepL (d : Dat) (c : ℕ) (L : List Tab) : Prop :=
  (∃ i < d.n / 2, ∀ t, t ∈ L ↔ t ∈ d.DL (d.ix i)) ∨
  (c ≠ 0 ∧ ((∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2 + 1))) ∨
    (∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2))) ∨
    ((∀ t ∈ L, t ∈ d.DL (d.ix (d.n / 2 - 1))) ∧
      2 * L.length = (d.DL (d.ix (d.n / 2 - 1))).length ∧
      ¬ ∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2 + 1))) ∨
    (c = 2 ∧ isE8T d.n L = true)))

structure Ok (d : Dat) : Prop where
  n5 : 5 ≤ d.n
  n8 : d.n ≤ 8
  bp : chkBP = true
  tm : chkTM d = true
  ea : chkEAM d = true
  named : chkNamedM d = true
  amT : ∀ b ∈ d.Am, ∀ x ∈ b, x < d.nT
  a0T : ∀ x ∈ d.A0, x < d.nT

structure ModOK (d : Dat) (k : Mod) : Prop where
  rep_off : ∀ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) →
    offOK d.n k d.DD (d.DL j) = true
  cover : ∀ j < d.nD, offOK d.n k d.DD (d.DL j) = true → ∃ r < d.nD,
    RepL d (caseOf d.n (mIdx k)) (d.DL r) ∧ ∃ g : Tab, isTab d.n g = true ∧
      (∀ b ∈ d.bas r, cjT g b ∈ d.DL j) ∧ (d.DL r).length = (d.DL j).length
  J : ∃ JL G S : List Tab, subOK d.n JL = true ∧ chainOK G (idT d.n) [] S = true ∧
    (∀ g ∈ G, g ∈ S) ∧ (∀ t, t ∈ S ↔ t ∈ JL) ∧
    (∀ g ∈ G, ∃ j < d.nD, offOK d.n k d.DD (d.DL j) = true ∧ g ∈ d.DL j) ∧
    (∀ j < d.nD, offOK d.n k d.DD (d.DL j) = true → ∀ t ∈ d.DL j, t ∈ JL) ∧
    (caseOf d.n (mIdx k) = 0 → ∀ t, t ∈ JL ↔ t ∈ d.DL (d.ix (d.n / 2 - 1))) ∧
    (caseOf d.n (mIdx k) = 2 → ∀ t, t ∈ JL ↔ t ∈ d.TL) ∧
    (caseOf d.n (mIdx k) = 1 → ∃ G5 S5 : List Tab, chainOK G5 (idT d.n) [] S5 = true ∧
      (∀ g ∈ G5, g ∈ S5) ∧ (∀ t, t ∈ S5 ↔ t ∈ JL) ∧
      (∀ g ∈ G5, g ∈ d.DL (d.ix (d.n / 2 - 1)) ∨
        (g ∈ d.TL ∧ mulT g g = idT d.n ∧ suppCardT g = 4)) ∧
      (∀ t ∈ d.DL (d.ix (d.n / 2 - 1)), t ∈ JL) ∧
      ∀ t ∈ d.TL, mulT t t = idT d.n → suppCardT t = 4 → t ∈ JL)
  ranks0 : caseOf d.n (mIdx k) = 0 →
    ∀ i < d.n / 2, rankOK d.n k (d.DL (d.ix i)) (i + 1) (i + 1) = true
  ranksB : caseOf d.n (mIdx k) ≠ 0 →
    (∀ i < d.n / 2, rankOK d.n k (d.DL (d.ix i)) (i + 1)
      (if i + 1 = d.n / 2 then d.n / 2 - 1 else i + 1) = true) ∧
    rankOK d.n k (d.DL (d.ix (d.n / 2))) (d.n / 2) (d.n / 2) = true
  ranksE8 : caseOf d.n (mIdx k) = 2 →
    ∀ j < d.nD, isE8T d.n (d.DL j) = true → rankOK d.n k (d.DL j) 3 3 = true
  q : (∀ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) →
      qRow d.n k (if caseOf d.n (mIdx k) = 0 then 1 else d.n - 2)
        (if caseOf d.n (mIdx k) = 0 then 1 else d.n) (d.DL j) = true) ∧
    ∃ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) ∧
      qWit d.n k (if caseOf d.n (mIdx k) = 0 then 1 else d.n - 2)
        (if caseOf d.n (mIdx k) = 0 then 1 else d.n) (d.DL j) = true
  strong : caseOf d.n (mIdx k) ≠ 0 → ∀ j < d.nD, offOK d.n k d.DD (d.DL j) = true →
    (cntF d.n k [idT d.n] < Fval d.n k (d.DL j) ↔ ∀ t, t ∈ d.DL j ↔ t ∈ d.DL (d.ix (d.n / 2 - 1)))

theorem tmBAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem tmLetB (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem tmAllN {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    have e : allN (m + 1) f = (f m && allN m f) := by
      change Bool.rec (motive := fun _ => Bool) false (allN m f) (f m) = _
      exact tmBAnd _ _
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem tmTestBit_orN {m q : ℕ} {f : ℕ → ℕ} :
    (orN m f).testBit q = true ↔ ∃ i < m, (f i).testBit q = true := by
  induction m with
  | zero =>
    change (0 : ℕ).testBit q = true ↔ _
    simp
  | succ m ih =>
    have e : orN (m + 1) f = f m ||| orN m f := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem tmOne (i : ℕ) : one i = 2 ^ i := by
  change 1 <<< i = 2 ^ i
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem tmOnes (w : ℕ) : ones w = 2 ^ w - 1 := by
  rw [← tmOne]
  rfl

theorem tmTestBit_one {i q : ℕ} : (one i).testBit q = true ↔ i = q := by
  rw [tmOne, Nat.testBit_two_pow, decide_eq_true_iff]

theorem tmTestBit_ones {w q : ℕ} : (ones w).testBit q = true ↔ q < w := by
  rw [tmOnes, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]

theorem tmTestBit_pt (t i k : ℕ) :
    (pt t i).testBit k = (decide (k < 3) && t.testBit (3 * i + k)) := by
  change ((t >>> (3 * i)) &&& (2 ^ 3 - 1)).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem tmPt_lt (t i : ℕ) : pt t i < 8 :=
  Nat.lt_succ_of_le (Nat.and_le_right)

theorem tmTestBit_pack {n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 8) :
    ∀ j, (sumN n (fun i => Nat.shiftLeft (g i) (Nat.mul 3 i))).testBit j =
      (decide (j < 3 * n) && (g (j / 3)).testBit (j % 3)) := by
  induction n with
  | zero =>
    intro j
    change (0 : ℕ).testBit j = _
    simp
  | succ n ih =>
    intro j
    have ih' := ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    have e : sumN (n + 1) (fun i => Nat.shiftLeft (g i) (Nat.mul 3 i)) =
        g n <<< (3 * n) + sumN n (fun i => Nat.shiftLeft (g i) (Nat.mul 3 i)) := rfl
    have hlt : sumN n (fun i => Nat.shiftLeft (g i) (Nat.mul 3 i)) < 2 ^ (3 * n) := by
      refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
      rw [ih']
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inl (by omega)
    rw [e, Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_shiftLeft, ih']
    by_cases h1 : j < 3 * n
    · have h2 : ¬ j ≥ 3 * n := by omega
      have h3 : j < 3 * (n + 1) := by omega
      simp [h1, h2, h3]
    · have h2 : j ≥ 3 * n := by omega
      by_cases h4 : j < 3 * n + 3
      · have h5 : j / 3 = n := by omega
        have h6 : j - 3 * n = j % 3 := by omega
        have h3 : j < 3 * (n + 1) := by omega
        simp [h1, h2, h3, h5, h6]
      · have h3 : ¬ j < 3 * (n + 1) := by omega
        have h7 : (g n).testBit (j - 3 * n) = false :=
          Nat.testBit_eq_false_of_lt ((hg n (Nat.lt_succ_self n)).trans_le
            (by
              calc 8 = 2 ^ 3 := rfl
                _ ≤ 2 ^ (j - 3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h3, h7]

theorem tmPt_pack {n : ℕ} {g : ℕ → ℕ} (hg : ∀ i < n, g i < 8) {p : ℕ} (hp : p < n) :
    pt (sumN n (fun i => Nat.shiftLeft (g i) (Nat.mul 3 i))) p = g p := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [tmTestBit_pt, tmTestBit_pack hg]
  by_cases hk : k < 3
  · have h1 : (3 * p + k) / 3 = p := by omega
    have h2 : (3 * p + k) % 3 = k := by omega
    have h3 : 3 * p + k < 3 * n := by omega
    simp [hk, h1, h2, h3]
  · have h7 : (g p).testBit k = false :=
      Nat.testBit_eq_false_of_lt ((hg p hp).trans_le
        (by
          calc 8 = 2 ^ 3 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hk, h7]

theorem tmEq_of_pt {n a b : ℕ} (ha : a < 2 ^ (3 * n)) (hb : b < 2 ^ (3 * n))
    (h : ∀ p < n, pt a p = pt b p) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 3 * n
  · have h1 := congrArg (fun x => x.testBit (j % 3)) (h (j / 3) (by omega))
    simp only [tmTestBit_pt] at h1
    have e : 3 * (j / 3) + j % 3 = j := by omega
    have hm : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [e] at h1
    simpa [hm] using h1
  · have hle : 2 ^ (3 * n) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hle), Nat.testBit_eq_false_of_lt (hb.trans_le hle)]

theorem tmFactN (n : ℕ) : factN n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (n + 1) * factN n = _
    rw [ih, Nat.factorial_succ]

theorem tmIsTab {n a : ℕ} (h : isPerm n a = true) :
    isTab n ((List.range n).map (fun p => pt a p)) = true ∧ a < 2 ^ (3 * n) ∧
      ∀ p < n, pt a p < n := by
  unfold isPerm at h
  rw [tmBAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, tmOne] at h
  obtain ⟨ha, ho⟩ := h
  have hlt : ∀ p < n, pt a p < n := by
    intro p hp
    have h1 : (orN n (fun i => one (pt a i))).testBit (pt a p) = true :=
      tmTestBit_orN.2 ⟨p, hp, tmTestBit_one.2 rfl⟩
    rw [ho] at h1
    exact tmTestBit_ones.1 h1
  have hsurj : ∀ q < n, ∃ p < n, pt a p = q := by
    intro q hq
    have h1 : (ones n).testBit q = true := tmTestBit_ones.2 hq
    rw [← ho] at h1
    obtain ⟨p, hp, h2⟩ := tmTestBit_orN.1 h1
    exact ⟨p, hp, tmTestBit_one.1 h2⟩
  let f : Fin n → Fin n := fun p => ⟨pt a p, hlt p p.isLt⟩
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨p, hp, h2⟩ := hsurj q q.isLt
    exact ⟨⟨p, hp⟩, Fin.ext h2⟩
  have hfi : Function.Injective f := Finite.injective_iff_surjective.2 hfs
  refine ⟨?_, ha, hlt⟩
  simp only [isTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.length_map, List.length_range, List.mem_map, List.mem_range, true_and]
  refine ⟨?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact hlt p hp
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    rw [List.mem_range] at hx hy
    have := hfi (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Fin.ext hxy)
    exact congrArg Fin.val this

theorem tmTl_getD (d : Dat) {i p : ℕ} (hp : p < d.n) : (d.tl i).getD p 0 = pt (d.tab i) p := by
  unfold Dat.tl
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp

theorem tmLenL {α : Type} (L : List α) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change lenL L + 1 = _
    rw [ih, List.length_cons]

theorem tmLget {α : Type} (L : List α) (i : ℕ) (a : α) : lget L i a = L.getD i a := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change lget L i a = _
      rw [ih, List.getD_cons_succ]

theorem tmAllL {α : Type} {L : List α} {f : α → Bool} : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x L ih =>
    change Bool.rec (motive := fun _ => Bool) false (allL L f) (f x) = true ↔ _
    rw [tmBAnd, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem tmAll2Aux {α β : Type} {dy : β} {f : ℕ → α → β → Bool} : ∀ (X : List α) (Y : List β) (i0 : ℕ),
    List.rec (motive := fun _ => ℕ → List β → Bool) (fun _ _ => true)
      (fun x _ ih i Y => letB i (fun i =>
        List.rec (motive := fun _ => Bool) (bAnd(f i x dy, ih (Nat.add i 1) []))
          (fun y Y' _ => bAnd(f i x y, ih (Nat.add i 1) Y')) Y)) X i0 Y = true →
      ∀ i (hi : i < X.length), f (i0 + i) X[i] (Y.getD i dy) = true
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: X, Y, i0, h, i, hi => by
    dsimp only at h
    rw [tmLetB] at h
    cases Y with
    | nil =>
      dsimp only at h
      rw [tmBAnd, Bool.and_eq_true] at h
      cases i with
      | zero => exact h.1
      | succ i =>
        have := tmAll2Aux X [] (i0 + 1) h.2 i (by simpa using hi)
        rw [Nat.add_right_comm, Nat.add_assoc] at this
        simpa [Nat.add_assoc] using this
    | cons y Y =>
      dsimp only at h
      rw [tmBAnd, Bool.and_eq_true] at h
      cases i with
      | zero => exact h.1
      | succ i =>
        have := tmAll2Aux X Y (i0 + 1) h.2 i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem tmAll2 {α β : Type} {X : List α} {Y : List β} {dy : β} {f : ℕ → α → β → Bool}
    (h : all2 X Y dy f = true) (i : ℕ) (hi : i < X.length) : f i X[i] (Y.getD i dy) = true := by
  have := tmAll2Aux X Y 0 h i hi
  rwa [Nat.zero_add] at this

theorem tmBImp (c t : Bool) : Bool.rec (motive := fun _ => Bool) true t c = (!c || t) := by
  cases c <;> rfl

theorem tmMul (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem tmBit (X i : ℕ) : bit X i = X.testBit i := by
  rw [Bool.eq_iff_iff]
  change Nat.beq ((X >>> i) &&& 1) 1 = true ↔ _
  have e : X.testBit i = decide (X / 2 ^ i % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_div_two_pow, Nat.zero_add]
  rw [Nat.beq_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, e, decide_eq_true_iff]

theorem tmNIf (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem tmTestBit_orN_nIf {m w : ℕ} {p : ℕ → Bool} :
    (orN m (fun x => Bool.rec (motive := fun _ => ℕ) 0 (one x) (p x))).testBit w = true ↔
      w < m ∧ p w = true := by
  rw [tmTestBit_orN]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [tmNIf] at h
    split_ifs at h with hp
    · obtain rfl := tmTestBit_one.1 h
      exact ⟨hx, hp⟩
    · simp at h
  · rintro ⟨hw, hp⟩
    refine ⟨w, hw, ?_⟩
    rw [tmNIf, if_pos hp]
    exact tmTestBit_one.2 rfl

theorem tmInv_lt (d : Dat) {s : ℕ} (h : bit d.invM s = true) : s < d.nT := by
  rw [tmBit] at h
  exact (tmTestBit_orN_nIf.1 h).1

theorem tmSumN (m : ℕ) (f : ℕ → ℕ) : sumN m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change f m + sumN m f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

theorem tmTestBit_ent (X w i b : ℕ) :
    (ent X w i).testBit b = (decide (b < w) && X.testBit (w * i + b)) := by
  change ((X >>> (w * i)) &&& ones w).testBit b = _
  rw [tmOnes, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem tmEnt_lt (X w i : ℕ) : ent X w i < 2 ^ w := by
  change ((X >>> (w * i)) &&& ones w) < _
  rw [tmOnes]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

theorem tmBpT (hbp : chkBP = true) {y : ℕ} (hy : y < 256) :
    ent bpT 4 y = ∑ b ∈ Finset.range 8, if y.testBit b = true then 1 else 0 := by
  unfold chkBP at hbp
  have h1 := tmAllN.1 hbp y hy
  rw [Nat.beq_eq, tmSumN] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [tmNIf, tmBit]

theorem tmPopc (hbp : chkBP = true) (nb X : ℕ) :
    popc nb X = ∑ i ∈ Finset.range (8 * nb), if X.testBit i = true then 1 else 0 := by
  induction nb with
  | zero =>
    change 0 = _
    simp
  | succ nb ih =>
    have e : popc (nb + 1) X = ent bpT 4 (ent X 8 nb) + popc nb X := rfl
    have hlt : ent X 8 nb < 256 := tmEnt_lt X 8 nb
    rw [e, ih, Nat.mul_succ, Finset.sum_range_add, Nat.add_comm (ent bpT 4 _), tmBpT hbp hlt]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    rw [tmTestBit_ent]
    simp [hb]

theorem tmTestBit_cntM (d : Dat) (k W w : ℕ) : ∀ b : List ℕ,
    (List.rec (motive := fun _ => ℕ) W (fun g _ ih => Nat.land (d.fM k g) ih) b).testBit w =
      (W.testBit w && b.all (fun g => (d.fM k g).testBit w))
  | [] => by simp
  | g :: b => by
    have e := Nat.testBit_and (d.fM k g)
      (List.rec (motive := fun _ => ℕ) W (fun g _ ih => Nat.land (d.fM k g) ih) b) w
    rw [tmTestBit_cntM d k W w b] at e
    rw [List.all_cons]
    refine e.trans ?_
    exact Bool.and_left_comm _ _ _

theorem tmBeq (a b : ℕ) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem inW_eq (hbp : chkBP = true) {k : Mod} {n w : ℕ} (hn : n ≤ 8) (hw : w < 2 ^ n) :
    inW (mIdx k) w = inWk n k w := by
  have hw256 : w < 256 := lt_of_lt_of_le hw
    (calc 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 256 := rfl)
  have hpar : Nat.beq (ent bpT 4 w % 2) 0 = popPar n w := by
    rw [tmBpT hbp hw256, popPar, list_sum_range]
    have h1 : ∑ b ∈ Finset.range 8, (if w.testBit b = true then 1 else 0) =
        ∑ i ∈ Finset.range n, (if w.testBit i = true then 1 else 0) := by
      rw [← Finset.sum_range_add_sum_Ico _ hn, Finset.sum_eq_zero (s := Finset.Ico n 8), add_zero]
      intro i hi
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw
        (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Ico.1 hi).1))]
      rfl
    rw [h1, tmBeq]
  cases k
  · rfl
  · exact hpar
  · rfl
  · exact hpar

theorem inN_eq {k : Mod} {n x : ℕ} (hx : x < 2 ^ n) : inN n (mIdx k) x = inNk n k x := by
  cases k
  · change Bool.rec (motive := fun _ => Bool) false true (Nat.beq x 0) = (x % 2 ^ n == 0)
    rw [Nat.mod_eq_of_lt hx, ← tmBeq]
    cases Nat.beq x 0 <;> rfl
  · change Bool.rec (motive := fun _ => Bool) false true (Nat.beq x 0) = (x % 2 ^ n == 0)
    rw [Nat.mod_eq_of_lt hx, ← tmBeq]
    cases Nat.beq x 0 <;> rfl
  · change Bool.rec (motive := fun _ => Bool) (Nat.beq x (ones n)) true (Nat.beq x 0) =
      (x % 2 ^ n == 0 || x % 2 ^ n == 2 ^ n - 1)
    rw [Nat.mod_eq_of_lt hx, ← tmBeq, ← tmBeq, tmOnes]
    cases Nat.beq x 0 <;> rfl
  · change Bool.rec (motive := fun _ => Bool) (Nat.beq x (ones n)) true (Nat.beq x 0) =
      (x % 2 ^ n == 0 || x % 2 ^ n == 2 ^ n - 1)
    rw [Nat.mod_eq_of_lt hx, ← tmBeq, ← tmBeq, tmOnes]
    cases Nat.beq x 0 <;> rfl

theorem tmTestBit_actV {n t m q : ℕ} :
    (actV n t m).testBit q = true ↔ ∃ i < n, m.testBit i = true ∧ pt t i = q := by
  unfold actV
  rw [tmTestBit_orN]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [tmNIf, tmBit]
  split_ifs with h
  · rw [tmTestBit_one]
    exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
  · simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and]
    exact fun h' => absurd h' h

theorem actV_eq (d : Dat) {g m : ℕ} (hg : isPerm d.n (d.tab g) = true) :
    actV d.n (d.tab g) m = actM d.n (d.tl g) m := by
  have hlt := (tmIsTab hg).2.2
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Bool.eq_iff_iff, tmTestBit_actV, actM, testBit_foldl_aux]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [tmTl_getD d hi]

theorem actV_xor_lt {n t w : ℕ} (hg : isPerm n t = true) (hw : w < 2 ^ n) :
    actV n t w ^^^ w < 2 ^ n := by
  have hlt := (tmIsTab hg).2.2
  have h1 : actV n t w < 2 ^ n := by
    refine Nat.lt_pow_two_of_testBit _ fun q hq => ?_
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨i, hi, -, rfl⟩ := tmTestBit_actV.1 h
    exact absurd (hlt i hi) (by omega)
  exact Nat.xor_lt_two_pow h1 hw

@[expose] noncomputable def decT (n a : ℕ) : Tab := (List.range n).map (fun p => pt a p)

@[expose] noncomputable def spanE (d : Dat) (b : List ℕ) (x : ℕ) : ℕ := ent (d.spanP b) d.iw x

@[expose] noncomputable def spanL (d : Dat) (b : List ℕ) : List Tab :=
  (List.range (2 ^ b.length)).map (fun x => d.tl (spanE d b x))

theorem tmAdd (a b : ℕ) : Nat.add a b = a + b := rfl

theorem tmStrictN (y : ℕ) (k : ℕ → ℕ) : Loop.strictN y k = k y := by
  cases y <;> rfl

theorem decT_length (n a : ℕ) : (decT n a).length = n := by simp [decT]

theorem decT_getD {n a p : ℕ} (hp : p < n) : (decT n a).getD p 0 = pt a p := by
  unfold decT
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp

theorem pt_lt_of_decT {n a : ℕ} {σ : Gp n} (h : decT n a = tab σ) {p : ℕ} (hp : p < n) :
    pt a p < n := by
  rw [← decT_getD hp, h, getD_tab σ ⟨p, hp⟩]
  exact (σ ⟨p, hp⟩).isLt

theorem decT_pmul {n a b : ℕ} (hb : ∀ p < n, pt b p < n) :
    decT n (pmul n a b) = mulT (decT n a) (decT n b) := by
  have e : decT n b = (List.range n).map (fun p => pt b p) := rfl
  change (List.range n).map (fun p => pt (pmul n a b) p) = _
  unfold mulT
  rw [e, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  rw [List.mem_range] at hp
  simp only [Function.comp_apply]
  rw [decT_getD (hb p hp)]
  exact tmPt_pack (g := fun i => pt a (pt b i)) (fun i _ => tmPt_lt _ _) hp

theorem decT_pswap {n a b : ℕ} (hn : n ≤ 8) (ha : a < n) (hb : b < n) :
    decT n (pswap n a b) = tab (swapN n a b) := by
  have hs : swapN n a b = Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ := dif_pos ⟨ha, hb⟩
  rw [hs]
  apply List.ext_getElem
  · rw [decT_length, length_tab]
  · intro p h1 h2
    have hp : p < n := by rwa [decT_length] at h1
    rw [getElem_tab]
    have hg : ∀ i < n, nIf(Nat.beq i a, b, nIf(Nat.beq i b, a, i)) < 8 := by
      intro i hi
      simp only [tmNIf, Nat.beq_eq]
      split_ifs <;> omega
    have e : (decT n (pswap n a b))[p] = nIf(Nat.beq p a, b, nIf(Nat.beq p b, a, p)) := by
      simp only [decT, List.getElem_map, List.getElem_range]
      exact tmPt_pack (g := fun i => nIf(Nat.beq i a, b, nIf(Nat.beq i b, a, i))) hg hp
    rw [e]
    simp only [tmNIf, Nat.beq_eq, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff]

theorem mulT_idT {n : ℕ} {t : Tab} (h : t.length = n) : mulT t (idT n) = t := by
  apply List.ext_getElem
  · simp [mulT, idT, h]
  · intro i h1 h2
    simp only [mulT, idT, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ h2]

theorem suppCardT_idT (n : ℕ) : suppCardT (idT n) = 0 := by
  rw [← tab_one, suppCardT_tab]
  simp

theorem supp_eq (n a : ℕ) : supp n a = suppCardT (decT n a) := by
  unfold suppCardT
  rw [decT_length, List.countP_eq_length_filter, length_filter_range]
  change sumN n _ = _
  rw [tmSumN]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [decT_getD hi]
  by_cases h : pt a i = i <;> simp [tmNIf, Nat.beq_eq, h]

theorem evenP_eq (n a : ℕ) : evenP n a = isEvenT (decT n a) := by
  have e1 : sumN n (fun i => sumN i (fun j => nIf(Nat.blt (pt a i) (pt a j), 1, 0))) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if j < i ∧ pt a i < pt a j then 1 else 0 := by
    rw [tmSumN]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [tmSumN, ← Finset.sum_range_add_sum_Ico _ hi.le,
      Finset.sum_eq_zero (s := Finset.Ico i n), add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      by_cases h : pt a i < pt a j <;> simp [tmNIf, Nat.blt_eq, h, hj]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      have : ¬ j < i := by omega
      simp [this]
  have e2 : invCount (decT n a) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if i < j ∧ pt a j < pt a i then 1 else 0 := by
    unfold invCount
    rw [decT_length, list_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [length_filter_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hi hj
    rw [decT_getD hi, decT_getD hj]
    simp
  have e3 : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if j < i ∧ pt a i < pt a j then 1 else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if i < j ∧ pt a j < pt a i then 1 else 0 :=
    Finset.sum_comm
  unfold evenP isEvenT
  rw [e1, e3, ← e2, tmBeq]
  rfl

theorem tmEnt_small {X w : ℕ} (hX : X < 2 ^ w) (i : ℕ) : ent X w i = if i = 0 then X else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [tmTestBit_ent]
  split_ifs with hi
  · subst hi
    rw [Nat.mul_zero, Nat.zero_add]
    by_cases hb : b < w
    · simp [hb]
    · rw [Nat.testBit_eq_false_of_lt (hX.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
  · rw [Nat.zero_testBit]
    by_cases hb : b < w
    · have h1 : w ≤ w * i := Nat.le_mul_of_pos_right w (by omega)
      rw [Nat.testBit_eq_false_of_lt (hX.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp
    · simp [hb]

theorem tmEnt_lor_shift {P Q w z : ℕ} (hP : P < 2 ^ (w * z)) (y : ℕ) :
    ent (Nat.lor P (Nat.shiftLeft Q (Nat.mul w z))) w y =
      if y < z then ent P w y else ent Q w (y - z) := by
  have e1 : Nat.lor P (Nat.shiftLeft Q (Nat.mul w z)) = P ||| Q <<< (w * z) := rfl
  rw [e1]
  apply Nat.eq_of_testBit_eq
  intro b
  split_ifs with hy
  · rw [tmTestBit_ent, tmTestBit_ent]
    by_cases hb : b < w
    · have h1 : w * (y + 1) ≤ w * z := Nat.mul_le_mul_left w hy
      rw [Nat.mul_add, Nat.mul_one] at h1
      have h2 : ¬ (w * z ≤ w * y + b) := by omega
      simp [hb, Nat.testBit_or, Nat.testBit_shiftLeft, h2]
    · simp [hb]
  · rw [tmTestBit_ent, tmTestBit_ent]
    by_cases hb : b < w
    · have h1 : w * z ≤ w * y := Nat.mul_le_mul_left w (by omega)
      have h3 : w * (y - z) + w * z = w * y := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      have h4 : P.testBit (w * y + b) = false :=
        Nat.testBit_eq_false_of_lt (hP.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h5 : w * y + b - w * z = w * (y - z) + b := by omega
      have h6 : w * z ≤ w * y + b := by omega
      simp [hb, Nat.testBit_or, Nat.testBit_shiftLeft, h4, h5, h6]
    · simp [hb]

theorem tmOrN_shift {w : ℕ} {g : ℕ → ℕ} : ∀ z, (∀ x < z, g x < 2 ^ w) →
    orN z (fun x => Nat.shiftLeft (g x) (Nat.mul w x)) < 2 ^ (w * z) ∧
    ∀ y, ent (orN z (fun x => Nat.shiftLeft (g x) (Nat.mul w x))) w y = if y < z then g y else 0
  | 0, _ => by
    refine ⟨Nat.two_pow_pos _, fun y => ?_⟩
    change ent 0 w y = _
    rw [tmEnt_small (Nat.two_pow_pos w)]
    simp
  | z + 1, hg => by
    obtain ⟨h1, h2⟩ := tmOrN_shift z (fun x hx => hg x (by omega))
    have e : orN (z + 1) (fun x => Nat.shiftLeft (g x) (Nat.mul w x)) =
        Nat.lor (orN z (fun x => Nat.shiftLeft (g x) (Nat.mul w x)))
          (Nat.shiftLeft (g z) (Nat.mul w z)) := by
      change Nat.lor _ _ = _
      exact Nat.lor_comm _ _
    rw [e]
    have hgz := hg z (by omega)
    refine ⟨?_, fun y => ?_⟩
    · change _ ||| g z <<< (w * z) < _
      apply Nat.or_lt_two_pow
      · exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by omega)))
      · rw [Nat.shiftLeft_eq, Nat.mul_add, Nat.mul_one, Nat.pow_add]
        have := Nat.two_pow_pos (w * z)
        nlinarith
    · rw [tmEnt_lor_shift h1, h2, tmEnt_small hgz]
      by_cases hy : y < z
      · rw [if_pos hy, if_pos hy, if_pos (by omega)]
      · rw [if_neg hy]
        by_cases hyz : y = z
        · subst hyz
          rw [if_pos (Nat.sub_self y), if_pos (Nat.lt_succ_self y)]
        · rw [if_neg (by omega), if_neg (by omega)]

theorem tmSpanP_cons (d : Dat) (s : ℕ) (c : List ℕ) :
    d.spanP (s :: c) = Nat.lor (d.spanP c) (Nat.shiftLeft (orN (2 ^ c.length)
      (fun x => Nat.shiftLeft (d.mt s (spanE d c x)) (Nat.mul d.iw x)))
        (Nat.mul d.iw (2 ^ c.length))) := by
  have e : d.spanP (s :: c) = Loop.strictN (d.spanP c) (fun P => Loop.strictN (d.row s)
      (fun r => Loop.strictN (one (lenL c)) (fun z => Nat.lor P (Nat.shiftLeft
        (orN z (fun x => Nat.shiftLeft (ent r d.iw (ent P d.iw x)) (Nat.mul d.iw x)))
          (Nat.mul d.iw z))))) := rfl
  rw [e, tmStrictN, tmStrictN, tmStrictN, tmOne, tmLenL]
  rfl

theorem tmSpan_lt (d : Dat) : ∀ b : List ℕ, d.spanP b < 2 ^ (d.iw * 2 ^ b.length)
  | [] => Nat.two_pow_pos _
  | s :: c => by
    rw [tmSpanP_cons]
    have h1 := tmSpan_lt d c
    have h2 := (tmOrN_shift (w := d.iw) (g := fun x => d.mt s (spanE d c x)) (2 ^ c.length)
      (fun x _ => tmEnt_lt _ _ _)).1
    have ez : d.iw * 2 ^ (s :: c).length = d.iw * 2 ^ c.length + d.iw * 2 ^ c.length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_two, Nat.mul_add]
    rw [ez]
    change _ ||| _ <<< (d.iw * 2 ^ c.length) < _
    have hp := Nat.two_pow_pos (d.iw * 2 ^ c.length)
    apply Nat.or_lt_two_pow
    · exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [Nat.shiftLeft_eq, Nat.pow_add]
      nlinarith

theorem tmSpanE_nil (d : Dat) (y : ℕ) : spanE d [] y = 0 := by
  change ent 0 d.iw y = 0
  rw [tmEnt_small (Nat.two_pow_pos _)]
  simp

theorem tmSpanE_cons (d : Dat) (s : ℕ) (c : List ℕ) (y : ℕ) :
    spanE d (s :: c) y = if y < 2 ^ c.length then spanE d c y else
      if y - 2 ^ c.length < 2 ^ c.length then d.mt s (spanE d c (y - 2 ^ c.length)) else 0 := by
  change ent (d.spanP (s :: c)) d.iw y = _
  rw [tmSpanP_cons, tmEnt_lor_shift (tmSpan_lt d c),
    (tmOrN_shift (w := d.iw) (g := fun x => d.mt s (spanE d c x)) (2 ^ c.length)
      (fun x _ => tmEnt_lt _ _ _)).2]
  rfl

theorem tmSpanE_zero (d : Dat) : ∀ b, spanE d b 0 = 0
  | [] => tmSpanE_nil d 0
  | s :: c => by rw [tmSpanE_cons, if_pos (Nat.two_pow_pos _), tmSpanE_zero d c]

theorem tmSpanE_lt (d : Dat) (hnT : 0 < d.nT) (hmt : ∀ i < d.nT, ∀ j < d.nT, d.mt i j < d.nT) :
    ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) → ∀ x, spanE d b x < d.nT
  | [], _, x => by rw [tmSpanE_nil]; exact hnT
  | s :: c, hb, x => by
    have hc : ∀ s ∈ c, s < d.nT := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    rw [tmSpanE_cons]
    split_ifs
    · exact tmSpanE_lt d hnT hmt c hc x
    · exact hmt s (hb s List.mem_cons_self) _ (tmSpanE_lt d hnT hmt c hc _)
    · exact hnT

theorem tmSpanL_cons (d : Dat)
    (hmul : ∀ i < d.nT, ∀ j < d.nT, mulT (d.tl i) (d.tl j) = d.tl (d.mt i j))
    {s : ℕ} {c : List ℕ} (hs : s < d.nT) (hc : ∀ x, spanE d c x < d.nT) :
    spanL d (s :: c) = spanL d c ++ (spanL d c).map (mulT (d.tl s)) := by
  unfold spanL
  rw [List.length_cons, Nat.pow_succ, Nat.mul_two, List.range_add, List.map_append]
  simp only [List.map_map]
  congr 1
  · refine List.map_congr_left fun x hx => ?_
    rw [List.mem_range] at hx
    rw [tmSpanE_cons, if_pos hx]
  · refine List.map_congr_left fun x hx => ?_
    rw [List.mem_range] at hx
    simp only [Function.comp_apply]
    rw [tmSpanE_cons, if_neg (by omega), Nat.add_sub_cancel_left, if_pos hx, hmul s hs _ (hc x)]

theorem chainOK_of_done {G : List Tab} {idt : Tab} :
    ∀ (L done : List Tab), (∀ x ∈ L, x = idt ∨ ∃ g ∈ G, ∃ y ∈ done, mulT g y = x) →
      chainOK G idt done L = true
  | [], _, _ => rfl
  | x :: L, done, h => by
    simp only [chainOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    refine ⟨?_, chainOK_of_done L (x :: done) fun z hz => ?_⟩
    · rcases h x List.mem_cons_self with h1 | ⟨g, hg, y, hy, e⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g, hg, y, hy, e⟩
    · rcases h z (List.mem_cons_of_mem _ hz) with h1 | ⟨g, hg, y, hy, e⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g, hg, y, List.mem_cons_of_mem _ hy, e⟩

theorem chainOK_mono {G G' : List Tab} {idt : Tab} (hG : ∀ g ∈ G, g ∈ G') :
    ∀ (L done : List Tab), chainOK G idt done L = true → chainOK G' idt done L = true
  | [], _, _ => rfl
  | x :: L, done, h => by
    simp only [chainOK, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at h ⊢
    refine ⟨?_, chainOK_mono hG L (x :: done) h.2⟩
    rcases h.1 with h1 | ⟨g, hg, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨g, hG g hg, h2⟩

theorem chainOK_append {G : List Tab} {idt : Tab} (L2 : List Tab) :
    ∀ (L1 done : List Tab), chainOK G idt done (L1 ++ L2) =
      (chainOK G idt done L1 && chainOK G idt (L1.reverse ++ done) L2)
  | [], _ => by simp [chainOK]
  | x :: L1, done => by
    simp only [List.cons_append, chainOK, chainOK_append L2 L1 (x :: done), Bool.and_assoc,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append]

theorem tmSpanL_chain (d : Dat) (hnT : 0 < d.nT)
    (hmt : ∀ i < d.nT, ∀ j < d.nT, d.mt i j < d.nT)
    (hmul : ∀ i < d.nT, ∀ j < d.nT, mulT (d.tl i) (d.tl j) = d.tl (d.mt i j))
    (hid : d.tl 0 = idT d.n) :
    ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) → chainOK (b.map d.tl) (idT d.n) [] (spanL d b) = true
  | [], _ => by
    have e : spanL d [] = [idT d.n] := by
      unfold spanL
      simp [tmSpanE_nil, hid]
    rw [e]
    exact chainOK_of_done _ _ (by simp)
  | s :: c, hb => by
    have hc : ∀ s ∈ c, s < d.nT := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have hs : s < d.nT := hb s List.mem_cons_self
    rw [tmSpanL_cons d hmul hs (tmSpanE_lt d hnT hmt c hc), chainOK_append, Bool.and_eq_true]
    refine ⟨chainOK_mono (fun g hg => ?_) _ _ (tmSpanL_chain d hnT hmt hmul hid c hc),
      chainOK_of_done _ _ fun x hx => ?_⟩
    · rw [List.map_cons]
      exact List.mem_cons_of_mem _ hg
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact Or.inr ⟨d.tl s, by simp, y, by simpa using hy, rfl⟩

theorem tmSpanL_gen (d : Dat) (hnT : 0 < d.nT)
    (hmt : ∀ i < d.nT, ∀ j < d.nT, d.mt i j < d.nT)
    (hmul : ∀ i < d.nT, ∀ j < d.nT, mulT (d.tl i) (d.tl j) = d.tl (d.mt i j))
    (hid : d.tl 0 = idT d.n) :
    ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) → ∀ g ∈ b, d.tl g ∈ spanL d b
  | [], _, g, hg => absurd hg List.not_mem_nil
  | s :: c, hb, g, hg => by
    have hc : ∀ s ∈ c, s < d.nT := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    have hs : s < d.nT := hb s List.mem_cons_self
    rw [tmSpanL_cons d hmul hs (tmSpanE_lt d hnT hmt c hc), List.mem_append]
    rcases List.mem_cons.1 hg with rfl | hg
    · refine Or.inr (List.mem_map.2 ⟨d.tl 0, ?_, ?_⟩)
      · refine List.mem_map.2 ⟨0, List.mem_range.2 (Nat.two_pow_pos _), ?_⟩
        rw [tmSpanE_zero]
      · rw [hid]
        exact mulT_idT (decT_length _ _)
    · exact Or.inl (tmSpanL_gen d hnT hmt hmul hid c hc g hg)

theorem mem_mL (d : Dat) (M : ℕ) (t : Tab) :
    t ∈ d.mL M ↔ ∃ y < d.nT, bit M y = true ∧ d.tl y = t := by
  simp [Dat.mL, List.mem_filter, and_assoc]

theorem tmBit_spanM (d : Dat) (b : List ℕ) (y : ℕ) :
    bit (d.spanM b) y = true ↔ ∃ x < 2 ^ b.length, spanE d b x = y := by
  rw [tmBit]
  change (Loop.strictN (d.spanP b) (fun P => orN (one (lenL b)) (fun x => one (ent P d.iw x)))).testBit
    y = true ↔ _
  simp only [tmStrictN, tmTestBit_orN, tmTestBit_one]
  simp only [tmOne, tmLenL]
  rfl

theorem tmSpanL_iff (d : Dat) {b : List ℕ} (hlt : ∀ x, spanE d b x < d.nT) {M : ℕ}
    (hM : ∀ y, bit M y = true ↔ ∃ x < 2 ^ b.length, spanE d b x = y) (t : Tab) :
    t ∈ spanL d b ↔ t ∈ d.mL M := by
  rw [mem_mL]
  simp only [spanL, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hlt x, (hM _).2 ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, -, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hM y).1 hy
    exact ⟨x, hx, rfl⟩

theorem tmAllIAux {α : Type} {f : ℕ → α → Bool} : ∀ (L : List α) (i0 : ℕ),
    List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun x _ ih i => letB i (fun i => bAnd(f i x, ih (Nat.add i 1)))) L i0 = true →
      ∀ i (hi : i < L.length), f (i0 + i) L[i] = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: L, i0, h, i, hi => by
    dsimp only at h
    rw [tmLetB, tmBAnd, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      have := tmAllIAux L (i0 + 1) h.2 i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem tmAllI {α : Type} {L : List α} {f : ℕ → α → Bool} (h : allI L f = true) (i : ℕ)
    (hi : i < L.length) : f i L[i] = true := by
  have := tmAllIAux L 0 h i hi
  rwa [Nat.zero_add] at this

theorem tmTestBit_orL {α : Type} {L : List α} {f : α → ℕ} {q : ℕ} :
    (orL L f).testBit q = true ↔ ∃ x ∈ L, (f x).testBit q = true := by
  induction L with
  | nil =>
    change (0 : ℕ).testBit q = true ↔ _
    simp
  | cons x L ih =>
    change (f x ||| orL L f).testBit q = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp

theorem tmFacts (d : Dat) (hn8 : d.n ≤ 8) (h : chkTM d = true) :
    0 < d.nT ∧ (∀ i < d.nT, isPerm d.n (d.tab i) = true) ∧
    (∀ i < d.nT, ∀ j < d.nT, d.mt i j < d.nT) ∧
    (∀ i < d.nT, ∀ j < d.nT, mulT (d.tl i) (d.tl j) = d.tl (d.mt i j)) ∧
    d.tl 0 = idT d.n ∧ (∀ i < d.nT, ∀ j < d.nT, d.tl i = d.tl j → i = j) := by
  unfold chkTM at h
  simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmAllN, tmLetB] at h
  obtain ⟨hnT, -, -, h0, hall⟩ := h
  rw [tmOne] at hnT
  have hnT0 : 0 < d.nT := by
    rw [hnT]
    exact Nat.two_pow_pos _
  have hperm : ∀ i < d.nT, isTab d.n (d.tl i) = true ∧ d.tab i < 2 ^ (3 * d.n) ∧
      ∀ p < d.n, pt (d.tab i) p < d.n := fun i hi => tmIsTab (hall i hi).1
  refine ⟨hnT0, fun i hi => (hall i hi).1, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    have h1 : (orN d.nT (fun j => one (ent (d.row i) d.iw j))).testBit (ent (d.row i) d.iw j) =
        true := tmTestBit_orN.2 ⟨j, hj, tmTestBit_one.2 rfl⟩
    rw [(hall i hi).2.2.1] at h1
    exact tmTestBit_ones.1 h1
  · intro i hi j hj
    unfold mulT
    have e1 : d.tl j = (List.range d.n).map (fun p => pt (d.tab j) p) := rfl
    have e2 : d.tl (ent (d.row i) d.iw j) =
        (List.range d.n).map (fun p => pt (d.tab (ent (d.row i) d.iw j)) p) := rfl
    change _ = d.tl (ent (d.row i) d.iw j)
    rw [e1, e2, List.map_map, ← (hall i hi).2.2.2 j hj]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    simp only [Function.comp_apply]
    rw [tmTl_getD d ((hperm j hj).2.2 p hp)]
    exact (tmPt_pack (g := fun i' => pt (d.tab i) (pt (d.tab j) i'))
      (fun i' _ => tmPt_lt _ _) hp).symm
  · unfold Dat.tl idT
    rw [h0]
    conv_rhs => rw [← List.map_id (List.range d.n)]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    exact tmPt_pack (g := fun i => i) (fun i hi => by omega) hp
  · intro i hi j hj hij
    have hab : d.tab i = d.tab j := by
      refine tmEq_of_pt (hperm i hi).2.1 (hperm j hj).2.1 fun p hp => ?_
      rw [← tmTl_getD d hp, ← tmTl_getD d hp, hij]
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have := (hall j hj).2.1 i hlt
      rw [hab] at this
      simp [Nat.beq_refl] at this
    · exact heq
    · have := (hall i hi).2.1 j hgt
      rw [hab] at this
      simp [Nat.beq_refl] at this

theorem chkTM_sound (d : Dat) (hn8 : d.n ≤ 8) (h : chkTM d = true) :
    subOK d.n d.TL = true ∧ d.TL.length = 2 ^ d.e ∧ d.n.factorial = 2 ^ d.e * d.m ∧
      d.m % 2 = 1 := by
  unfold chkTM at h
  simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmAllN, tmLetB] at h
  obtain ⟨hnT, hfac, hm, h0, hall⟩ := h
  rw [tmOne] at hnT hfac
  have hnT0 : 0 < d.nT := by
    rw [hnT]
    exact Nat.two_pow_pos _
  have hperm : ∀ i < d.nT, isTab d.n (d.tl i) = true ∧ d.tab i < 2 ^ (3 * d.n) ∧
      ∀ p < d.n, pt (d.tab i) p < d.n := fun i hi => tmIsTab (hall i hi).1
  have hmtlt : ∀ i < d.nT, ∀ j < d.nT, ent (d.row i) d.iw j < d.nT := by
    intro i hi j _
    have h1 : (orN d.nT (fun j => one (ent (d.row i) d.iw j))).testBit (ent (d.row i) d.iw j) =
        true := tmTestBit_orN.2 ⟨j, by assumption, tmTestBit_one.2 rfl⟩
    rw [(hall i hi).2.2.1] at h1
    exact tmTestBit_ones.1 h1
  have hmt0 : ∀ i < d.nT, ∃ j < d.nT, ent (d.row i) d.iw j = 0 := by
    intro i hi
    have h1 : (ones d.nT).testBit 0 = true := tmTestBit_ones.2 hnT0
    rw [← (hall i hi).2.2.1] at h1
    obtain ⟨j, hj, h2⟩ := tmTestBit_orN.1 h1
    exact ⟨j, hj, tmTestBit_one.1 h2⟩
  have hmul : ∀ i < d.nT, ∀ j < d.nT, mulT (d.tl i) (d.tl j) = d.tl (ent (d.row i) d.iw j) := by
    intro i hi j hj
    unfold mulT
    have e1 : d.tl j = (List.range d.n).map (fun p => pt (d.tab j) p) := rfl
    have e2 : d.tl (ent (d.row i) d.iw j) =
        (List.range d.n).map (fun p => pt (d.tab (ent (d.row i) d.iw j)) p) := rfl
    rw [e1, e2, List.map_map, ← (hall i hi).2.2.2 j hj]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    simp only [Function.comp_apply]
    rw [tmTl_getD d ((hperm j hj).2.2 p hp)]
    exact (tmPt_pack (g := fun i' => pt (d.tab i) (pt (d.tab j) i'))
      (fun i' _ => tmPt_lt _ _) hp).symm
  have hid : d.tl 0 = idT d.n := by
    unfold Dat.tl idT
    rw [h0]
    conv_rhs => rw [← List.map_id (List.range d.n)]
    refine List.map_congr_left fun p hp => ?_
    rw [List.mem_range] at hp
    exact tmPt_pack (g := fun i => i) (fun i hi => by omega) hp
  have hmemT : ∀ t, t ∈ d.TL ↔ ∃ i < d.nT, d.tl i = t := by
    intro t
    simp [Dat.TL]
  have hlen : d.TL.length = d.nT := by simp [Dat.TL]
  refine ⟨?_, by rw [hlen, hnT], by rw [← tmFactN, hfac]; rfl, hm⟩
  simp only [subOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := (hmemT t).1 ht
    exact (hperm i hi).1
  · exact (hmemT _).2 ⟨0, hnT0, hid⟩
  · intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := (hmemT a).1 ha
    obtain ⟨j, hj, rfl⟩ := (hmemT b).1 hb
    rw [hmul i hi j hj]
    exact (hmemT _).2 ⟨_, hmtlt i hi j hj, rfl⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := (hmemT a).1 ha
    obtain ⟨j, hj, hj0⟩ := hmt0 i hi
    obtain ⟨σ, hσ⟩ := exists_tab_eq (hperm i hi).1
    obtain ⟨τ, hτ⟩ := exists_tab_eq (hperm j hj).1
    have h1 : tab (σ * τ) = tab (1 : Gp d.n) := by
      rw [tab_mul, hσ, hτ, hmul i hi j hj, hj0, hid, tab_one]
    have h2 : τ = σ⁻¹ := eq_inv_of_mul_eq_one_right (tab_injective h1)
    rw [← hσ, ← tab_inv, ← h2, hτ]
    exact (hmemT _).2 ⟨j, hj, rfl⟩
  · refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
    rw [List.mem_range] at hi hj
    have hab : d.tab i = d.tab j := by
      refine tmEq_of_pt (hperm i hi).2.1 (hperm j hj).2.1 fun p hp => ?_
      rw [← tmTl_getD d hp, ← tmTl_getD d hp, hij]
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have := (hall j hj).2.1 i hlt
      rw [hab] at this
      simp [Nat.beq_refl] at this
    · exact heq
    · have := (hall i hi).2.1 j hgt
      rw [hab] at this
      simp [Nat.beq_refl] at this

noncomputable def eaG (d : Dat) (y : ℕ) : Gp d.n :=
  if h : isTab d.n (d.tl y) = true then (exists_tab_eq h).choose else 1

def eaSp (d : Dat) (b : List ℕ) (y : ℕ) : Prop := ∃ x < 2 ^ b.length, spanE d b x = y

section EA

variable (d : Dat) (hn8 : d.n ≤ 8) (hT : chkTM d = true)

include hn8 hT

theorem eaG_tab {y : ℕ} (hy : y < d.nT) : tab (eaG d y) = d.tl y := by
  have h : isTab d.n (d.tl y) = true := (tmIsTab ((tmFacts d hn8 hT).2.1 y hy)).1
  unfold eaG
  rw [dif_pos h]
  exact (exists_tab_eq h).choose_spec

theorem eaG_mul {i j : ℕ} (hi : i < d.nT) (hj : j < d.nT) :
    eaG d (d.mt i j) = eaG d i * eaG d j := by
  obtain ⟨-, -, hmt, hmul, -, -⟩ := tmFacts d hn8 hT
  apply tab_injective
  rw [eaG_tab d hn8 hT (hmt i hi j hj), tab_mul, eaG_tab d hn8 hT hi, eaG_tab d hn8 hT hj,
    hmul i hi j hj]

theorem eaG_zero : eaG d 0 = 1 := by
  obtain ⟨hnT, -, -, -, hid, -⟩ := tmFacts d hn8 hT
  apply tab_injective
  rw [eaG_tab d hn8 hT hnT, hid, tab_one]

theorem eaG_inj {i j : ℕ} (hi : i < d.nT) (hj : j < d.nT) (h : eaG d i = eaG d j) : i = j := by
  obtain ⟨-, -, -, -, -, hinj⟩ := tmFacts d hn8 hT
  refine hinj i hi j hj ?_
  rw [← eaG_tab d hn8 hT hi, ← eaG_tab d hn8 hT hj, h]

omit hn8 hT in
theorem eaSp_nil {y : ℕ} : eaSp d [] y ↔ y = 0 := by
  constructor
  · rintro ⟨x, -, rfl⟩
    exact tmSpanE_nil d x
  · rintro rfl
    exact ⟨0, Nat.two_pow_pos _, tmSpanE_nil d 0⟩

omit hn8 hT in
theorem eaSp_cons {s : ℕ} {c : List ℕ} {y : ℕ} :
    eaSp d (s :: c) y ↔ eaSp d c y ∨ ∃ y', eaSp d c y' ∧ d.mt s y' = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [List.length_cons, Nat.pow_succ] at hx
    rw [tmSpanE_cons]
    by_cases h1 : x < 2 ^ c.length
    · rw [if_pos h1]
      exact Or.inl ⟨x, h1, rfl⟩
    · rw [if_neg h1, if_pos (by omega)]
      exact Or.inr ⟨_, ⟨x - 2 ^ c.length, by omega, rfl⟩, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
    · refine ⟨x, ?_, ?_⟩
      · rw [List.length_cons, Nat.pow_succ]
        omega
      · rw [tmSpanE_cons, if_pos hx]
    · refine ⟨x + 2 ^ c.length, ?_, ?_⟩
      · rw [List.length_cons, Nat.pow_succ]
        omega
      · rw [tmSpanE_cons, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]

theorem eaSp_lt {b : List ℕ} (hb : ∀ s ∈ b, s < d.nT) {y : ℕ} (h : eaSp d b y) : y < d.nT := by
  obtain ⟨hnT, -, hmt, -⟩ := tmFacts d hn8 hT
  obtain ⟨x, -, rfl⟩ := h
  exact tmSpanE_lt d hnT hmt b hb x

theorem eaSp_comm (t : ℕ) : ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) →
    (∀ s ∈ b, Commute (eaG d t) (eaG d s)) → ∀ y, eaSp d b y → Commute (eaG d t) (eaG d y)
  | [], _, _, y, h => by
    rw [eaSp_nil] at h
    subst h
    rw [eaG_zero d hn8 hT]
    exact Commute.one_right _
  | s :: c, hb, hc, y, h => by
    have hb' : ∀ x ∈ c, x < d.nT := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hc' : ∀ x ∈ c, Commute (eaG d t) (eaG d x) :=
      fun x hx => hc x (List.mem_cons_of_mem _ hx)
    rcases (eaSp_cons d).1 h with h | ⟨y', hy', rfl⟩
    · exact eaSp_comm t c hb' hc' y h
    · rw [eaG_mul d hn8 hT (hb s List.mem_cons_self) (eaSp_lt d hn8 hT hb' hy')]
      exact (hc s List.mem_cons_self).mul_right (eaSp_comm t c hb' hc' y' hy')

theorem eaSp_facts : ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) → (∀ s ∈ b, eaG d s * eaG d s = 1) →
    (∀ s ∈ b, ∀ s' ∈ b, Commute (eaG d s) (eaG d s')) →
    (∀ y, eaSp d b y → eaG d y * eaG d y = 1) ∧
    ∀ y y', eaSp d b y → eaSp d b y' → Commute (eaG d y) (eaG d y') ∧ eaSp d b (d.mt y y')
  | [], _, _, _ => by
    obtain ⟨hnT, -, hmt, -⟩ := tmFacts d hn8 hT
    refine ⟨fun y h => ?_, fun y y' h h' => ?_⟩
    · rw [eaSp_nil] at h
      subst h
      rw [eaG_zero d hn8 hT, one_mul]
    · rw [eaSp_nil] at h h'
      subst h
      subst h'
      refine ⟨Commute.refl _, ?_⟩
      rw [eaSp_nil]
      refine eaG_inj d hn8 hT (hmt 0 hnT 0 hnT) hnT ?_
      rw [eaG_mul d hn8 hT hnT hnT, eaG_zero d hn8 hT, one_mul]
  | s :: c, hb, hsq, hcm => by
    obtain ⟨-, -, hmt, -⟩ := tmFacts d hn8 hT
    have hb' : ∀ x ∈ c, x < d.nT := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hsq' : ∀ x ∈ c, eaG d x * eaG d x = 1 := fun x hx => hsq x (List.mem_cons_of_mem _ hx)
    have hcm' : ∀ x ∈ c, ∀ x' ∈ c, Commute (eaG d x) (eaG d x') :=
      fun x hx x' hx' => hcm x (List.mem_cons_of_mem _ hx) x' (List.mem_cons_of_mem _ hx')
    obtain ⟨ih1, ih2⟩ := eaSp_facts c hb' hsq' hcm'
    have hs : s < d.nT := hb s List.mem_cons_self
    have hss : eaG d s * eaG d s = 1 := hsq s List.mem_cons_self
    have hsc : ∀ y, eaSp d c y → Commute (eaG d s) (eaG d y) :=
      eaSp_comm d hn8 hT s c hb' (fun x hx => hcm s List.mem_cons_self x (List.mem_cons_of_mem _ hx))
    have hlt : ∀ y, eaSp d c y → y < d.nT := fun y h => eaSp_lt d hn8 hT hb' h
    have hP : ∀ y, eaSp d (s :: c) y → y < d.nT ∧ ∃ u, eaSp d c u ∧
        (eaG d y = eaG d u ∨ eaG d y = eaG d s * eaG d u) := by
      intro y h
      rcases (eaSp_cons d).1 h with h | ⟨u, hu, rfl⟩
      · exact ⟨hlt y h, y, h, Or.inl rfl⟩
      · exact ⟨hmt s hs u (hlt u hu), u, hu, Or.inr (eaG_mul d hn8 hT hs (hlt u hu))⟩
    have hQ : ∀ z, z < d.nT → ∀ u, eaSp d c u →
        (eaG d z = eaG d u ∨ eaG d z = eaG d s * eaG d u) → eaSp d (s :: c) z := by
      intro z hz u hu h
      rcases h with h | h
      · rw [eaG_inj d hn8 hT hz (hlt u hu) h]
        exact (eaSp_cons d).2 (Or.inl hu)
      · rw [← eaG_mul d hn8 hT hs (hlt u hu)] at h
        rw [eaG_inj d hn8 hT hz (hmt s hs u (hlt u hu)) h]
        exact (eaSp_cons d).2 (Or.inr ⟨u, hu, rfl⟩)
    refine ⟨fun y h => ?_, fun y y' h h' => ?_⟩
    · obtain ⟨-, u, hu, e | e⟩ := hP y h
      · rw [e]
        exact ih1 u hu
      · rw [e, mul_assoc, (hsc u hu).symm.left_comm, ← mul_assoc, hss, one_mul]
        exact ih1 u hu
    · obtain ⟨hy, u, hu, e⟩ := hP y h
      obtain ⟨hy', u', hu', e'⟩ := hP y' h'
      have hm : d.mt y y' < d.nT := hmt y hy y' hy'
      have hg : eaG d (d.mt y y') = eaG d y * eaG d y' := eaG_mul d hn8 hT hy hy'
      have huu := ih2 u u' hu hu'
      rcases e with e | e <;> rcases e' with e' | e' <;> rw [e, e'] at hg <;> rw [e, e']
      · exact ⟨huu.1, hQ _ hm _ huu.2 (Or.inl (by rw [hg, eaG_mul d hn8 hT (hlt u hu) (hlt u' hu')]))⟩
      · refine ⟨(hsc u hu).symm.mul_right huu.1, hQ _ hm _ huu.2 (Or.inr ?_)⟩
        rw [hg, eaG_mul d hn8 hT (hlt u hu) (hlt u' hu'), (hsc u hu).symm.left_comm]
      · refine ⟨(hsc u' hu').mul_left huu.1, hQ _ hm _ huu.2 (Or.inr ?_)⟩
        rw [hg, eaG_mul d hn8 hT (hlt u hu) (hlt u' hu'), mul_assoc]
      · refine ⟨((Commute.refl _).mul_right (hsc u' hu')).mul_left
          ((hsc u hu).symm.mul_right huu.1), hQ _ hm _ huu.2 (Or.inl ?_)⟩
        rw [hg, eaG_mul d hn8 hT (hlt u hu) (hlt u' hu'), mul_assoc,
          (hsc u hu).symm.left_comm, ← mul_assoc, hss, one_mul]

theorem eaSp_zero (b : List ℕ) : eaSp d b 0 := ⟨0, Nat.two_pow_pos _, tmSpanE_zero d b⟩

theorem eaSp_gen : ∀ b : List ℕ, (∀ s ∈ b, s < d.nT) → ∀ s ∈ b, eaSp d b s
  | [], _, s, hs => absurd hs List.not_mem_nil
  | t :: c, hb, s, hs => by
    obtain ⟨hnT, -, hmt, -⟩ := tmFacts d hn8 hT
    have hb' : ∀ x ∈ c, x < d.nT := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.1 hs with rfl | hs
    · refine (eaSp_cons d).2 (Or.inr ⟨0, eaSp_zero d hn8 hT c, ?_⟩)
      have ht := hb s List.mem_cons_self
      refine eaG_inj d hn8 hT (hmt s ht 0 hnT) ht ?_
      rw [eaG_mul d hn8 hT ht hnT, eaG_zero d hn8 hT, mul_one]
    · exact (eaSp_cons d).2 (Or.inl (eaSp_gen c hb' s hs))

omit hn8 hT in
theorem eaTestBit_landL (f : ℕ → ℕ) (W u : ℕ) : ∀ b : List ℕ,
    (List.rec (motive := fun _ => ℕ) W (fun x _ ih => Nat.land (f x) ih) b).testBit u =
      (W.testBit u && b.all (fun x => (f x).testBit u))
  | [] => by simp
  | x :: b => by
    have e := Nat.testBit_and (f x)
      (List.rec (motive := fun _ => ℕ) W (fun x _ ih => Nat.land (f x) ih) b) u
    rw [eaTestBit_landL f W u b] at e
    rw [List.all_cons]
    refine e.trans ?_
    exact Bool.and_left_comm _ _ _

omit hn8 hT in
theorem eaInv_bit (s : ℕ) : bit d.invM s = true ↔ s < d.nT ∧ 0 < s ∧ d.mt s s = 0 := by
  rw [tmBit]
  unfold Dat.invM
  rw [tmTestBit_orN_nIf, tmBAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]

theorem eaM_facts (h : chkEAM d = true) {j : ℕ} (hj : j < d.nD) :
    (∀ s ∈ d.Db.getD j [], s < d.nT ∧ eaG d s * eaG d s = 1) ∧
    (∀ s ∈ d.Db.getD j [], ∀ t ∈ d.Db.getD j [], Commute (eaG d s) (eaG d t)) ∧
    (∀ y, bit (d.dm j) y = true ↔ eaSp d (d.Db.getD j []) y) ∧
    popc d.nb (d.dm j) = 2 ^ (d.Db.getD j []).length ∧
    ∀ u < d.nT, eaG d u * eaG d u = 1 → bit (d.dm j) u = false →
      (∀ s ∈ d.Db.getD j [], Commute (eaG d u) (eaG d s)) →
      ∃ j' < d.nD, ∀ y, bit (d.dm j') y = true ↔
        (bit (d.dm j) y = true ∨ ∃ y', eaSp d (d.Db.getD j []) y' ∧ d.mt u y' = y) := by
  obtain ⟨hnT, -, hmt, -⟩ := tmFacts d hn8 hT
  unfold chkEAM at h
  simp only [tmLetB, tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAllN] at h
  obtain ⟨hcen, -, hDb, -, hea⟩ := h
  have hjD : j < d.Db.length := by omega
  have h1 := tmAll2 hea j hjD
  rw [← List.getD_eq_getElem d.Db [] hjD] at h1
  generalize d.Db.getD j [] = b at h1 ⊢
  generalize d.ext.getD j [] = w at h1
  unfold eaOK Dat.basisOK at h1
  simp only [tmLetB, tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmAllL, Nat.blt_eq, tmLenL] at h1
  obtain ⟨hbas, hM, hpop, hQ, hw⟩ := h1
  have hcomm : ∀ s < d.nT, ∀ t < d.nT, (bit (d.cen s) t = true ↔ Commute (eaG d s) (eaG d t)) := by
    intro s hs t ht
    rw [tmBit, hcen s hs, tmTestBit_orN_nIf, Nat.beq_eq]
    change t < d.nT ∧ d.mt s t = d.mt t s ↔ eaG d s * eaG d t = eaG d t * eaG d s
    rw [← eaG_mul d hn8 hT hs ht, ← eaG_mul d hn8 hT ht hs]
    exact ⟨fun e => by rw [e.2], fun e => ⟨ht, eaG_inj d hn8 hT (hmt s hs t ht) (hmt t ht s hs) e⟩⟩
  have hb1 : ∀ s ∈ b, s < d.nT ∧ eaG d s * eaG d s = 1 := by
    intro s hs
    obtain ⟨hs', -, hm⟩ := (eaInv_bit d s).1 (hbas s hs).1
    exact ⟨hs', by rw [← eaG_mul d hn8 hT hs' hs', hm, eaG_zero d hn8 hT]⟩
  have hbit : ∀ y, bit (d.dm j) y = true ↔ eaSp d b y := by
    intro y
    unfold eaSp
    rw [tmBit, ← hM, tmTestBit_orN]
    simp only [tmTestBit_one]
    rw [tmOne]
    exact Iff.rfl
  refine ⟨hb1, fun s hs t ht => (hcomm s (hb1 s hs).1 t (hb1 t ht).1).1 ((hbas s hs).2 t ht), hbit,
    by rw [hpop, tmOne], fun u hu hsq hnot hc => ?_⟩
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with rfl | h
    · rw [(hbit 0).2 (eaSp_zero d hn8 hT b)] at hnot
      exact absurd hnot (by decide)
    · exact h
  have huu : d.mt u u = 0 := by
    refine eaG_inj d hn8 hT (hmt u hu u hu) hnT ?_
    rw [eaG_mul d hn8 hT hu hu, hsq, eaG_zero d hn8 hT]
  have hQu : (orL w (fun p => one p.1)).testBit u = true := by
    rw [hQ]
    change (d.invM &&& ((ones d.nT ^^^ d.dm j) &&& List.rec (motive := fun _ => ℕ) (ones d.nT)
      (fun x _ ih => Nat.land (d.cen x) ih) b)).testBit u = true
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, eaTestBit_landL, ← tmBit d.invM u,
      ← tmBit (d.dm j) u, (eaInv_bit d u).2 ⟨hu, hu0, huu⟩, hnot, tmTestBit_ones.2 hu]
    simp only [Bool.true_and, Bool.xor_false, List.all_eq_true]
    intro x hx
    rw [← tmBit]
    exact (hcomm x (hb1 x hx).1 u hu).2 (hc x hx).symm
  obtain ⟨p, hp, hpu⟩ := tmTestBit_orL.1 hQu
  rw [tmTestBit_one] at hpu
  obtain ⟨-, hp2, hdm⟩ := hw p hp
  refine ⟨p.2, hp2, fun y => ?_⟩
  rw [tmBit, hdm]
  change (d.dm j ||| _).testBit y = true ↔ _
  rw [Nat.testBit_or, Bool.or_eq_true, ← tmBit, tmTestBit_orN]
  simp only [tmTestBit_one]
  rw [tmOne, hpu]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨_, ⟨x, hx, rfl⟩, e⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, e⟩
    exact ⟨x, hx, e⟩

end EA

theorem eaSeteq_of {A B : List Tab} (h : ∀ t, t ∈ A ↔ t ∈ B) : seteqT A B = true := by
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

theorem eaMemD_of {D : List (List Tab)} {B X : List Tab} (hB : B ∈ D) (h1 : B.Nodup)
    (h2 : X.Nodup) (h : ∀ t, t ∈ B ↔ t ∈ X) : memD D X = true := by
  simp only [memD, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨B, hB, ((List.perm_ext_iff_of_nodup h1 h2).2 h).length_eq, eaSeteq_of h⟩

theorem eaChkEA_of {n : ℕ} {T : List Tab} {D : List (List Tab)} (h1 : memD D [idT n] = true)
    (h2 : ∀ A ∈ D, subOK n A = true ∧ (∀ a ∈ A, a ∈ T) ∧ (∀ a ∈ A, ∀ b ∈ A, mulT a b = mulT b a) ∧
      ∀ a ∈ A, mulT a a = idT n)
    (h3 : ∀ A ∈ D, ∀ s ∈ T, mulT s s = idT n → s ∉ A → (∀ a ∈ A, mulT a s = mulT s a) →
      memD D (extT A s) = true) : chkEA n T D = true := by
  simp only [chkEA, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq]
  refine ⟨⟨h1, fun A hA => ?_⟩, fun A hA s hs => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h2 A hA
    exact ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩
  · rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    by_cases hss : mulT s s = idT n
    · by_cases hsA : s ∈ A
      · exact Or.inl (Or.inl (Or.inr (List.contains_iff_mem.2 hsA)))
      · by_cases hc : ∀ a ∈ A, mulT a s = mulT s a
        · exact Or.inr (h3 A hA s hs hss hsA hc)
        · exact Or.inl (Or.inr (by simpa using hc))
    · exact Or.inl (Or.inl (Or.inl (by simpa using hss)))

theorem chkEAM_sound (d : Dat) (hn8 : d.n ≤ 8) (hbp : chkBP = true) (hT : chkTM d = true)
    (h : chkEAM d = true) (hN : chkNamedM d = true) :
    chkEA d.n d.TL d.DD = true ∧ ∀ j < d.nD, (∀ g ∈ d.bas j, g ∈ d.DL j) ∧
      (d.DL j).length = 2 ^ (d.bas j).length ∧
      ∃ S : List Tab, chainOK (d.bas j) (idT d.n) [] S = true ∧ ∀ t, t ∈ S ↔ t ∈ d.DL j := by
  obtain ⟨hnT, hperm, hmt, hmul, hid, hinj⟩ := tmFacts d hn8 hT
  have hD : 0 < d.nD := by
    unfold chkNamedM at hN
    simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmLetB, tmAllL, Nat.blt_eq, tmAdd,
      tmMul] at hN
    obtain ⟨-, -, -, -, hnmwLen, hnmwD, -⟩ := hN
    obtain ⟨x, hx⟩ : ∃ x, x ∈ d.nmw := by
      rcases hl : d.nmw with _ | ⟨x, _⟩
      · rw [hl] at hnmwLen
        simp at hnmwLen
      · exact ⟨x, List.mem_cons_self⟩
    exact lt_of_le_of_lt (Nat.zero_le _) (hnmwD x hx)
  have hD0 : d.dm 0 = 1 := by
    have h' := h
    unfold chkEAM at h'
    simp only [tmLetB, tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAllN] at h'
    exact h'.2.1
  have hF := fun j (hj : j < d.nD) => eaM_facts d hn8 hT h hj
  have hbas : ∀ j, d.bas j = (d.Db.getD j []).map d.tl := fun j => by rw [Dat.bas, tmLget]
  have hblt : ∀ j < d.nD, ∀ s ∈ d.Db.getD j [], s < d.nT := fun j hj s hs => ((hF j hj).1 s hs).1
  have hSp : ∀ j < d.nD, (∀ y, eaSp d (d.Db.getD j []) y → eaG d y * eaG d y = 1) ∧
      ∀ y y', eaSp d (d.Db.getD j []) y → eaSp d (d.Db.getD j []) y' →
        Commute (eaG d y) (eaG d y') ∧ eaSp d (d.Db.getD j []) (d.mt y y') := fun j hj =>
    eaSp_facts d hn8 hT _ (hblt j hj) (fun s hs => ((hF j hj).1 s hs).2) (hF j hj).2.1
  have hSplt : ∀ j < d.nD, ∀ y, eaSp d (d.Db.getD j []) y → y < d.nT :=
    fun j hj y hy => eaSp_lt d hn8 hT (hblt j hj) hy
  have hDL : ∀ j < d.nD, ∀ t, t ∈ d.DL j ↔ ∃ y, eaSp d (d.Db.getD j []) y ∧ d.tl y = t := by
    intro j hj t
    change t ∈ d.mL (d.dm j) ↔ _
    rw [mem_mL]
    constructor
    · rintro ⟨y, -, hy, rfl⟩
      exact ⟨y, ((hF j hj).2.2.1 y).1 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hSplt j hj y hy, ((hF j hj).2.2.1 y).2 hy, rfl⟩
  have hnd : ∀ M, (d.mL M).Nodup := by
    intro M
    unfold Dat.mL
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.nodup_range.filter _)
    rw [List.mem_filter, List.mem_range] at hx hy
    exact hinj x hx.1 y hy.1 hxy
  have htl : ∀ y < d.nT, d.tl y = tab (eaG d y) := fun y hy => (eaG_tab d hn8 hT hy).symm
  have hTL : ∀ t, t ∈ d.TL ↔ ∃ y < d.nT, d.tl y = t := by
    intro t
    simp [Dat.TL]
  have hDD : ∀ A, A ∈ d.DD ↔ ∃ j < d.nD, d.DL j = A := by
    intro A
    simp [Dat.DD]
  have hsub : ∀ j < d.nD, subOK d.n (d.DL j) = true ∧ (∀ a ∈ d.DL j, a ∈ d.TL) ∧
      (∀ a ∈ d.DL j, ∀ b ∈ d.DL j, mulT a b = mulT b a) ∧ ∀ a ∈ d.DL j, mulT a a = idT d.n := by
    intro j hj
    obtain ⟨hsq, hcm⟩ := hSp j hj
    simp only [subOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨fun t ht => ?_, ?_⟩, fun a ha b hb => ?_⟩, fun a ha => ?_⟩, hnd _⟩, fun a ha => ?_,
      fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj t).1 ht
      exact (tmIsTab (hperm y (hSplt j hj y hy))).1
    · exact (hDL j hj _).2 ⟨0, eaSp_zero d hn8 hT _, hid⟩
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
      obtain ⟨y', hy', rfl⟩ := (hDL j hj b).1 hb
      rw [hmul y (hSplt j hj y hy) y' (hSplt j hj y' hy')]
      exact (hDL j hj _).2 ⟨_, (hcm y y' hy hy').2, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
      have hyl := hSplt j hj y hy
      rw [htl y hyl, ← tab_inv, inv_eq_of_mul_eq_one_right (hsq y hy), ← htl y hyl]
      exact (hDL j hj _).2 ⟨y, hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
      exact (hTL _).2 ⟨y, hSplt j hj y hy, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
      obtain ⟨y', hy', rfl⟩ := (hDL j hj b).1 hb
      rw [htl y (hSplt j hj y hy), htl y' (hSplt j hj y' hy'), ← tab_mul, ← tab_mul,
        (hcm y y' hy hy').1.eq]
    · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
      rw [htl y (hSplt j hj y hy), ← tab_mul, hsq y hy, tab_one]
  refine ⟨eaChkEA_of ?_ (fun A hA => ?_) (fun A hA s hs hss hsA hc => ?_), fun j hj => ?_⟩
  ·
    refine eaMemD_of (B := d.DL 0) ((hDD _).2 ⟨0, hD, rfl⟩) (hnd _) (List.nodup_singleton _)
      fun t => ?_
    change t ∈ d.mL (d.dm 0) ↔ _
    rw [mem_mL, hD0, List.mem_singleton]
    constructor
    · rintro ⟨y, -, hy, rfl⟩
      rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero] at hy
      rw [hy, hid]
    · rintro rfl
      exact ⟨0, hnT, by rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero], hid⟩
  · obtain ⟨j, hj, rfl⟩ := (hDD A).1 hA
    exact hsub j hj
  ·
    obtain ⟨j, hj, rfl⟩ := (hDD A).1 hA
    obtain ⟨u, hu, rfl⟩ := (hTL s).1 hs
    have hsq : eaG d u * eaG d u = 1 := by
      apply tab_injective
      rw [tab_mul, ← htl u hu, hss, tab_one]
    have hnot : bit (d.dm j) u = false := by
      rw [Bool.eq_false_iff]
      intro hb
      exact hsA ((mem_mL d _ _).2 ⟨u, hu, hb, rfl⟩)
    have hcu : ∀ s ∈ d.Db.getD j [], Commute (eaG d u) (eaG d s) := by
      intro x hx
      have hxl := hblt j hj x hx
      have e := hc (d.tl x) ((hDL j hj _).2 ⟨x, eaSp_gen d hn8 hT _ (hblt j hj) x hx, rfl⟩)
      rw [htl x hxl, htl u hu, ← tab_mul, ← tab_mul] at e
      exact (tab_injective e).symm
    obtain ⟨j', hj', hbit'⟩ := (hF j hj).2.2.2.2 u hu hsq hnot hcu
    have hset : ∀ t, t ∈ d.DL j' ↔ t ∈ extT (d.DL j) (d.tl u) := by
      intro t
      change t ∈ d.mL (d.dm j') ↔ _
      rw [mem_mL, extT, List.mem_append, List.mem_map]
      simp only [hbit']
      constructor
      · rintro ⟨y, hy, hb | ⟨y', hy', rfl⟩, rfl⟩
        · exact Or.inl ((mem_mL d _ _).2 ⟨y, hy, hb, rfl⟩)
        · refine Or.inr ⟨d.tl y', (hDL j hj _).2 ⟨y', hy', rfl⟩, ?_⟩
          rw [hc _ ((hDL j hj _).2 ⟨y', hy', rfl⟩), hmul u hu y' (hSplt j hj y' hy')]
      · rintro (ht | ⟨a, ha, rfl⟩)
        · obtain ⟨y, hy, hb, rfl⟩ := (mem_mL d _ _).1 ht
          exact ⟨y, hy, Or.inl hb, rfl⟩
        · obtain ⟨y', hy', rfl⟩ := (hDL j hj a).1 ha
          have hy'l := hSplt j hj y' hy'
          refine ⟨d.mt u y', hmt u hu y' hy'l, Or.inr ⟨y', hy', rfl⟩, ?_⟩
          rw [hc _ ha, hmul u hu y' hy'l]
    have hndE : (extT (d.DL j) (d.tl u)).Nodup := by
      rw [extT, List.nodup_append]
      refine ⟨hnd _, List.Nodup.map_on (fun a ha b hb hab => ?_) (hnd _), fun a ha b hb hab => ?_⟩
      · obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
        obtain ⟨y', hy', rfl⟩ := (hDL j hj b).1 hb
        rw [htl y (hSplt j hj y hy), htl y' (hSplt j hj y' hy'), htl u hu, ← tab_mul,
          ← tab_mul] at hab
        rw [htl y (hSplt j hj y hy), htl y' (hSplt j hj y' hy'),
          mul_right_cancel (tab_injective hab)]
      · obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
        obtain ⟨y, hy, rfl⟩ := (hDL j hj a).1 ha
        obtain ⟨y', hy', rfl⟩ := (hDL j hj b').1 hb'
        have hyl := hSplt j hj y hy
        have hy'l := hSplt j hj y' hy'
        apply hsA
        have e : eaG d u = eaG d y' * eaG d y := by
          rw [htl y hyl, htl y' hy'l, htl u hu, ← tab_mul] at hab
          rw [tab_injective hab, ← mul_assoc, (hSp j hj).1 y' hy', one_mul]
        rw [htl u hu, e, tab_mul, ← htl y' hy'l, ← htl y hyl, hmul y' hy'l y hyl]
        exact (hDL j hj _).2 ⟨_, ((hSp j hj).2 y' y hy' hy).2, rfl⟩
    exact eaMemD_of ((hDD _).2 ⟨j', hj', rfl⟩) (hnd _) hndE hset
  · rw [hbas j]
    refine ⟨fun g hg => ?_, ?_, spanL d (d.Db.getD j []), ?_, fun t => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact (hDL j hj _).2 ⟨s, eaSp_gen d hn8 hT _ (hblt j hj) s hs, rfl⟩
    · rw [List.length_map, ← (hF j hj).2.2.2.1, tmPopc hbp]
      change (((List.range d.nT).filter (fun y => bit (d.dm j) y)).map d.tl).length = _
      rw [List.length_map, length_filter_range]
      have hM : d.dm j < 2 ^ d.nT := tmEnt_lt _ _ _
      have hnb : d.nT ≤ 8 * d.nb := by
        change d.nT ≤ 8 * ((d.nT + 7) / 8)
        omega
      rw [← Finset.sum_range_add_sum_Ico _ hnb, Finset.sum_eq_zero (s := Finset.Ico d.nT (8 * d.nb)),
        add_zero]
      · refine Finset.sum_congr rfl fun y _ => ?_
        rw [tmBit]
      · intro i hi
        rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM
          (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Ico.1 hi).1))]
        rfl
    · exact tmSpanL_chain d hnT hmt hmul hid _ (hblt j hj)
    · exact tmSpanL_iff d (fun x => tmSpanE_lt d hnT hmt _ (hblt j hj) x)
        (fun y => (hF j hj).2.2.1 y) t

theorem chkNamedM_sound (d : Dat) (hn : 5 ≤ d.n) (hn8 : d.n ≤ 8) (hbp : chkBP = true)
    (hT : chkTM d = true) (hEA : chkEAM d = true) (h : chkNamedM d = true)
    (hAmT : ∀ b ∈ d.Am, ∀ x ∈ b, x < d.nT) (hA0T : ∀ x ∈ d.A0, x < d.nT) :
    (∀ i < d.n / 2, d.ix i < d.nD ∧ ∃ S : List Tab,
      chainOK ((gensAm d.n (i + 1)).map tab) (idT d.n) [] S = true ∧
      (∀ g ∈ (gensAm d.n (i + 1)).map tab, g ∈ S) ∧ ∀ t, t ∈ S ↔ t ∈ d.DL (d.ix i)) ∧
    (d.ix (d.n / 2) < d.nD ∧ ∃ S : List Tab,
      chainOK ((gensA0 d.n).map tab) (idT d.n) [] S = true ∧
      (∀ g ∈ (gensA0 d.n).map tab, g ∈ S) ∧ ∀ t, t ∈ S ↔ t ∈ d.DL (d.ix (d.n / 2))) ∧
    (d.ix (d.n / 2 + 1) < d.nD ∧ ∀ t, t ∈ d.DL (d.ix (d.n / 2 + 1)) ↔
      t ∈ d.DL (d.ix (d.n / 2 - 1)) ∧ isEvenT t = true) ∧
    suppCardT (CFSG.Quasithin.B3.t12 d.n) = 4 ∧
    ∀ t ∈ d.TL, mulT t t = idT d.n → suppCardT t = 4 →
      ∃ g : Tab, isTab d.n g = true ∧ cjT g (CFSG.Quasithin.B3.t12 d.n) = t := by
  obtain ⟨hnT, hpermT, hmt, hmul, hid, hinj⟩ := tmFacts d hn8 hT
  have hh : d.h = d.n / 2 := rfl
  unfold chkNamedM at h
  simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmLetB, tmAllL, Nat.blt_eq, tmAdd,
    tmMul] at h
  obtain ⟨hAmLen, hAmTab, hA0Len, hA0Tab, hnmwLen, hnmwD, hAmSpan, hA0Span, -, hEven, hSupp,
    hDT, hdtw⟩ := h
  have hix : ∀ i < d.n / 2 + 2, d.ix i < d.nD := by
    intro i hi
    unfold Dat.ix
    rw [tmLget, List.getD_eq_getElem _ _ (by rw [hnmwLen]; exact hi)]
    exact hnmwD _ (List.getElem_mem _)
  have hlt := tmSpanE_lt d hnT hmt
  have hspan : ∀ (b : List ℕ) (i : ℕ), (∀ s ∈ b, s < d.nT) → d.spanM b = d.nm i →
      ∀ t, t ∈ spanL d b ↔ t ∈ d.DL (d.ix i) := by
    intro b i hb he t
    refine tmSpanL_iff d (hlt b hb) (fun y => ?_) t
    change bit (d.nm i) y = true ↔ _
    rw [← he, tmBit_spanM]
  have hpsw : ∀ i, 2 * i + 1 < d.n → decT d.n (pswap d.n (2 * i) (2 * i + 1)) = tab (ti d.n i) :=
    fun i hi => decT_pswap hn8 (by omega) hi
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hiA : i < d.Am.length := by rw [hAmLen]; exact hi
    have h1 := tmAllI hAmTab i hiA
    have h2 := tmAllI hAmSpan i hiA
    simp only [Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAdd, tmMul] at h1 h2
    obtain ⟨hlen, hent⟩ := h1
    have hbT : ∀ s ∈ d.Am[i], s < d.nT := hAmT _ (List.getElem_mem _)
    have hmap : d.Am[i].map d.tl = (gensAm d.n (i + 1)).map tab := by
      apply List.ext_getElem
      · simp [gensAm, hlen]
      · intro i' h3 h4
        have hi' : i' < d.Am[i].length := by simpa using h3
        have e := tmAllI hent i' hi'
        rw [Nat.beq_eq] at e
        simp only [List.getElem_map, gensAm, List.getElem_range]
        change decT d.n (d.tab d.Am[i][i']) = _
        rw [e]
        exact hpsw i' (by omega)
    refine ⟨hix i (by omega), spanL d d.Am[i], ?_, fun g hg => ?_, hspan _ i hbT h2.1⟩
    · rw [← hmap]
      exact tmSpanL_chain d hnT hmt hmul hid _ hbT
    · rw [← hmap] at hg
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact tmSpanL_gen d hnT hmt hmul hid _ hbT s hs
  ·
    have h2 : 1 < d.A0.length := by omega
    have hent : ∀ i (hi : i < d.A0.length), d.tl d.A0[i] = tab
        (if i = 0 then swapN d.n 0 1 * swapN d.n 2 3 else
          if i = 1 then swapN d.n 0 2 * swapN d.n 1 3 else ti d.n i) := by
      intro i hi
      have e := tmAllI hA0Tab i hi
      rw [Nat.beq_eq] at e
      change decT d.n (d.tab d.A0[i]) = _
      rw [e]
      unfold a0gen
      simp only [tmNIf, Nat.beq_eq, tmMul]
      have hpw : ∀ a b, a < d.n → b < d.n → ∀ p < d.n, pt (pswap d.n a b) p < d.n :=
        fun a b ha hb p hp => pt_lt_of_decT (decT_pswap hn8 ha hb) hp
      split_ifs with h0 h1
      · rw [decT_pmul (hpw 2 3 (by omega) (by omega)),
          decT_pswap hn8 (a := 0) (b := 1) (by omega) (by omega),
          decT_pswap hn8 (a := 2) (b := 3) (by omega) (by omega), tab_mul]
      · rw [decT_pmul (hpw 1 3 (by omega) (by omega)),
          decT_pswap hn8 (a := 0) (b := 2) (by omega) (by omega),
          decT_pswap hn8 (a := 1) (b := 3) (by omega) (by omega), tab_mul]
      · exact hpsw i (by omega)
    have hG : ∀ s ∈ d.A0, d.tl s ∈ (gensA0 d.n).map tab := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
      rw [hent i hi]
      refine List.mem_map.2 ⟨_, ?_, rfl⟩
      simp only [gensA0, List.mem_append, List.mem_cons, List.mem_map, List.mem_filter,
        List.mem_range, decide_eq_true_eq]
      split_ifs with h0 h1
      · simp
      · simp
      · exact Or.inr ⟨i, ⟨by omega, by omega⟩, rfl⟩
    refine ⟨hix _ (by omega), spanL d d.A0,
      chainOK_mono (fun g hg => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
        exact hG s hs) _ _ (tmSpanL_chain d hnT hmt hmul hid _ hA0T), fun g hg => ?_,
      hspan _ _ hA0T hA0Span⟩
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hg
    have hgen := tmSpanL_gen d hnT hmt hmul hid _ hA0T
    simp only [gensA0, List.mem_append, List.mem_cons, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq, List.not_mem_nil, or_false] at hσ
    rcases hσ with (rfl | rfl) | ⟨i, ⟨hi, h2i⟩, rfl⟩
    · have e := hent 0 (by omega)
      rw [if_pos rfl] at e
      rw [← e]
      exact hgen _ (List.getElem_mem _)
    · have e := hent 1 (by omega)
      rw [if_neg (by omega), if_pos rfl] at e
      rw [← e]
      exact hgen _ (List.getElem_mem _)
    · have e := hent i (by omega)
      rw [if_neg (by omega), if_neg (by omega)] at e
      rw [← e]
      exact hgen _ (List.getElem_mem _)
  ·
    refine ⟨hix _ (by omega), fun t => ?_⟩
    have hb : ∀ y, bit (d.evenPart d.dcM) y = true ↔
        y < d.nT ∧ bit d.dcM y = true ∧ isEvenT (d.tl y) = true := by
      intro y
      rw [tmBit]
      unfold Dat.evenPart
      rw [tmTestBit_orN_nIf, tmBAnd, Bool.and_eq_true, evenP_eq]
      rfl
    change t ∈ d.mL (d.nm (d.h + 1)) ↔ t ∈ d.mL d.dcM ∧ isEvenT t = true
    rw [← hEven, mem_mL, mem_mL]
    simp only [hb]
    constructor
    · rintro ⟨y, -, ⟨hy, hM, hev⟩, rfl⟩
      exact ⟨⟨y, hy, hM, rfl⟩, hev⟩
    · rintro ⟨⟨y, hy, hM, rfl⟩, hev⟩
      exact ⟨y, hy, ⟨hy, hM, hev⟩, rfl⟩
  ·
    have e : decT d.n (CFSG.KC.B3M.t12 d.n) = CFSG.Quasithin.B3.t12 d.n := by
      unfold CFSG.KC.B3M.t12 CFSG.Quasithin.B3.t12
      rw [decT_pmul (fun p hp => pt_lt_of_decT (decT_pswap hn8 (a := 2) (b := 3) (by omega)
        (by omega)) hp), decT_pswap hn8 (a := 0) (b := 1) (by omega) (by omega),
        decT_pswap hn8 (a := 2) (b := 3) (by omega) (by omega), ← tab_mul]
      rfl
    rw [← e, ← supp_eq]
    exact hSupp
  ·
    intro t ht hsq hs4
    obtain ⟨x, hx, rfl⟩ : ∃ x < d.nT, d.tl x = t := by simpa [Dat.TL] using ht
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [hid, suppCardT_idT] at hs4
      exact absurd hs4 (by norm_num)
    have hinv : bit d.invM x = true := by
      rw [tmBit]
      unfold Dat.invM
      rw [tmTestBit_orN_nIf, tmBAnd, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
      refine ⟨hx, Nat.pos_of_ne_zero hx0, hinj _ (hmt x hx x hx) 0 hnT ?_⟩
      rw [← hmul x hx x hx, hsq, hid]
    have hdtM : bit d.dtM x = true := by
      rw [tmBit]
      unfold Dat.dtM
      rw [tmStrictN, tmTestBit_orN_nIf, tmBAnd, Bool.and_eq_true, Nat.beq_eq, supp_eq]
      exact ⟨hx, hinv, hs4⟩
    rw [tmBit, ← hDT, tmTestBit_orL] at hdtM
    obtain ⟨p, hp, hpx⟩ := hdtM
    rw [tmTestBit_one] at hpx
    obtain ⟨hperm, -, hpm⟩ := hdtw p hp
    obtain ⟨hgT, -, hglt⟩ := tmIsTab hperm
    have h12 : decT d.n (CFSG.KC.B3M.t12 d.n) = tab (ti d.n 0 * ti d.n 1) := by
      unfold CFSG.KC.B3M.t12
      rw [decT_pmul (fun p hp => pt_lt_of_decT (decT_pswap hn8 (a := 2) (b := 3) (by omega)
        (by omega)) hp), decT_pswap hn8 (a := 0) (b := 1) (by omega) (by omega),
        decT_pswap hn8 (a := 2) (b := 3) (by omega) (by omega), ← tab_mul]
      rfl
    have e1 : mulT (decT d.n p.2) (decT d.n (CFSG.KC.B3M.t12 d.n)) =
        mulT (d.tl x) (decT d.n p.2) := by
      rw [← decT_pmul (fun q hq => pt_lt_of_decT h12 hq), hpm, decT_pmul hglt, hpx]
      rfl
    obtain ⟨γ, hγ⟩ := exists_tab_eq hgT
    obtain ⟨τ, hτ⟩ := exists_tab_eq (tmIsTab (hpermT x hx)).1
    change tab γ = decT d.n p.2 at hγ
    change tab τ = d.tl x at hτ
    have e2 : γ * (ti d.n 0 * ti d.n 1) = τ * γ := by
      apply tab_injective
      rw [tab_mul γ, tab_mul τ γ, hγ, hτ, ← h12]
      exact e1
    refine ⟨decT d.n p.2, hgT, ?_⟩
    have ht12 : CFSG.Quasithin.B3.t12 d.n = tab (ti d.n 0 * ti d.n 1) := rfl
    rw [ht12, ← hγ, cjT_tab, e2, mul_inv_cancel_right, hτ]

theorem chkModM_fv (d : Dat) (k : Mod) (hn : 5 ≤ d.n) (hn8 : d.n ≤ 8) (hbp : chkBP = true)
    (hT : chkTM d = true) (hEA : chkEAM d = true) (h : chkModM d (mIdx k) = true) :
    ∀ j < d.nD, lget (lget d.FV (mIdx k) []) j 0 =
      2 ^ (d.bas j).length * cntF d.n k (d.bas j) := by
  intro j hj
  have hperm : ∀ i < d.nT, isPerm d.n (d.tab i) = true := by
    unfold chkTM at hT
    simp only [tmBAnd, Bool.and_eq_true, tmAllN, tmLetB] at hT
    exact fun i hi => (hT.2.2.2.2 i hi).1
  unfold chkEAM at hEA
  simp only [tmBAnd, Bool.and_eq_true, tmLetB, Nat.beq_eq, tmLenL] at hEA
  obtain ⟨-, -, hDb, -, hea⟩ := hEA
  unfold chkModM at h
  simp only [tmBAnd, Bool.and_eq_true, tmLetB] at h
  obtain ⟨hrows, -, hfv, -⟩ := h
  have hjD : j < d.Db.length := by omega
  have hb : ∀ s ∈ d.Db[j], bit d.invM s = true := by
    have h1 := tmAll2 hea j hjD
    unfold eaOK Dat.basisOK at h1
    simp only [tmLetB, tmBAnd, Bool.and_eq_true, tmAllL] at h1
    exact fun s hs => (h1.1 s hs).1
  have h1 := tmAll2 hfv j hjD
  simp only [Bool.and_eq_true, Nat.beq_eq] at h1
  rw [tmLget, h1.2, tmOne, tmLenL, tmMul]
  have hbas : d.bas j = d.Db[j].map d.tl := by
    rw [Dat.bas, tmLget, List.getD_eq_getElem _ _ hjD]
  rw [hbas, List.length_map]
  congr 1
  unfold Dat.rowsOK at hrows
  simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmAllN, tmBImp, tmLetB, Bool.or_eq_true,
    Bool.not_eq_true'] at hrows
  obtain ⟨hW, hF⟩ := hrows
  have h8 : 8 * d.vb = 2 ^ d.n := by
    have e : d.vb = 2 ^ d.n / 2 ^ 3 := by
      change one d.n >>> 3 = _
      rw [tmOne, Nat.shiftRight_eq_div_pow]
    rw [e]
    exact Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 (by omega : 3 ≤ d.n))
  unfold Dat.cntM cntF
  rw [tmPopc hbp, h8, length_filter_range]
  refine Finset.sum_congr rfl fun w hw => if_congr ?_ rfl rfl
  rw [Finset.mem_range] at hw
  rw [tmTestBit_cntM, Bool.and_eq_true, hW, tmTestBit_orN_nIf, tmOne, inW_eq hbp hn8 hw]
  simp only [hw, true_and, Bool.and_eq_true, List.all_eq_true, List.forall_mem_map]
  refine and_congr_right fun _ => forall₂_congr fun g hg' => ?_
  have hgT := tmInv_lt d (hb g hg')
  have hF' := (hF g hgT).resolve_left (by rw [hb g hg']; simp)
  rw [hF', tmTestBit_orN_nIf, tmOne, ← actV_eq d (hperm g hgT),
    ← inN_eq (actV_xor_lt (hperm g hgT) hw)]
  simp only [hw, true_and]
  exact Iff.rfl

theorem mmBOr (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

theorem mmBIfF (c e : Bool) : Bool.rec (motive := fun _ => Bool) e false c = (!c && e) := by
  cases c <;> rfl

theorem mmAnyN {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero =>
    exact ⟨fun h => absurd (h : false = true) Bool.false_ne_true,
      fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    have e : anyN (m + 1) f = (f m || anyN m f) := by
      change Bool.rec (motive := fun _ => Bool) (anyN m f) true (f m) = _
      exact mmBOr _ _
    rw [e, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem mmPackL (w : ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, x < 2 ^ w) → ∀ i, ent (packL w L) w i = L.getD i 0
  | [], _, i => by
    change ent 0 w i = 0
    rw [tmEnt_small (Nat.two_pow_pos w)]
    simp
  | x :: L, hL, i => by
    have hx : x < 2 ^ w := hL x List.mem_cons_self
    have e : packL w (x :: L) = Nat.lor x (Nat.shiftLeft (packL w L) (Nat.mul w 1)) := by
      change Nat.lor x (Nat.shiftLeft (packL w L) w) = _
      rw [tmMul, Nat.mul_one]
    rw [e, tmEnt_lor_shift (by rwa [Nat.mul_one])]
    cases i with
    | zero =>
      rw [if_pos Nat.one_pos, tmEnt_small hx, if_pos rfl]
      simp
    | succ i =>
      rw [if_neg (by omega), Nat.add_sub_cancel,
        mmPackL w L (fun y hy => hL y (List.mem_cons_of_mem _ hy)) i]
      simp

theorem mmRK : ∀ L : List (List ℕ),
    List.rec (motive := fun _ => ℕ) 0 (fun b _ ih => Nat.lor (lenL b) (Nat.shiftLeft ih 4)) L =
      packL 4 (L.map lenL)
  | [] => rfl
  | b :: L => by
    change Nat.lor (lenL b) (Nat.shiftLeft (List.rec (motive := fun _ => ℕ) 0
      (fun b _ ih => Nat.lor (lenL b) (Nat.shiftLeft ih 4)) L) 4) = Nat.lor (lenL b)
        (Nat.shiftLeft (packL 4 (L.map lenL)) 4)
    rw [mmRK L]

theorem mmSubM_iff {A B : ℕ} : subM A B = true ↔ ∀ y, bit A y = true → bit B y = true := by
  unfold subM
  rw [Nat.beq_eq]
  simp only [tmBit]
  constructor
  · intro h y hy
    rw [← h] at hy
    change (A &&& B).testBit y = true at hy
    rw [Nat.testBit_and, Bool.and_eq_true] at hy
    exact hy.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro y
    change (A &&& B).testBit y = _
    rw [Nat.testBit_and]
    cases hA : A.testBit y
    · rfl
    · rw [h y hA]
      rfl

theorem mmCntF_pos (n : ℕ) (k : Mod) (L : List Tab) : 0 < cntF n k L := by
  unfold cntF
  refine List.length_pos_of_mem (a := 0) ?_
  rw [List.mem_filter, List.mem_range]
  refine ⟨Nat.two_pow_pos n, ?_⟩
  have h0 : ∀ t, actM n t 0 = 0 := by
    intro t
    apply Nat.eq_of_testBit_eq
    intro j
    unfold actM
    rw [testBit_foldl_aux]
    simp
  have hw : inWk n k 0 = true := by
    cases k <;> simp [inWk, popPar]
  have hN : inNk n k 0 = true := by
    cases k <;> simp [inNk]
  simp only [h0, Nat.xor_self, hN, hw, Bool.true_and, List.all_eq_true]
  exact fun _ _ => trivial

theorem mmCntF_congr (n : ℕ) (k : Mod) {A B : List Tab} (h : ∀ t, t ∈ A ↔ t ∈ B) :
    cntF n k A = cntF n k B := by
  unfold cntF
  congr 1
  refine List.filter_congr fun m _ => ?_
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h1 t ht => h1 t ((h t).2 ht), fun h1 t ht => h1 t ((h t).1 ht)⟩

section MM

variable (d : Dat) (hn8 : d.n ≤ 8) (hT : chkTM d = true)

omit hn8 hT in
theorem mmBit_lt {M y : ℕ} (hM : M < 2 ^ d.nT) (h : bit M y = true) : y < d.nT := by
  rw [tmBit] at h
  by_contra hy
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM
    (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  exact absurd h (by decide)

include hn8 hT

theorem mmSubBits {A B : ℕ} (hA : A < 2 ^ d.nT) :
    (∀ y, bit A y = true → bit B y = true) ↔ ∀ t ∈ d.mL A, t ∈ d.mL B := by
  obtain ⟨-, -, -, -, -, hinj⟩ := tmFacts d hn8 hT
  constructor
  · intro h t ht
    obtain ⟨y, hy, hb, rfl⟩ := (mem_mL d _ _).1 ht
    exact (mem_mL d _ _).2 ⟨y, hy, h y hb, rfl⟩
  · intro h y hb
    have hy := mmBit_lt d hA hb
    obtain ⟨y', hy', hb', e⟩ := (mem_mL d _ _).1 (h _ ((mem_mL d _ _).2 ⟨y, hy, hb, rfl⟩))
    rw [← hinj y' hy' y hy e]
    exact hb'

theorem mmSub {A B : ℕ} (hA : A < 2 ^ d.nT) : subM A B = true ↔ ∀ t ∈ d.mL A, t ∈ d.mL B := by
  rw [mmSubM_iff]
  exact mmSubBits d hn8 hT hA

theorem mmEq {A B : ℕ} (hA : A < 2 ^ d.nT) (hB : B < 2 ^ d.nT) :
    A = B ↔ ∀ t, t ∈ d.mL A ↔ t ∈ d.mL B := by
  constructor
  · rintro rfl t
    exact Iff.rfl
  · intro h
    have h1 := (mmSubBits d hn8 hT hA).2 (fun t ht => (h t).1 ht)
    have h2 := (mmSubBits d hn8 hT hB).2 (fun t ht => (h t).2 ht)
    apply Nat.eq_of_testBit_eq
    intro y
    rw [Bool.eq_iff_iff]
    simp only [← tmBit]
    exact ⟨h1 y, h2 y⟩

omit hn8 hT in
theorem mmLen (hbp : chkBP = true) {M : ℕ} (hM : M < 2 ^ d.nT) :
    (d.mL M).length = popc d.nb M := by
  rw [tmPopc hbp]
  change (((List.range d.nT).filter (fun y => bit M y)).map d.tl).length = _
  rw [List.length_map, length_filter_range]
  have hnb : d.nT ≤ 8 * d.nb := by
    change d.nT ≤ 8 * ((d.nT + 7) / 8)
    omega
  rw [← Finset.sum_range_add_sum_Ico _ hnb, Finset.sum_eq_zero (s := Finset.Ico d.nT (8 * d.nb)),
    add_zero]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [tmBit]
  · intro i hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM
      (Nat.pow_le_pow_right (by norm_num) (Finset.mem_Ico.1 hi).1))]
    rfl

theorem mmML1 (t : Tab) : t ∈ d.mL 1 ↔ t = d.tl 0 := by
  obtain ⟨hnT, -⟩ := tmFacts d hn8 hT
  rw [mem_mL]
  constructor
  · rintro ⟨y, -, hy, rfl⟩
    rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero] at hy
    rw [hy]
  · rintro rfl
    exact ⟨0, hnT, by rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero], rfl⟩

theorem mmNd (M : ℕ) : (d.mL M).Nodup := by
  obtain ⟨-, -, -, -, -, hinj⟩ := tmFacts d hn8 hT
  unfold Dat.mL
  refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.nodup_range.filter _)
  rw [List.mem_filter, List.mem_range] at hx hy
  exact hinj x hx.1 y hy.1 hxy

theorem mmOne {M : ℕ} (hM : M < 2 ^ d.nT) (h0 : d.tl 0 ∈ d.mL M) :
    M = 1 ↔ (d.mL M).length = 1 := by
  obtain ⟨hnT, -⟩ := tmFacts d hn8 hT
  have h1 : (1 : ℕ) < 2 ^ d.nT := Nat.one_lt_two_pow (by omega)
  rw [mmEq d hn8 hT hM h1]
  simp only [mmML1 d hn8 hT]
  constructor
  · intro h
    have hp := (List.perm_ext_iff_of_nodup (mmNd d hn8 hT M) (List.nodup_singleton (d.tl 0))).2
      (fun t => by rw [h t, List.mem_singleton])
    rw [hp.length_eq]
    rfl
  · intro h t
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h
    rw [ha, List.mem_singleton] at h0 ⊢
    rw [h0]

theorem mmOff (k : Mod) (h0 : ∀ j < d.nD, d.tl 0 ∈ d.DL j) {FVP : ℕ}
    (hFV : ∀ j < d.nD, ent FVP 16 j = Fval d.n k (d.DL j)) (j : ℕ) :
    bit (d.offM FVP) j = true ↔ j < d.nD ∧ offOK d.n k d.DD (d.DL j) = true := by
  rw [tmBit]
  unfold Dat.offM
  rw [tmTestBit_orN_nIf]
  simp only [tmLetB, tmBAnd, mmBIfF, tmBImp, tmBeq, Bool.and_eq_true, Bool.and_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, tmAllN, Bool.or_eq_true, Nat.ble_eq, offOK,
    List.all_eq_true, decide_eq_true_eq, ne_eq]
  have hsub : ∀ i, subM (d.dm i) (d.dm j) = true ↔
      ((d.DL i).all fun t => (d.DL j).contains t) = true := by
    intro i
    rw [mmSub d hn8 hT (A := d.dm i) (tmEnt_lt _ _ _), List.all_eq_true]
    simp only [List.contains_iff_mem]
    rfl
  refine and_congr_right fun hj =>
    and_congr (not_congr (mmOne d hn8 hT (tmEnt_lt _ _ _) (h0 j hj)))
      ⟨fun h x hx => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hi
    rcases h i hi with h1 | h1
    · left
      rw [← Bool.not_eq_true] at h1 ⊢
      exact fun h2 => h1 ((hsub i).2 h2)
    · right
      rw [← hFV i hi, ← hFV j hj]
      exact h1
  · rcases h (d.DL i) (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩) with h1 | h1
    · left
      rw [← Bool.not_eq_true] at h1 ⊢
      exact fun h2 => h1 ((hsub i).1 h2)
    · right
      rw [hFV i hi, hFV j hj]
      exact h1

theorem mmE8 (hbp : chkBP = true) (hn : d.n = 8) {M : ℕ} (hM : M < 2 ^ d.nT) :
    d.e8 M = true ↔ isE8T d.n (d.mL M) = true := by
  unfold Dat.e8 isE8T regB
  simp only [tmBAnd, tmBImp, Bool.and_eq_true, Nat.beq_eq, tmAllN, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, List.all_eq_true, List.any_eq_true, hn, true_and,
    List.mem_range]
  obtain ⟨-, hperm, -⟩ := tmFacts d hn8 hT
  have htl : ∀ y, d.tl y = decT 8 (d.tab y) := by
    intro y
    unfold Dat.tl decT
    rw [hn]
  have hbits : ∀ q, (orN d.nT fun x => Bool.rec (motive := fun _ => ℕ) 0 (one (pt (d.tab x) 0))
      (bit M x)).testBit q = true ↔ ∃ x < d.nT, bit M x = true ∧ pt (d.tab x) 0 = q := by
    intro q
    rw [tmTestBit_orN]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [tmNIf]
    split_ifs with h
    · rw [tmTestBit_one]
      exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
    · simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_and]
      exact fun h' => absurd h' h
  have hg : ∀ y < d.nT, (d.tl y).getD 0 0 = pt (d.tab y) 0 := fun y _ => tmTl_getD d (by omega)
  rw [mmLen d hbp hM]
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨⟨a, fun x hx => ?_⟩, fun q hq => ?_⟩
    · obtain ⟨y, hy, hb, rfl⟩ := (mem_mL d _ _).1 hx
      rcases b y hy with h1 | h1
      · rw [hb] at h1
        exact absurd h1 (by decide)
      · rw [htl, ← evenP_eq]
        exact h1
    · have h1 : (ones 8).testBit q = true := tmTestBit_ones.2 hq
      rw [← c, hbits] at h1
      obtain ⟨y, hy, hb, e⟩ := h1
      exact ⟨d.tl y, (mem_mL d _ _).2 ⟨y, hy, hb, rfl⟩, by rw [hg y hy, e]⟩
  · rintro ⟨⟨a, b⟩, c⟩
    refine ⟨a, fun i hi => ?_, ?_⟩
    · by_cases hb : bit M i = true
      · right
        have := b _ ((mem_mL d _ _).2 ⟨i, hi, hb, rfl⟩)
        rw [htl, ← evenP_eq] at this
        exact this
      · left
        simpa using hb
    · apply Nat.eq_of_testBit_eq
      intro q
      rw [Bool.eq_iff_iff, hbits, tmTestBit_ones]
      constructor
      · rintro ⟨y, hy, -, rfl⟩
        have := (tmIsTab (hperm y hy)).2.2 0 (by omega)
        rwa [hn] at this
      · intro hq
        obtain ⟨t, ht, e⟩ := c q hq
        obtain ⟨y, hy, hb, rfl⟩ := (mem_mL d _ _).1 ht
        exact ⟨y, hy, hb, by rw [← hg y hy, e]⟩

theorem mmRep (hbp : chkBP = true) (c j : ℕ) (hc : c = 2 → d.n = 8) :
    d.repP c (d.dm j) = true ↔ RepL d c (d.DL j) := by
  unfold Dat.repP
  simp only [mmBOr, mmBIfF, tmBAnd, tmBeq, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne, ne_eq, mmAnyN, tmMul, tmAdd, and_true]
  have hE : ∀ i, d.dm j = d.nm i ↔ ∀ t, t ∈ d.DL j ↔ t ∈ d.DL (d.ix i) :=
    fun i => mmEq d hn8 hT (tmEnt_lt _ _ _) (tmEnt_lt _ _ _)
  have hl : ∀ i, (d.DL i).length = popc d.nb (d.dm i) := fun i => mmLen d hbp (tmEnt_lt _ _ _)
  unfold RepL
  refine or_congr (exists_congr fun i => and_congr Iff.rfl (hE i))
    (and_congr Iff.rfl (or_congr (hE _) (or_congr (hE _) (or_congr ⟨?_, ?_⟩
      (and_congr_right fun h2 => mmE8 d hn8 hT hbp (hc h2) (tmEnt_lt _ _ _))))))
  · rintro ⟨a, b, e⟩
    refine ⟨(mmSub d hn8 hT (tmEnt_lt _ _ _)).1 a, ?_, fun h => e ((hE _).2 h)⟩
    exact (congrArg (2 * ·) (hl j)).trans (b.trans (hl _).symm)
  · rintro ⟨a, b, e⟩
    refine ⟨(mmSub d hn8 hT (tmEnt_lt _ _ _)).2 a, ?_, fun h => e ((hE _).1 h)⟩
    exact (congrArg (2 * ·) (hl j)).symm.trans (b.trans (hl _))

theorem mmNamed (hbp : chkBP = true) (hN : chkNamedM d = true) :
    (∀ i < d.h + 2, d.ix i < d.nD) ∧ (∀ i < d.h, (d.DL (d.ix i)).length = 2 ^ (i + 1)) ∧
      (d.DL (d.ix d.h)).length = 2 ^ d.h := by
  unfold chkNamedM at hN
  simp only [tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmLetB, tmAllL, Nat.blt_eq, tmAdd,
    tmMul] at hN
  obtain ⟨hAmLen, -, -, -, hnmwLen, hnmwD, hAmSpan, -, hA0pop, -⟩ := hN
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · unfold Dat.ix
    rw [tmLget, List.getD_eq_getElem _ _ (by rw [hnmwLen]; exact hi)]
    exact hnmwD _ (List.getElem_mem _)
  · have h2 := tmAllI hAmSpan i (by rw [hAmLen]; exact hi)
    simp only [Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAdd, tmMul] at h2
    exact (mmLen d hbp (tmEnt_lt _ _ _)).trans (h2.2.trans (tmOne _))
  · exact (mmLen d hbp (tmEnt_lt _ _ _)).trans (hA0pop.trans (tmOne _))

theorem mmChain (S : List ℕ) (hS : ∀ s ∈ S, s < d.nT) (J : ℕ) (P : ℕ → Prop)
    (hP : ∀ s ∈ S, ∀ x < d.nT, P x → P (d.mt s x)) :
    ∀ (ch : List (ℕ × ℕ × ℕ)) (A : ℕ) (done : List Tab),
      (∀ y, bit A y = true → y < d.nT ∧ d.tl y ∈ done ∧ P y) →
      List.rec (motive := fun _ => ℕ → ℕ) (fun A => A)
        (fun c _ ih A => Loop.strictN A fun A =>
          Bool.rec (motive := fun _ => ℕ) 0 (ih (A.lor (one c.1)))
            (bit (orL S one) c.2.1 && (bit A c.2.2 && d.mt c.2.1 c.2.2 == c.1))) ch A = J →
      J ≠ 0 →
      chainOK (S.map d.tl) (idT d.n) done (ch.map (fun c => d.tl c.1)) = true ∧
      (∀ y, bit J y = true ↔ bit A y = true ∨ ∃ c ∈ ch, c.1 = y) ∧
      ∀ y, bit J y = true → y < d.nT ∧ P y
  | [], A, done, hA, h, _ => by
    change A = J at h
    subst h
    refine ⟨rfl, fun y => ?_, fun y hy => ⟨(hA y hy).1, (hA y hy).2.2⟩⟩
    simp
  | c :: ch, A, done, hA, h, hJ => by
    obtain ⟨-, -, hmt, hmul, -, -⟩ := tmFacts d hn8 hT
    dsimp only at h
    rw [tmStrictN] at h
    cases hc : (bit (orL S one) c.2.1 && (bit A c.2.2 && d.mt c.2.1 c.2.2 == c.1))
    · rw [hc] at h
      exact absurd h.symm hJ
    · rw [hc] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hs, hx, hm⟩ := hc
      rw [tmBit, tmTestBit_orL] at hs
      obtain ⟨s, hsS, hs1⟩ := hs
      rw [tmTestBit_one] at hs1
      obtain ⟨hxl, hxd, hPx⟩ := hA _ hx
      have hsl : c.2.1 < d.nT := hs1 ▸ hS s hsS
      have hyl : c.1 < d.nT := hm ▸ hmt _ hsl _ hxl
      have hA' : ∀ y, bit (A.lor (one c.1)) y = true →
          y < d.nT ∧ d.tl y ∈ d.tl c.1 :: done ∧ P y := by
        intro y hy
        rw [tmBit] at hy
        change (A ||| one c.1).testBit y = true at hy
        rw [Nat.testBit_or, Bool.or_eq_true, ← tmBit, tmTestBit_one] at hy
        rcases hy with hy | rfl
        · obtain ⟨a1, a2, a3⟩ := hA y hy
          exact ⟨a1, List.mem_cons_of_mem _ a2, a3⟩
        · refine ⟨hyl, List.mem_cons_self, ?_⟩
          rw [← hm]
          exact hP _ (hs1 ▸ hsS) _ hxl hPx
      obtain ⟨hch, hbits, hlt⟩ := mmChain S hS J P hP ch _ _ hA' h hJ
      refine ⟨?_, fun y => ?_, hlt⟩
      · simp only [List.map_cons, chainOK, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
          beq_iff_eq]
        refine ⟨Or.inr ⟨d.tl c.2.1, List.mem_map_of_mem (hs1 ▸ hsS), d.tl c.2.2, hxd, ?_⟩, hch⟩
        rw [hmul _ hsl _ hxl, hm]
      · rw [hbits y, tmBit]
        change (A ||| one c.1).testBit y = true ∨ _ ↔ _
        rw [Nat.testBit_or, Bool.or_eq_true, ← tmBit, tmTestBit_one]
        constructor
        · rintro ((h1 | h1) | ⟨c', hc', e⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨c, List.mem_cons_self, h1⟩
          · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', e⟩
        · rintro (h1 | ⟨c', hc', e⟩)
          · exact Or.inl (Or.inl h1)
          · rcases List.mem_cons.1 hc' with rfl | hc'
            · exact Or.inl (Or.inr e)
            · exact Or.inr ⟨c', hc', e⟩

theorem mmClos {S : List ℕ} {ch : List (ℕ × ℕ × ℕ)} {J : ℕ} (h : d.closOK S ch J = true)
    (hS : ∀ s ∈ S, s < d.nT) :
    ∃ Sc : List Tab, chainOK (S.map d.tl) (idT d.n) [] Sc = true ∧
      (∀ t, t ∈ Sc ↔ t ∈ d.mL J) ∧ subOK d.n (d.mL J) = true ∧ ∀ s ∈ S, bit J s = true := by
  obtain ⟨hnT, hperm, hmt, hmul, hid, -⟩ := tmFacts d hn8 hT
  unfold Dat.closOK at h
  simp only [mmBOr, mmBIfF, tmBAnd, tmBImp, tmBeq, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq, mmAnyN, tmAllN, tmMul, tmAdd,
    tmLetB, tmAllL, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨h0, hSJ, hcl, hch⟩ := h
  have hSJ' : ∀ s ∈ S, bit J s = true := by
    intro s hs
    refine mmSubM_iff.1 hSJ s ?_
    rw [tmBit, tmTestBit_orL]
    exact ⟨s, hs, tmTestBit_one.2 rfl⟩
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [tmBit] at h0
    exact absurd h0 (by simp)
  have hassoc : ∀ s < d.nT, ∀ x < d.nT, ∀ z < d.nT,
      d.mt (d.mt s x) z = d.mt s (d.mt x z) := by
    intro s hs x hx z hz
    refine eaG_inj d hn8 hT (hmt _ (hmt s hs x hx) z hz) (hmt s hs _ (hmt x hx z hz)) ?_
    rw [eaG_mul d hn8 hT (hmt s hs x hx) hz, eaG_mul d hn8 hT hs hx,
      eaG_mul d hn8 hT hs (hmt x hx z hz), eaG_mul d hn8 hT hx hz, mul_assoc]
  have hP : ∀ s ∈ S, ∀ x < d.nT, (∀ z < d.nT, bit J z = true → bit J (d.mt x z) = true) →
      ∀ z < d.nT, bit J z = true → bit J (d.mt (d.mt s x) z) = true := by
    intro s hs x hx hPx z hz hJz
    rw [hassoc s (hS s hs) x hx z hz]
    rcases hcl s hs _ (hmt x hx z hz) with h1 | h1
    · rw [hPx z hz hJz] at h1
      exact absurd h1 (by decide)
    · exact h1
  have hA : ∀ y, bit 1 y = true → y < d.nT ∧ d.tl y ∈ [idT d.n] ∧
      ∀ z < d.nT, bit J z = true → bit J (d.mt y z) = true := by
    intro y hy
    rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero] at hy
    subst hy
    refine ⟨hnT, by rw [hid]; exact List.mem_singleton_self _, fun z hz hJz => ?_⟩
    have e : d.mt 0 z = z := by
      refine eaG_inj d hn8 hT (hmt 0 hnT z hz) hz ?_
      rw [eaG_mul d hn8 hT hnT hz, eaG_zero d hn8 hT, one_mul]
    rw [e]
    exact hJz
  obtain ⟨hchain, hbits, hlt⟩ := mmChain d hn8 hT S hS J _ hP ch 1 [idT d.n] hA hch hJ0
  have hmemJ : ∀ t, t ∈ d.mL J ↔ ∃ y, bit J y = true ∧ d.tl y = t := by
    intro t
    rw [mem_mL]
    constructor
    · rintro ⟨y, -, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hlt y hy).1, hy, rfl⟩
  refine ⟨idT d.n :: ch.map (fun c => d.tl c.1), ?_, fun t => ?_, ?_, hSJ'⟩
  · simp only [chainOK, Bool.and_eq_true, Bool.or_eq_true, beq_self_eq_true, true_or, true_and]
    exact hchain
  · rw [hmemJ, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨c, hc, rfl⟩)
      · exact ⟨0, h0, hid⟩
      · exact ⟨c.1, (hbits _).2 (Or.inr ⟨c, hc, rfl⟩), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases (hbits y).1 hy with h1 | ⟨c, hc, rfl⟩
      · rw [tmBit, Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
        subst h1
        exact Or.inl hid
      · exact Or.inr ⟨c, hc, rfl⟩
  · simp only [subOK, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
      decide_eq_true_eq]
    refine ⟨⟨⟨⟨fun t ht => ?_, ?_⟩, fun a ha b hb => ?_⟩, fun a ha => ?_⟩, mmNd d hn8 hT J⟩
    · obtain ⟨y, hy, rfl⟩ := (hmemJ t).1 ht
      exact (tmIsTab (hperm y (hlt y hy).1)).1
    · exact (hmemJ _).2 ⟨0, h0, hid⟩
    · obtain ⟨y, hy, rfl⟩ := (hmemJ a).1 ha
      obtain ⟨z, hz, rfl⟩ := (hmemJ b).1 hb
      rw [hmul y (hlt y hy).1 z (hlt z hz).1]
      exact (hmemJ _).2 ⟨_, (hlt y hy).2 z (hlt z hz).1 hz, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := (hmemJ a).1 ha
      have hyl := (hlt y hy).1
      have hpow : ∀ m : ℕ, ∃ z, bit J z = true ∧ z < d.nT ∧ eaG d z = eaG d y ^ m := by
        intro m
        induction m with
        | zero => exact ⟨0, h0, hnT, by rw [eaG_zero d hn8 hT, pow_zero]⟩
        | succ m ih =>
          obtain ⟨z, hz, hzl, e⟩ := ih
          exact ⟨d.mt y z, (hlt y hy).2 z hzl hz, hmt y hyl z hzl,
            by rw [eaG_mul d hn8 hT hyl hzl, pow_succ', e]⟩
      obtain ⟨z, hz, hzl, e⟩ := hpow (orderOf (eaG d y) - 1)
      have hinv : (eaG d y)⁻¹ = eaG d z := by
        rw [e]
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
      rw [← eaG_tab d hn8 hT hyl, ← tab_inv, hinv, eaG_tab d hn8 hT hzl]
      exact (hmemJ _).2 ⟨z, hz, rfl⟩

theorem mmPinv {a : ℕ} (h : isPerm d.n a = true) :
    decT d.n (pinv d.n a) = invT (decT d.n a) ∧ ∀ p < d.n, pt (pinv d.n a) p < d.n := by
  obtain ⟨hTb, -, -⟩ := tmIsTab h
  obtain ⟨σ, hσ⟩ := exists_tab_eq hTb
  change tab σ = decT d.n a at hσ
  have hpa : ∀ i : Fin d.n, pt a i = σ i := by
    intro i
    have := getD_tab σ i
    rw [hσ, decT_getD i.isLt] at this
    exact this
  let f : ℕ → ℕ := fun p => if hp : p < d.n then (σ⁻¹ ⟨p, hp⟩ : ℕ) else 0
  have hf : ∀ p < d.n, f p < 8 := by
    intro p hp
    simp only [f, dif_pos hp]
    exact lt_of_lt_of_le (σ⁻¹ ⟨p, hp⟩).isLt hn8
  have e : pinv d.n a = sumN d.n (fun p => Nat.shiftLeft (f p) (Nat.mul 3 p)) := by
    unfold pinv
    rw [tmSumN, tmSumN, Finset.sum_range, Finset.sum_range]
    refine (Equiv.sum_comp σ⁻¹ _).symm.trans (Finset.sum_congr rfl fun p _ => ?_)
    have hσσ : σ (σ⁻¹ p) = p := by simp
    rw [hpa (σ⁻¹ p), hσσ]
    simp only [f, dif_pos p.isLt, Fin.eta]
  have key : ∀ p < d.n, pt (pinv d.n a) p = f p := by
    intro p hp
    rw [e]
    exact tmPt_pack hf hp
  have hinv : decT d.n (pinv d.n a) = tab σ⁻¹ := by
    apply List.ext_getElem
    · rw [decT_length, length_tab]
    · intro p h1 h2
      have hp : p < d.n := by rwa [decT_length] at h1
      rw [getElem_tab]
      simp only [decT, List.getElem_map, List.getElem_range]
      rw [key p hp]
      simp only [f, dif_pos hp]
  refine ⟨by rw [hinv, tab_inv, hσ], fun p hp => ?_⟩
  rw [key p hp]
  simp only [f, dif_pos hp]
  exact (σ⁻¹ ⟨p, hp⟩).isLt

end MM

theorem mmCase2 {n k : ℕ} (h : caseOf n k = 2) : n = 8 := by
  unfold caseOf at h
  simp only [mmBOr, tmBAnd, tmBeq] at h
  cases hA : (Nat.mod n 2 == 1 || Nat.mod k 2 == 0) <;> rw [hA] at h
  · cases hB : (n == 8 && k == 3) <;> rw [hB] at h
    · exact absurd (h : 1 = 2) (by decide)
    · simp only [Bool.and_eq_true, beq_iff_eq] at hB
      exact hB.1
  · have h' : (0 : ℕ) = 2 := h
    exact absurd h' (by decide)

theorem mmBeqB (a b : Bool) : beqB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

theorem mmRk {n : ℕ} {k : Mod} {L : List Tab} {r s f pw : ℕ} (hf : f = Fval n k L)
    (hpw : pw = cntF n k [idT n]) (hL : L.length = 2 ^ r) (h : f * one s = one r * pw) :
    cntF n k L * 2 ^ s = cntF n k [idT n] := by
  rw [hf, hpw, Fval, hL, tmOne, tmOne, mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos r) h

theorem mmRankOK {n : ℕ} {k : Mod} {L : List Tab} {r s : ℕ} (hL : L.length = 2 ^ r)
    (hc : cntF n k L * 2 ^ s = cntF n k [idT n]) : rankOK n k L r s = true := by
  simp [rankOK, hL, hc]

theorem mmRkPair {n : ℕ} {k : Mod} {L : List Tab} {r s : ℕ} (hL : L.length = 2 ^ r)
    (hc : cntF n k L * 2 ^ s = cntF n k [idT n]) : rkPair n k L = (r, s) := by
  unfold rkPair
  rw [hL, Nat.log_pow (by norm_num), ← hc, Nat.mul_div_cancel_left _ (mmCntF_pos n k L),
    Nat.log_pow (by norm_num)]

theorem chkModM_sound (d : Dat) (k : Mod) (hn : 5 ≤ d.n) (hn8 : d.n ≤ 8) (hbp : chkBP = true)
    (hT : chkTM d = true) (hEA : chkEAM d = true) (hN : chkNamedM d = true)
    (h : chkModM d (mIdx k) = true)
    (hF : ∀ j < d.nD, lget (lget d.FV (mIdx k) []) j 0 = Fval d.n k (d.DL j)) :
    ModOK d k := by
  obtain ⟨hnT, hperm, hmt, hmul, hid, hinj⟩ := tmFacts d hn8 hT
  obtain ⟨hEA', hb⟩ := chkEAM_sound d hn8 hbp hT hEA hN
  obtain ⟨-, hmem, -⟩ := chkEA_spec hEA'
  have hDLmem : ∀ j < d.nD, d.DL j ∈ d.DD :=
    fun j hj => List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have hsubD : ∀ j < d.nD, subOK d.n (d.DL j) = true := fun j hj => (hmem _ (hDLmem j hj)).1
  have h0 : ∀ j < d.nD, d.tl 0 ∈ d.DL j := fun j hj => by
    rw [hid]
    exact (subOK_spec (hsubD j hj)).2.1
  have hdm : ∀ j, d.dm j < 2 ^ d.nT := fun j => tmEnt_lt _ _ _
  have hl : ∀ j, (d.DL j).length = popc d.nb (d.dm j) := fun j => mmLen d hbp (hdm j)
  obtain ⟨hix, hlA, hlA0⟩ := mmNamed d hn8 hT hbp hN
  have hD : 0 < d.nD := lt_of_le_of_lt (Nat.zero_le _) (hix 0 (by omega))
  have hD0 : d.dm 0 = 1 := by
    have h' := hEA
    unfold chkEAM at h'
    simp only [tmLetB, tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAllN] at h'
    exact h'.2.1
  have hc2 : caseOf d.n (mIdx k) = 2 → d.n = 8 := mmCase2
  unfold chkModM at h
  simp only [tmBAnd, Bool.and_eq_true, tmLetB] at h
  obtain ⟨-, hlen, hall, hRO, hcov, hJ, hrk, hq, hst⟩ := h
  rw [Nat.beq_eq, tmLenL] at hlen
  have hDbl : d.Db.length = d.nD := by
    have h' := hEA
    unfold chkEAM at h'
    simp only [tmLetB, tmBAnd, Bool.and_eq_true, Nat.beq_eq, tmLenL, tmAllN] at h'
    exact h'.2.2.1
  have hrow : ∀ i < d.nD, (lget d.FV (mIdx k) []).getD i 0 < 65536 ∧
      (lget d.FV (mIdx k) []).getD i 0 = Nat.mul (one (lenL (d.Db.getD i [])))
        (d.cntM (mIdx k) (d.wM (mIdx k)) (d.Db.getD i [])) := by
    intro i hi
    have h1 := tmAll2 hall i (by omega)
    rw [← List.getD_eq_getElem d.Db [] (by omega)] at h1
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    exact h1
  have hFVlt : ∀ x ∈ lget d.FV (mIdx k) [], x < 2 ^ 16 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := (hrow i (by omega)).1
    rw [List.getD_eq_getElem _ _ hi] at this
    exact this
  have hFV : ∀ j < d.nD, ent (packL 16 (lget d.FV (mIdx k) [])) 16 j = Fval d.n k (d.DL j) := by
    intro j hj
    rw [mmPackL 16 _ hFVlt j, ← tmLget]
    exact hF j hj
  have hl0 : (d.DL 0).length = 1 := (mmOne d hn8 hT (hdm 0) (h0 0 hD)).1 hD0
  have hb0 : d.Db.getD 0 [] = [] := by
    have h1 := (hb 0 hD).2.1
    rw [Dat.bas, tmLget, List.length_map] at h1
    rw [hl0] at h1
    have h3 : (d.Db.getD 0 []).length = 0 := by
      have := Nat.pow_right_injective (le_refl 2) (h1.symm.trans (pow_zero 2).symm)
      exact this
    exact List.eq_nil_of_length_eq_zero h3
  have hpw : popc d.vb (d.wM (mIdx k)) = cntF d.n k [idT d.n] := by
    have h1 := (hrow 0 hD).2
    rw [hb0] at h1
    have h2 := hF 0 hD
    rw [tmLget] at h2
    rw [h2, Fval, hl0, one_mul] at h1
    rw [mmCntF_congr d.n k (B := [idT d.n]) (fun t => by
      change t ∈ d.mL (d.dm 0) ↔ _
      rw [hD0, mmML1 d hn8 hT, List.mem_singleton, hid])] at h1
    rw [h1]
    change popc d.vb (d.wM (mIdx k)) = Nat.mul 1 (popc d.vb (d.wM (mIdx k)))
    rw [tmMul, one_mul]
  have hOM := mmOff d hn8 hT k h0 hFV
  have hRM : ∀ j, bit (orN d.nD fun j => Bool.rec (motive := fun _ => ℕ) 0 (one j)
      (d.repP (caseOf d.n (mIdx k)) (d.dm j))) j = true ↔
        j < d.nD ∧ RepL d (caseOf d.n (mIdx k)) (d.DL j) := by
    intro j
    rw [tmBit, tmTestBit_orN_nIf, mmRep d hn8 hT hbp _ j hc2]
  have hU : ∀ y, bit (orN d.nD fun j => Bool.rec (motive := fun _ => ℕ) 0 (d.dm j)
      (bit (d.offM (packL 16 (lget d.FV (mIdx k) []))) j)) y = true ↔
        ∃ j < d.nD, offOK d.n k d.DD (d.DL j) = true ∧ bit (d.dm j) y = true := by
    intro y
    rw [tmBit, tmTestBit_orN]
    refine exists_congr fun j => ⟨fun ⟨hj, e⟩ => ?_, fun ⟨hj, ho, e⟩ => ⟨hj, ?_⟩⟩
    · rw [tmNIf] at e
      split_ifs at e with ho
      · exact ⟨hj, ((hOM j).1 ho).2, by rw [tmBit]; exact e⟩
      · simp at e
    · rw [tmNIf, if_pos ((hOM j).2 ⟨hj, ho⟩), ← tmBit]
      exact e
  have hcntL : ∀ j < d.nD, ∀ r s, (d.DL j).length = 2 ^ r →
      ent (packL 16 (lget d.FV (mIdx k) [])) 16 j * one s = one r * popc d.vb (d.wM (mIdx k)) →
      cntF d.n k (d.DL j) * 2 ^ s = cntF d.n k [idT d.n] :=
    fun j hj r s hL h => mmRk (hFV j hj) hpw hL h
  have hixe : ∀ i, d.nmw.getD i 0 = d.ix i := fun i => by rw [Dat.ix, tmLget]
  have hh : d.h = d.n / 2 := rfl
  have hTL : ∀ t, t ∈ d.TL ↔ ∃ y < d.nT, d.tl y = t := by
    intro t
    simp [Dat.TL]
  have horL : ∀ (S : List ℕ) s, s ∈ S → bit (orL S one) s = true := by
    intro S s hs
    rw [tmBit, tmTestBit_orL]
    exact ⟨s, hs, tmTestBit_one.2 rfl⟩
  have hrep : ∀ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) →
      offOK d.n k d.DD (d.DL j) = true :=
    fun j hj hr => ((hOM j).1 (mmSubM_iff.1 hRO j ((hRM j).2 ⟨hj, hr⟩))).2
  generalize d.offM (packL 16 (lget d.FV (mIdx k) [])) = OM at hOM hU hRO hcov hJ hst
  generalize (orN d.nD fun j => Bool.rec (motive := fun _ => ℕ) 0 (one j)
    (d.repP (caseOf d.n (mIdx k)) (d.dm j))) = RM at hRM hRO hcov hq hrep
  generalize (orN d.nD fun j => Bool.rec (motive := fun _ => ℕ) 0 (d.dm j) (bit OM j)) = U
    at hU hJ
  generalize packL 16 (lget d.FV (mIdx k) []) = FVP at hFV hcntL hrk hq hst
  generalize popc d.vb (d.wM (mIdx k)) = pw at hpw hcntL hrk hq hst
  refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro j hj ho
    unfold Dat.covOK at hcov
    simp only [tmBAnd, tmBeq, Bool.and_eq_true, beq_iff_eq, mmAnyN, tmLetB, tmAllL, tmLget,
      Nat.beq_eq] at hcov
    obtain ⟨hcv, hcvs⟩ := hcov
    have hj' := (hOM j).2 ⟨hj, ho⟩
    rw [← hcv, tmBit, tmTestBit_orL] at hj'
    obtain ⟨x, hx, hxj⟩ := hj'
    rw [tmTestBit_one] at hxj
    obtain ⟨-, hxr, hxp, hxpop, hxb⟩ := hcvs x hx
    rw [hxj] at hxpop hxb
    obtain ⟨hr, hrep⟩ := (hRM _).1 hxr
    obtain ⟨hgT, -, -⟩ := tmIsTab hxp
    obtain ⟨hinvE, hinvlt⟩ := mmPinv d hn8 hT hxp
    refine ⟨_, hr, hrep, decT d.n (x.getD 2 0), hgT, fun b' hb' => ?_, by rw [hl, hl, hxpop]⟩
    rw [Dat.bas, tmLget] at hb'
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hb'
    obtain ⟨i, hi, hbit, he⟩ := hxb b hbm
    have hbl : b < d.nT := ((eaM_facts d hn8 hT hEA hr).1 b hbm).1
    have e : cjT (decT d.n (x.getD 2 0)) (d.tl b) = d.tl i := by
      unfold cjT
      rw [← hinvE]
      change _ = decT d.n (d.tab i)
      rw [he, decT_pmul hinvlt, decT_pmul (tmIsTab (hperm b hbl)).2.2]
      rfl
    rw [e]
    exact (mem_mL d _ _).2 ⟨i, hi, hbit, rfl⟩
  ·
    unfold Dat.jOK at hJ
    simp only [tmBAnd, tmBeq, Bool.and_eq_true, tmLetB, tmAllL, tmLget] at hJ
    obtain ⟨hcl, hJSU, hUJ, hcase⟩ := hJ
    have hJS : ∀ s ∈ d.JS.getD (mIdx k) [], s < d.nT := by
      intro s hs
      obtain ⟨j, -, -, hbit⟩ := (hU s).1 (hJSU s hs)
      exact mmBit_lt d (hdm j) hbit
    obtain ⟨Sc, hch, hSc, hsubJ, hSJ⟩ := mmClos d hn8 hT hcl hJS
    refine ⟨d.mL (d.JU.getD (mIdx k) 0), (d.JS.getD (mIdx k) []).map d.tl, Sc, hsubJ, hch,
      fun g hg => ?_, hSc, fun g hg => ?_, fun j hj ho t ht => ?_, fun hc0 => ?_,
      fun hc2' => ?_, fun hc1 => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      exact (hSc _).2 ((mem_mL d _ _).2 ⟨s, hJS s hs, hSJ s hs, rfl⟩)
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      obtain ⟨j, hj, ho, hbit⟩ := (hU s).1 (hJSU s hs)
      exact ⟨j, hj, ho, (mem_mL d _ _).2 ⟨s, hJS s hs, hbit, rfl⟩⟩
    · obtain ⟨y, hy, hbit, rfl⟩ := (mem_mL d _ _).1 ht
      exact (mem_mL d _ _).2 ⟨y, hy, mmSubM_iff.1 hUJ y ((hU y).2 ⟨j, hj, ho, hbit⟩), rfl⟩
    · simp only [(beq_iff_eq.2 hc0 : (caseOf d.n (mIdx k) == 0) = true), beq_iff_eq] at hcase
      rw [hcase]
      exact fun t => Iff.rfl
    · have e0 : (caseOf d.n (mIdx k) == 0) = false := by
        rw [hc2']
        rfl
      simp only [e0, (beq_iff_eq.2 hc2' : (caseOf d.n (mIdx k) == 2) = true),
        beq_iff_eq] at hcase
      rw [hcase]
      intro t
      rw [mem_mL, hTL]
      refine exists_congr fun y => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ?_, h.2⟩⟩
      rw [tmBit]
      exact tmTestBit_ones.2 h.1
    · have e0 : (caseOf d.n (mIdx k) == 0) = false := by
        rw [hc1]
        rfl
      have e2 : (caseOf d.n (mIdx k) == 2) = false := by
        rw [hc1]
        rfl
      simp only [e0, e2, Bool.and_eq_true] at hcase
      obtain ⟨hcl5, hS5, hDJ⟩ := hcase
      have hDD : ∀ y, bit (d.dcM.lor d.dtM) y = true ↔
          bit d.dcM y = true ∨ bit d.dtM y = true := by
        intro y
        rw [tmBit, tmBit, tmBit]
        change (d.dcM ||| d.dtM).testBit y = true ↔ _
        rw [Nat.testBit_or, Bool.or_eq_true]
      have hdt : ∀ x, bit d.dtM x = true ↔
          x < d.nT ∧ bit d.invM x = true ∧ suppCardT (d.tl x) = 4 := by
        intro x
        rw [tmBit]
        unfold Dat.dtM
        rw [tmStrictN, tmTestBit_orN_nIf, tmBAnd, Bool.and_eq_true, Nat.beq_eq, supp_eq]
        exact Iff.rfl
      have hS5lt : ∀ s ∈ d.S5, s < d.nT := by
        intro s hs
        rcases (hDD s).1 (mmSubM_iff.1 hS5 s (horL _ s hs)) with h1 | h1
        · exact mmBit_lt d (hdm _) h1
        · exact ((hdt s).1 h1).1
      obtain ⟨Sc5, hch5, hSc5, -, hS5J⟩ := mmClos d hn8 hT hcl5 hS5lt
      refine ⟨d.S5.map d.tl, Sc5, hch5, fun g hg => ?_, hSc5, fun g hg => ?_, fun t ht => ?_,
        fun t ht hsq hs4 => ?_⟩
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
        exact (hSc5 _).2 ((mem_mL d _ _).2 ⟨s, hS5lt s hs, hS5J s hs, rfl⟩)
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
        rcases (hDD s).1 (mmSubM_iff.1 hS5 s (horL _ s hs)) with h1 | h1
        · exact Or.inl ((mem_mL d _ _).2 ⟨s, hS5lt s hs, h1, rfl⟩)
        · obtain ⟨hsl, hinv, hs4⟩ := (hdt s).1 h1
          obtain ⟨-, -, hss⟩ := (eaInv_bit d s).1 hinv
          refine Or.inr ⟨(hTL _).2 ⟨s, hsl, rfl⟩, ?_, hs4⟩
          rw [hmul s hsl s hsl, hss, hid]
      · obtain ⟨y, hy, hbit, rfl⟩ := (mem_mL d _ _).1 ht
        exact (mem_mL d _ _).2 ⟨y, hy, mmSubM_iff.1 hDJ y ((hDD y).2 (Or.inl hbit)), rfl⟩
      · obtain ⟨x, hx, rfl⟩ := (hTL t).1 ht
        have hx0 : x ≠ 0 := by
          rintro rfl
          rw [hid, suppCardT_idT] at hs4
          exact absurd hs4 (by norm_num)
        have hxx : d.mt x x = 0 := by
          refine hinj _ (hmt x hx x hx) 0 hnT ?_
          rw [← hmul x hx x hx, hsq, hid]
        have hinv : bit d.invM x = true := (eaInv_bit d x).2 ⟨hx, Nat.pos_of_ne_zero hx0, hxx⟩
        exact (mem_mL d _ _).2 ⟨x, hx, mmSubM_iff.1 hDJ x ((hDD x).2 (Or.inr
          ((hdt x).2 ⟨hx, hinv, hs4⟩))), rfl⟩
  ·
    intro hc0 i hi
    unfold Dat.ranksOK at hrk
    simp only [tmBAnd, tmBImp, tmBeq, tmLget, tmAdd, rkOK] at hrk
    simp only [(beq_iff_eq.2 hc0 : (caseOf d.n (mIdx k) == 0) = true), tmAllN] at hrk
    have h1 := beq_iff_eq.1 (hrk i hi)
    rw [hixe] at h1
    exact mmRankOK (hlA i hi) (hcntL _ (hix i (by omega)) _ _ (hlA i hi) h1)
  ·
    intro hc0
    unfold Dat.ranksOK at hrk
    simp only [tmBAnd, tmBImp, tmBeq, tmLget, tmAdd, rkOK] at hrk
    simp only [(beq_eq_false_iff_ne.2 hc0 : (caseOf d.n (mIdx k) == 0) = false),
      Bool.and_eq_true, tmAllN] at hrk
    obtain ⟨ha, hb', -⟩ := hrk
    refine ⟨fun i hi => ?_, ?_⟩
    · have h1 := beq_iff_eq.1 (ha i hi)
      rw [hixe, tmNIf] at h1
      simp only [beq_iff_eq] at h1
      exact mmRankOK (hlA i hi) (hcntL _ (hix i (by omega)) _ _ (hlA i hi) h1)
    · have h1 := beq_iff_eq.1 hb'
      rw [hixe] at h1
      exact mmRankOK hlA0 (hcntL _ (hix _ (by omega)) _ _ hlA0 h1)
  ·
    intro hc j hj hE8
    have hn8' := hc2 hc
    unfold Dat.ranksOK at hrk
    simp only [tmBAnd, tmBImp, tmBeq, tmLget, tmAdd, rkOK] at hrk
    have e0 : (caseOf d.n (mIdx k) == 0) = false := by
      rw [hc]
      rfl
    simp only [e0, Bool.and_eq_true, (beq_iff_eq.2 hc : (caseOf d.n (mIdx k) == 2) = true),
      Bool.not_true, Bool.false_or, tmAllN] at hrk
    obtain ⟨-, -, hrk⟩ := hrk
    have h1 := hrk j hj
    rw [(mmE8 d hn8 hT hbp hn8' (hdm j)).2 hE8, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
    have hL : (d.DL j).length = 2 ^ 3 := by
      unfold isE8T at hE8
      simp only [Bool.and_eq_true, beq_iff_eq] at hE8
      rw [hE8.1.1.2]
      norm_num
    exact mmRankOK hL (hcntL _ hj _ _ hL h1)
  ·
    have hfac : d.nT ≤ 40320 := by
      obtain ⟨-, hlen', hf, hm⟩ := chkTM_sound d hn8 hT
      have hTLl : d.TL.length = d.nT := by simp [Dat.TL]
      rw [hTLl] at hlen'
      have h1 : d.nT ≤ d.n.factorial := by
        rw [hf, ← hlen']
        exact Nat.le_mul_of_pos_right _ (by omega)
      have h2 : d.n.factorial ≤ (8 : ℕ).factorial := Nat.factorial_le hn8
      have h3 : (8 : ℕ).factorial = 40320 := by decide
      omega
    have hDbl16 : ∀ x ∈ d.Db.map lenL, x < 2 ^ 4 := by
      intro x hx
      obtain ⟨b, hbD, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbD
      have hiD : i < d.nD := by omega
      have h1 := (hb i hiD).2.1
      rw [Dat.bas, tmLget, List.length_map, List.getD_eq_getElem _ _ hi] at h1
      have h2 : (d.DL i).length ≤ d.nT := by
        change (((List.range d.nT).filter (fun y => bit (d.dm i) y)).map d.tl).length ≤ _
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (List.length_range).le
      rw [tmLenL]
      have h3 : 2 ^ d.Db[i].length < 2 ^ 16 := by omega
      have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
      omega
    have hRK : ∀ j < d.nD, ent (List.rec (motive := fun _ => ℕ) 0
        (fun b _ ih => Nat.lor (lenL b) (Nat.shiftLeft ih 4)) d.Db) 4 j =
          (d.Db.getD j []).length := by
      intro j hj
      rw [mmRK, mmPackL 4 _ hDbl16 j, List.getD_eq_getElem _ _ (by simp; omega),
        List.getD_eq_getElem _ _ (by omega), List.getElem_map, tmLenL]
    have hLj : ∀ j < d.nD, (d.DL j).length = 2 ^ (d.Db.getD j []).length := by
      intro j hj
      have h1 := (hb j hj).2.1
      rwa [Dat.bas, tmLget, List.length_map] at h1
    have hqgen : ∀ a b, d.qOK FVP (List.rec (motive := fun _ => ℕ) 0
        (fun b _ ih => Nat.lor (lenL b) (Nat.shiftLeft ih 4)) d.Db) pw RM a b = true →
        (∀ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) → qRow d.n k a b (d.DL j) = true) ∧
        ∃ j < d.nD, RepL d (caseOf d.n (mIdx k)) (d.DL j) ∧ qWit d.n k a b (d.DL j) = true := by
      intro a b hq
      unfold Dat.qOK at hq
      simp only [mmBOr, mmBIfF, tmBAnd, tmBImp, tmBeq, Bool.or_eq_true, Bool.and_eq_true,
        Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq, mmAnyN, tmAllN, tmMul, tmAdd,
        tmLetB, tmAllL, Nat.blt_eq, Nat.ble_eq, rkOK, tmLget] at hq
      obtain ⟨hq1, j, hj, hRj, s, -, hrkj, hle⟩ := hq
      refine ⟨fun j' hj' hR => ?_, j, hj, ((hRM j).1 hRj).2, ?_⟩
      · rcases hq1 j' hj' with h1 | ⟨hpos, s', -, hrk', hle'⟩
        · rw [(hRM j').2 ⟨hj', hR⟩] at h1
          exact absurd h1 (by decide)
        · rw [hRK j' hj'] at hpos hrk' hle'
          have hc := hcntL j' hj' _ _ (hLj j' hj') hrk'
          rw [qRow, mmRkPair (hLj j' hj') hc, mmRankOK (hLj j' hj') hc]
          simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hpos, hle'⟩
      · rw [hRK j hj] at hrkj hle
        have hc := hcntL j hj _ _ (hLj j hj) hrkj
        rw [qWit, mmRkPair (hLj j hj) hc]
        simpa using hle
    by_cases hc0 : caseOf d.n (mIdx k) = 0
    · have e : Nat.beq (caseOf d.n (mIdx k)) 0 = true := by rw [Nat.beq_eq]; exact hc0
      simp only [e] at hq
      rw [if_pos hc0, if_pos hc0]
      exact hqgen 1 1 hq
    · have e : Nat.beq (caseOf d.n (mIdx k)) 0 = false := by
        rw [tmBeq]
        exact beq_eq_false_iff_ne.2 hc0
      simp only [e] at hq
      rw [if_neg hc0, if_neg hc0]
      exact hqgen _ _ hq
  ·
    intro hc0 j hj ho
    have e : Nat.beq (caseOf d.n (mIdx k)) 0 = false := by
      rw [tmBeq]
      exact beq_eq_false_iff_ne.2 hc0
    simp only [e] at hst
    unfold Dat.strongOK at hst
    simp only [tmBImp, tmAllN, Bool.or_eq_true, Bool.not_eq_true'] at hst
    rcases hst j hj with h1 | h1
    · rw [(hOM j).2 ⟨hj, ho⟩] at h1
      exact absurd h1 (by decide)
    · rw [mmBeqB, Nat.blt_eq, Nat.beq_eq, hpw, hFV j hj] at h1
      rw [h1]
      exact mmEq d hn8 hT (hdm j) (tmEnt_lt _ _ _)

variable {n : ℕ}

theorem exists_sylow_T {T : List Tab} {e m : ℕ} (hT : subOK n T = true) (hc : T.length = 2 ^ e)
    (hf : n.factorial = 2 ^ e * m) (hm : m % 2 = 1) :
    ∃ S : Sylow 2 (Gp n), (S : Subgroup (Gp n)) = subOf n T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (subOf n T) = 2 ^ e := by rw [card_subOf hT, hc]
  have hp : IsPGroup 2 (subOf n T) := IsPGroup.of_card hcard
  refine ⟨hp.toSylow ?_, rfl⟩
  have h1 := Subgroup.card_mul_index (subOf n T)
  rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, hf] at h1
  have h2 : (subOf n T).index = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h2]
  omega

theorem closure_map_tab (gensP : List (Gp n)) :
    Subgroup.closure {x : Gp n | tab x ∈ gensP.map tab} = Subgroup.closure {g | g ∈ gensP} := by
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← tab_injective hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem closure_eq_of_chain {G S L : List Tab} (hL : subOK n L = true)
    (hc : chainOK G (idT n) [] S = true) (hGS : ∀ g ∈ G, g ∈ S) (hSL : ∀ t, t ∈ S ↔ t ∈ L) :
    Subgroup.closure {x : Gp n | tab x ∈ G} = subOf n L := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_subOf hL]
    exact (hSL _).1 (hGS _ hx)
  · intro x hx
    rw [mem_subOf hL] at hx
    obtain ⟨σ, hσ, hσx⟩ := chain_sound' G
      (fun g hg => (subOK_spec hL).1 g ((hSL g).1 (hGS g hg))) S [] hc (by simp) _
      ((hSL _).2 hx)
    rwa [← tab_injective hσx]

theorem subOf_le_iff {L L' : List Tab} (hL : subOK n L = true) (hL' : subOK n L' = true) :
    subOf n L ≤ subOf n L' ↔ ∀ t ∈ L, t ∈ L' := by
  constructor
  · intro h t ht
    obtain ⟨x, rfl⟩ := exists_tab_eq ((subOK_spec hL).1 t ht)
    exact (mem_subOf hL').1 (h ((mem_subOf hL).2 ht))
  · intro h x hx
    exact (mem_subOf hL').2 (h _ ((mem_subOf hL).1 hx))

theorem subOf_eq_iff {L L' : List Tab} (hL : subOK n L = true) (hL' : subOK n L' = true) :
    subOf n L = subOf n L' ↔ ∀ t, t ∈ L ↔ t ∈ L' := by
  constructor
  · intro h t
    exact ⟨fun ht => (subOf_le_iff hL hL').1 h.le t ht,
      fun ht => (subOf_le_iff hL' hL).1 h.ge t ht⟩
  · exact subOf_eq_of_iff hL hL'

theorem inNk_iff (k : Mod) (σ : Gp n) (m : ℕ) :
    inNk n k (actM n (tab σ) m ^^^ m) = true ↔
      permAct n σ (vecOfNat n m) * vecOfNat n m ∈ k.N n := by
  rw [← vecOfNat_mem_N, vecOfNat_xor, vecOfNat_actM]

def fixN (k : Mod) (w : U n) : Subgroup (Gp n) where
  carrier := {σ | permAct n σ w * w ∈ k.N n}
  one_mem' := by
    change permAct n 1 w * w ∈ k.N n
    rw [map_one, MulAut.one_apply, U_mul_self]
    exact (k.N n).one_mem
  mul_mem' := fun {a b} ha hb => by
    change permAct n (a * b) w * w ∈ k.N n
    have h1 := k.isInv_N n a _ hb
    have e : permAct n (a * b) w * w =
        permAct n a (permAct n b w * w) * (permAct n a w * w) := by
      rw [map_mul (permAct n) a b, MulAut.mul_apply, map_mul (permAct n a) (permAct n b w) w,
        mul_assoc, ← mul_assoc (permAct n a w), U_mul_self, one_mul]
    rw [e]
    exact (k.N n).mul_mem h1 ha
  inv_mem' := fun {a} ha => by
    change permAct n a⁻¹ w * w ∈ k.N n
    have h1 := k.isInv_N n a⁻¹ _ ha
    have e : permAct n a⁻¹ (permAct n a w * w) = permAct n a⁻¹ w * w := by
      rw [map_mul (permAct n a⁻¹), ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MulAut.one_apply, mul_comm]
    rwa [e] at h1

theorem cntF_basis (k : Mod) {G L : List Tab} (hL : subOK n L = true)
    (hcl : Subgroup.closure {x : Gp n | tab x ∈ G} = subOf n L) (hGL : ∀ g ∈ G, g ∈ L) :
    cntF n k G = cntF n k L := by
  unfold cntF
  congr 1
  refine List.filter_congr fun m _ => ?_
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h t ht
    obtain ⟨σ, rfl⟩ := exists_tab_eq ((subOK_spec hL).1 t ht)
    have hσ : σ ∈ Subgroup.closure {x : Gp n | tab x ∈ G} := by
      rw [hcl, mem_subOf hL]
      exact ht
    have hle : Subgroup.closure {x : Gp n | tab x ∈ G} ≤ fixN k (vecOfNat n m) := by
      rw [Subgroup.closure_le]
      intro x hx
      exact (inNk_iff k x m).1 (h _ hx)
    exact (inNk_iff k σ m).2 (hle hσ)
  · intro h g hg
    exact h g (hGL g hg)

theorem cj_of_basis {G L C : List Tab} (hL : subOK n L = true) (hC : subOK n C = true)
    (hcl : Subgroup.closure {x : Gp n | tab x ∈ G} = subOf n L) {g : Tab}
    (hg : isTab n g = true) (hgb : ∀ b ∈ G, cjT g b ∈ C) (hlen : L.length = C.length) :
    ∃ γ : Gp n, cj γ (subOf n L) = subOf n C := by
  obtain ⟨γ, rfl⟩ := exists_tab_eq hg
  refine ⟨γ, ?_⟩
  have hle : subOf n L ≤ cj γ⁻¹ (subOf n C) := by
    rw [← hcl, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_cj, inv_inv, mem_subOf hC, ← cjT_tab]
    exact hgb _ hx
  have hle' : cj γ (subOf n L) ≤ subOf n C := by
    intro x hx
    rw [mem_cj] at hx
    have := hle hx
    rw [mem_cj, inv_inv] at this
    simpa [mul_assoc] using this
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  have hc : Nat.card (cj γ (subOf n L)) = Nat.card (subOf n L) := by
    unfold cj
    exact Subgroup.card_map_of_injective (MulAut.conj γ).injective
  simp [hc, card_subOf hC, card_subOf hL, hlen]

theorem classificationP (hn : 5 ≤ n) (k : Mod) {T : List Tab} {D : List (List Tab)}
    {P : List Tab → Prop} {S : Sylow 2 (Gp n)}
    (hS : (S : Subgroup (Gp n)) = subOf n T) (hT : subOK n T = true) (hD : chkEA n T D = true)
    (hreps : ∀ L ∈ D, P L → offOK n k D L = true)
    (hcover : ∀ K ∈ D, offOK n k D K = true →
      ∃ L ∈ D, P L ∧ ∃ γ : Gp n, cj γ (subOf n L) = subOf n K) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ L ∈ D, P L ∧ ∃ γ : Gp n, A = cj γ (subOf n L) := by
  intro A
  constructor
  · intro hA
    obtain ⟨hcomm, hsq⟩ := hA.comm_sq hn
    obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hsq)
    have hKcomm : ∀ a ∈ cj γ A, ∀ b ∈ cj γ A, a * b = b * a := by
      intro a ha b hb
      rw [mem_cj] at ha hb
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hcomm _ ha _ hb)
      simpa [mul_assoc] using h1
    have hKsq : ∀ a ∈ cj γ A, a * a = 1 := by
      intro a ha
      rw [mem_cj] at ha
      have h1 := congrArg (fun x => γ * x * γ⁻¹) (hsq _ ha)
      simpa [mul_assoc] using h1
    obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hT hD (cj γ A)
      (fun x hx => by
        have := hγ hx
        rw [hS] at this
        exact (mem_subOf hT).1 this) hKcomm hKsq
    have hKeq : cj γ A = subOf n C := subOf_eq hCok hKC
    have hoff : offOK n k D C = true :=
      (isOffG_iff_offOK hn k hT hD hC).1 (by rw [← hKeq]; exact hA.cj γ)
    obtain ⟨L, hL, hP, δ, hδ⟩ := hcover C hC hoff
    refine ⟨L, hL, hP, γ⁻¹ * δ, ?_⟩
    rw [cj_mul, hδ, ← hKeq, cj_inv_cj]
  · rintro ⟨L, hL, hP, γ, rfl⟩
    exact ((isOffG_iff_offOK hn k hT hD hL).2 (hreps L hL hP)).cj γ

theorem q_valueD (hn : 5 ≤ n) (k : Mod) {D : List (List Tab)} {P : List Tab → Prop}
    {snum sden : ℕ}
    (hcls : ∀ A : Subgroup (Gp n), IsOffG n k A ↔
      ∃ C ∈ D, P C ∧ ∃ γ : Gp n, A = cj γ (subOf n C))
    (hsub : ∀ C ∈ D, subOK n C = true)
    (hrows : ∀ C ∈ D, P C → qRow n k snum sden C = true)
    (hwit : ∃ C ∈ D, P C ∧ qWit n k snum sden C = true)
    (hsden : 0 < sden) (hle : snum ≤ sden) :
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = (((snum : ℚ) / sden : ℚ) : WithTop ℚ) := by
  have hsd : (0 : ℚ) < sden := by exact_mod_cast hsden
  refine qOf_eq_of_offenders (V_sq' k) ?_ ?_ ?_
  · rw [div_le_one hsd]
    exact_mod_cast hle
  · intro B hB
    obtain ⟨A, hAB, hA⟩ := exists_pullback k hB
    obtain ⟨C, hC, hpr, γ, hAC⟩ := (hcls A).1 hA
    obtain ⟨hr, hpos, hbound⟩ := qRow_spec hn k (hsub C hC) (hrows C hC hpr)
    rw [← hAB, hAC, rAV_map_cj, hr]
    have hposQ : (0 : ℚ) < (rkPair n k C).1 := by exact_mod_cast hpos
    rw [div_le_div_iff₀ hsd hposQ]
    have h1 : snum * (rkPair n k C).1 ≤ (rkPair n k C).2 * sden := by
      rw [Nat.mul_comm (rkPair n k C).2 sden]
      exact hbound
    exact_mod_cast h1
  · obtain ⟨C, hC, hpr, hw⟩ := hwit
    obtain ⟨hr, hpos, -⟩ := qRow_spec hn k (hsub C hC) (hrows C hC hpr)
    refine ⟨(subOf n C).map (Mod.act n k), ?_, ?_⟩
    · have : IsOffG n k (subOf n C) := (hcls _).2 ⟨C, hC, hpr, 1, (cj_one _).symm⟩
      exact this
    · rw [hr]
      have hposQ : (0 : ℚ) < (rkPair n k C).1 := by exact_mod_cast hpos
      rw [div_le_div_iff₀ hposQ hsd]
      simp only [qWit, decide_eq_true_eq] at hw
      have h2 : (rkPair n k C).2 * sden ≤ snum * (rkPair n k C).1 := by
        rw [Nat.mul_comm (rkPair n k C).2 sden]
        exact hw
      exact_mod_cast h2

theorem ffJ_eqT (hn : 5 ≤ n) (k : Mod) {T JL G : List Tab} {D : List (List Tab)}
    (hT : subOK n T = true) (hEA : chkEA n T D = true) (hJok : subOK n JL = true)
    (hcl : Subgroup.closure {x : Gp n | tab x ∈ G} = subOf n JL)
    (hgen : ∀ g ∈ G, ∃ C ∈ D, offOK n k D C = true ∧ g ∈ C)
    (hJ : ∀ C ∈ D, offOK n k D C = true → ∀ t ∈ C, t ∈ JL) :
    ffJ ((subOf n T).map (Mod.act n k)) = (subOf n JL).map (Mod.act n k) := by
  obtain ⟨-, hmem, -⟩ := chkEA_spec hEA
  apply le_antisymm
  · unfold ffJ
    refine iSup₂_le fun A' hA' => ?_
    obtain ⟨A, hAT, hAmap, hAoff⟩ := exists_pullback_T k hA'
    obtain ⟨hcomm, hsq⟩ := hAoff.comm_sq hn
    obtain ⟨C, hC, hCok, hAC⟩ := exists_mem_D hT hEA A (fun x hx => (mem_subOf hT).1 (hAT hx))
      hcomm hsq
    have hAeq : A = subOf n C := subOf_eq hCok hAC
    have hoff : offOK n k D C = true := by
      rw [← isOffG_iff_offOK hn k hT hEA hC, ← hAeq]
      exact hAoff
    rw [← hAmap]
    refine Subgroup.map_mono ?_
    rw [hAeq]
    intro x hx
    rw [mem_subOf hCok] at hx
    rw [mem_subOf hJok]
    exact hJ C hC hoff _ hx
  · rw [← hcl, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨C, hC, hoff, hxC⟩ := hgen _ hx
    obtain ⟨hCok, hCT, -, -⟩ := hmem C hC
    have hOffG := (isOffG_iff_offOK hn k hT hEA hC).2 hoff
    have hle : (subOf n C).map (Mod.act n k) ≤ (subOf n T).map (Mod.act n k) := by
      refine Subgroup.map_mono ?_
      intro y hy
      rw [mem_subOf hCok] at hy
      rw [mem_subOf hT]
      exact hCT _ hy
    have hTo : IsFFStarOffender ((subOf n T).map (Mod.act n k))
        ((subOf n C).map (Mod.act n k)) := ⟨hle, hOffG.2⟩
    have hxmem : Mod.act n k x ∈ (subOf n C).map (Mod.act n k) :=
      Subgroup.mem_map_of_mem _ ((mem_subOf hCok).2 hxC)
    have hsub : (subOf n C).map (Mod.act n k) ≤ ffJ ((subOf n T).map (Mod.act n k)) := by
      unfold ffJ
      exact le_iSup₂_of_le ((subOf n C).map (Mod.act n k)) hTo le_rfl
    exact hsub hxmem

theorem strong_iffT (hn : 5 ≤ n) (k : Mod) {T : List Tab} {D : List (List Tab)}
    (hT : subOK n T = true) (hEA : chkEA n T D = true)
    (hstrong : ∀ C ∈ D, offOK n k D C = true → cntF n k [idT n] < Fval n k C →
      subOf n C = Dsub n)
    (hDoff : IsOffG n k (Dsub n)) (hDstrong : rAV ((Dsub n).map (Mod.act n k)) < 1)
    {A : Subgroup (Gp n)} (hAT : A ≤ subOf n T) :
    IsStrongFFStarOffender ((subOf n T).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
      A = Dsub n := by
  constructor
  · rintro ⟨hoff, hlt⟩
    have hA : IsOffG n k A := ⟨hoff.1.trans (Subgroup.map_mono le_top), hoff.2⟩
    obtain ⟨hcomm, hsq⟩ := hA.comm_sq hn
    obtain ⟨C, hC, hCok, hAC⟩ := exists_mem_D hT hEA A (fun x hx => (mem_subOf hT).1 (hAT hx))
      hcomm hsq
    have hAeq : A = subOf n C := subOf_eq hCok hAC
    have hoffC : offOK n k D C = true := by
      rw [← isOffG_iff_offOK hn k hT hEA hC, ← hAeq]
      exact hA
    have hlt' := (rAV_lt_one_iff (V_sq' k) hoff.isA2).1 hlt
    have e1 := fval_eq hn k hCok (K := A) hAC
    have e2 := cntF_id (n := n) k
    have hlt2 : cntF n k [idT n] < Fval n k C := by
      rw [← e1, ← e2]
      exact Nat.mul_lt_mul_of_pos_right hlt' (cN_pos k)
    rw [hAeq]
    exact hstrong C hC hoffC hlt2
  · rintro rfl
    exact ⟨⟨Subgroup.map_mono hAT, hDoff.2⟩, hDstrong⟩

theorem rank_E8T (hn : 5 ≤ n) (k : Mod) {T : List Tab} {D : List (List Tab)}
    {S : Sylow 2 (Gp n)} (hS : (S : Subgroup (Gp n)) = subOf n T) (hT : subOK n T = true)
    (hEA : chkEA n T D = true) (hE8 : ∀ C ∈ D, isE8T n C = true → rankOK n k C 3 3 = true)
    (hn8 : n = 8) {A : Subgroup (Gp n)} (hA : A ∈ Rset n) :
    rkIdx (fixV (A.map (Mod.act n k))) = 3 := by
  obtain ⟨hL, hcomm, hsq, hcard, hreg⟩ := hA
  obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hsq)
  have hK := Rset_cj ⟨hL, hcomm, hsq, hcard, hreg⟩ γ
  obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hT hEA (cj γ A)
    (fun x hx => by
      have := hγ hx
      rw [hS] at this
      exact (mem_subOf hT).1 this) hK.2.1 hK.2.2.1
  have hE : isE8T n C = true := isE8T_of_mem_Rset hCok hn8 hK hKC
  have hrank := hE8 C hC hE
  simp only [rankOK, Bool.and_eq_true, beq_iff_eq] at hrank
  have h3 := (rank_data hn k hCok hrank.1 hrank.2).2.1
  have hKeq : cj γ A = subOf n C := subOf_eq hCok hKC
  have h4 := rkIdx_fixV_map_cj k γ⁻¹ (cj γ A)
  rw [cj_inv_cj] at h4
  rw [h4, hKeq]
  exact h3

theorem t12_sq (hn : 4 ≤ n) : (ti n 0 * ti n 1) * (ti n 0 * ti n 1) = 1 := by
  unfold ti swapN
  rw [dif_pos (by omega), dif_pos (by omega)]
  ext i
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem isConj_iff_dt {T : List Tab} (hn : 4 ≤ n)
    (hsupp : suppCardT (CFSG.Quasithin.B3.t12 n) = 4)
    (hdt : ∀ t ∈ T, mulT t t = idT n → suppCardT t = 4 →
      ∃ g : Tab, isTab n g = true ∧ cjT g (CFSG.Quasithin.B3.t12 n) = t)
    {x : Gp n} (hx : tab x ∈ T) :
    IsConj (ti n 0 * ti n 1) x ↔ mulT (tab x) (tab x) = idT n ∧ suppCardT (tab x) = 4 := by
  have ht12 : CFSG.Quasithin.B3.t12 n = tab (ti n 0 * ti n 1) := rfl
  have hsupp' : (ti n 0 * ti n 1).support.card = 4 := by
    rw [← suppCardT_tab, ← ht12]
    exact hsupp
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine ⟨?_, ?_⟩
    · rw [← tab_mul, ← tab_one]
      congr 1
      rw [← hc]
      calc c * (ti n 0 * ti n 1) * c⁻¹ * (c * (ti n 0 * ti n 1) * c⁻¹)
          = c * ((ti n 0 * ti n 1) * (ti n 0 * ti n 1)) * c⁻¹ := by simp [mul_assoc]
        _ = 1 := by rw [t12_sq hn]; simp
    · rw [suppCardT_tab, ← hc, Equiv.Perm.card_support_conj]
      exact hsupp'
  · rintro ⟨hsq, hs⟩
    obtain ⟨g, hg, hcj⟩ := hdt _ hx hsq hs
    obtain ⟨γ, rfl⟩ := exists_tab_eq hg
    rw [ht12, cjT_tab] at hcj
    exact isConj_iff.2 ⟨γ, tab_injective hcj⟩

theorem DL_mem (d : Dat) {j : ℕ} (hj : j < d.nD) : d.DL j ∈ d.DD :=
  List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem mem_DD (d : Dat) {L : List Tab} (h : L ∈ d.DD) : ∃ j < d.nD, L = d.DL j := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  exact ⟨j, List.mem_range.1 hj, rfl⟩

theorem base_facts (d : Dat) (hd : Ok d) :
    subOK d.n d.TL = true ∧ (∃ S : Sylow 2 (Gp d.n), (S : Subgroup (Gp d.n)) = subOf d.n d.TL) ∧
    chkEA d.n d.TL d.DD = true ∧ (∀ L ∈ d.DD, subOK d.n L = true) ∧
    (∀ j < d.nD, Subgroup.closure {x : Gp d.n | tab x ∈ d.bas j} = subOf d.n (d.DL j)) ∧
    (∀ j < d.nD, ∀ g ∈ d.bas j, g ∈ d.DL j) := by
  obtain ⟨hTs, hlen, hf, hm⟩ := chkTM_sound d hd.n8 hd.tm
  obtain ⟨hD, hb⟩ := chkEAM_sound d hd.n8 hd.bp hd.tm hd.ea hd.named
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  have hsubD : ∀ L ∈ d.DD, subOK d.n L = true := fun L hL => (hmem L hL).1
  refine ⟨hTs, exists_sylow_T hTs hlen hf hm, hD, hsubD, fun j hj => ?_, fun j hj => (hb j hj).1⟩
  obtain ⟨hgs, -, S, hch, hSL⟩ := hb j hj
  exact closure_eq_of_chain (hsubD _ (DL_mem d hj)) hch (fun g hg => (hSL g).2 (hgs g hg)) hSL

theorem named_facts (d : Dat) (hd : Ok d) :
    (∀ i < d.n / 2, d.ix i < d.nD ∧ Am d.n (i + 1) = subOf d.n (d.DL (d.ix i))) ∧
    (d.ix (d.n / 2) < d.nD ∧ A0 d.n = subOf d.n (d.DL (d.ix (d.n / 2)))) ∧
    (d.ix (d.n / 2 + 1) < d.nD ∧
      Dsub d.n ⊓ alternatingGroup (Fin d.n) = subOf d.n (d.DL (d.ix (d.n / 2 + 1)))) ∧
    (d.ix (d.n / 2 - 1) < d.nD ∧ Dsub d.n = subOf d.n (d.DL (d.ix (d.n / 2 - 1)))) := by
  obtain ⟨-, -, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, S0, hc0, hg0, hS0⟩, ⟨hl, hev⟩, -, -⟩ :=
    chkNamedM_sound d hd.n5 hd.n8 hd.bp hd.tm hd.ea hd.named hd.amT hd.a0T
  have hAm' : ∀ i < d.n / 2, d.ix i < d.nD ∧ Am d.n (i + 1) = subOf d.n (d.DL (d.ix i)) := by
    intro i hi
    obtain ⟨hj, S, hc, hg, hS⟩ := hAm i hi
    refine ⟨hj, ?_⟩
    rw [Am, ← closure_map_tab]
    exact closure_eq_of_chain (hsubD _ (DL_mem d hj)) hc hg hS
  have h5 := hd.n5
  have hdc : d.n / 2 - 1 < d.n / 2 := by omega
  obtain ⟨hdj, hdeq⟩ := hAm' _ hdc
  have hDs : Dsub d.n = subOf d.n (d.DL (d.ix (d.n / 2 - 1))) := by
    rw [← hdeq]
    unfold Dsub
    congr 1
    omega
  refine ⟨hAm', ⟨h0, ?_⟩, ⟨hl, ?_⟩, hdj, hDs⟩
  · rw [A0, ← closure_map_tab]
    exact closure_eq_of_chain (hsubD _ (DL_mem d h0)) hc0 hg0 hS0
  · have hDc := hsubD _ (DL_mem d hdj)
    have hDl := hsubD _ (DL_mem d hl)
    ext x
    rw [Subgroup.mem_inf, hDs, mem_subOf hDc, mem_alternatingGroup_iff, mem_subOf hDl, hev]

theorem mod_ok (d : Dat) (hd : Ok d) (k : Mod) (hM : chkModM d (mIdx k) = true) :
    ModOK d k := by
  obtain ⟨-, -, -, hsubD, hcl, hbL⟩ := base_facts d hd
  have hfv := chkModM_fv d k hd.n5 hd.n8 hd.bp hd.tm hd.ea hM
  obtain ⟨-, hb⟩ := chkEAM_sound d hd.n8 hd.bp hd.tm hd.ea hd.named
  refine chkModM_sound d k hd.n5 hd.n8 hd.bp hd.tm hd.ea hd.named hM fun j hj => ?_
  rw [hfv j hj, Fval, (hb j hj).2.1,
    cntF_basis k (hsubD _ (DL_mem d hj)) (hcl j hj) (hbL j hj)]

theorem offenders (d : Dat) (hd : Ok d) (k : Mod) (hM : chkModM d (mIdx k) = true) :
    ∀ A : Subgroup (Gp d.n), IsOffG d.n k A ↔
      ∃ L ∈ d.DD, RepL d (caseOf d.n (mIdx k)) L ∧ ∃ γ : Gp d.n, A = cj γ (subOf d.n L) := by
  obtain ⟨hTs, ⟨S, hS⟩, hD, hsubD, hcl, -⟩ := base_facts d hd
  have hmo := mod_ok d hd k hM
  refine classificationP hd.n5 k hS hTs hD (fun L hL hP => ?_) (fun K hK hoff => ?_)
  · obtain ⟨j, hj, rfl⟩ := mem_DD d hL
    exact hmo.rep_off j hj hP
  · obtain ⟨j, hj, rfl⟩ := mem_DD d hK
    obtain ⟨r, hr, hP, g, hg, hgb, hlen⟩ := hmo.cover j hj hoff
    obtain ⟨γ, hγ⟩ := cj_of_basis (hsubD _ (DL_mem d hr)) (hsubD _ (DL_mem d hj)) (hcl r hr) hg
      hgb hlen
    exact ⟨d.DL r, DL_mem d hr, hP, γ, hγ⟩

theorem repA_iff (d : Dat) (hd : Ok d) {L : List Tab} (hL : L ∈ d.DD) :
    RepL d 0 L ↔ ∃ i < d.n / 2, subOf d.n L = Am d.n (i + 1) := by
  obtain ⟨-, -, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨hAm, -⟩ := named_facts d hd
  unfold RepL
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨h0, -⟩)
    · refine ⟨i, hi, ?_⟩
      rw [(hAm i hi).2]
      exact subOf_eq_of_iff (hsubD L hL) (hsubD _ (DL_mem d (hAm i hi).1)) h
    · exact absurd rfl h0
  · rintro ⟨i, hi, h⟩
    refine Or.inl ⟨i, hi, ?_⟩
    rw [(hAm i hi).2] at h
    exact (subOf_eq_iff (hsubD L hL) (hsubD _ (DL_mem d (hAm i hi).1))).1 h

theorem repB_iff (d : Dat) (hd : Ok d) {c : ℕ} (hc : c ≠ 0) {L : List Tab} (hL : L ∈ d.DD) :
    RepL d c L ↔ (∃ i < d.n / 2, subOf d.n L = Am d.n (i + 1)) ∨
      subOf d.n L = Dsub d.n ⊓ alternatingGroup (Fin d.n) ∨ subOf d.n L = A0 d.n ∨
      (subOf d.n L ≤ Dsub d.n ∧ Nat.card (Dsub d.n) = 2 * Nat.card (subOf d.n L) ∧
        subOf d.n L ≠ Dsub d.n ⊓ alternatingGroup (Fin d.n)) ∨ (c = 2 ∧ isE8T d.n L = true) := by
  obtain ⟨-, -, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, hA0⟩, ⟨hl, hDL⟩, hdj, hDs⟩ := named_facts d hd
  have hLok := hsubD L hL
  have hDc := hsubD _ (DL_mem d hdj)
  have hDl := hsubD _ (DL_mem d hl)
  have hA0ok := hsubD _ (DL_mem d h0)
  have e1 : (∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2 + 1))) ↔
      subOf d.n L = Dsub d.n ⊓ alternatingGroup (Fin d.n) := by
    rw [hDL, subOf_eq_iff hLok hDl]
  have e2 : (∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2))) ↔ subOf d.n L = A0 d.n := by
    rw [hA0, subOf_eq_iff hLok hA0ok]
  have e3 : ((∀ t ∈ L, t ∈ d.DL (d.ix (d.n / 2 - 1))) ∧
      2 * L.length = (d.DL (d.ix (d.n / 2 - 1))).length ∧
      ¬ ∀ t, t ∈ L ↔ t ∈ d.DL (d.ix (d.n / 2 + 1))) ↔
      (subOf d.n L ≤ Dsub d.n ∧ Nat.card (Dsub d.n) = 2 * Nat.card (subOf d.n L) ∧
        subOf d.n L ≠ Dsub d.n ⊓ alternatingGroup (Fin d.n)) := by
    refine and_congr ?_ (and_congr ?_ (not_congr e1))
    · rw [hDs]
      exact (subOf_le_iff hLok hDc).symm
    · rw [hDs, card_subOf hDc, card_subOf hLok]
      exact eq_comm
  have e4 : (∃ i < d.n / 2, ∀ t, t ∈ L ↔ t ∈ d.DL (d.ix i)) ↔
      ∃ i < d.n / 2, subOf d.n L = Am d.n (i + 1) := by
    refine exists_congr fun i => ⟨fun ⟨hi, h⟩ => ⟨hi, ?_⟩, fun ⟨hi, h⟩ => ⟨hi, ?_⟩⟩
    · rw [(hAm i hi).2]
      exact subOf_eq_of_iff hLok (hsubD _ (DL_mem d (hAm i hi).1)) h
    · rw [(hAm i hi).2] at h
      exact (subOf_eq_iff hLok (hsubD _ (DL_mem d (hAm i hi).1))).1 h
  unfold RepL
  constructor
  · rintro (h | ⟨-, h1 | h2 | h3 | h4⟩)
    · exact Or.inl (e4.1 h)
    · exact Or.inr (Or.inl (e1.1 h1))
    · exact Or.inr (Or.inr (Or.inl (e2.1 h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (e3.1 h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  · rintro (h | h1 | h2 | h3 | h4)
    · exact Or.inl (e4.2 h)
    · exact Or.inr ⟨hc, Or.inl (e1.2 h1)⟩
    · exact Or.inr ⟨hc, Or.inr (Or.inl (e2.2 h2))⟩
    · exact Or.inr ⟨hc, Or.inr (Or.inr (Or.inl (e3.2 h3)))⟩
    · exact Or.inr ⟨hc, Or.inr (Or.inr (Or.inr h4))⟩

theorem le_T (d : Dat) (hd : Ok d) {S : Sylow 2 (Gp d.n)}
    (hS : (S : Subgroup (Gp d.n)) = subOf d.n d.TL) {L : List Tab} (hL : L ∈ d.DD) :
    subOf d.n L ≤ S := by
  obtain ⟨hTs, -, hD, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  intro x hx
  rw [hS, mem_subOf hTs]
  exact (hmem L hL).2.1 _ ((mem_subOf (hsubD L hL)).1 hx)

theorem ffJ_mod (d : Dat) (hd : Ok d) (k : Mod) (hM : chkModM d (mIdx k) = true) :
    ∃ JL : List Tab, subOK d.n JL = true ∧
      ffJ ((subOf d.n d.TL).map (Mod.act d.n k)) = (subOf d.n JL).map (Mod.act d.n k) ∧
      (caseOf d.n (mIdx k) = 0 → ∀ t, t ∈ JL ↔ t ∈ d.DL (d.ix (d.n / 2 - 1))) ∧
      (caseOf d.n (mIdx k) = 2 → ∀ t, t ∈ JL ↔ t ∈ d.TL) ∧
      (caseOf d.n (mIdx k) = 1 → ∃ G5 S5 : List Tab, chainOK G5 (idT d.n) [] S5 = true ∧
        (∀ g ∈ G5, g ∈ S5) ∧ (∀ t, t ∈ S5 ↔ t ∈ JL) ∧
        (∀ g ∈ G5, g ∈ d.DL (d.ix (d.n / 2 - 1)) ∨
          (g ∈ d.TL ∧ mulT g g = idT d.n ∧ suppCardT g = 4)) ∧
        (∀ t ∈ d.DL (d.ix (d.n / 2 - 1)), t ∈ JL) ∧
        ∀ t ∈ d.TL, mulT t t = idT d.n → suppCardT t = 4 → t ∈ JL) := by
  obtain ⟨hTs, -, hD, -, -, -⟩ := base_facts d hd
  obtain ⟨JL, G, S', hJok, hch, hGS, hSJ, hgen, hJ, hJ0, hJ2, hJ1⟩ := (mod_ok d hd k hM).J
  refine ⟨JL, hJok, ffJ_eqT hd.n5 k hTs hD hJok (closure_eq_of_chain hJok hch hGS hSJ)
    (fun g hg => ?_) (fun C hC hoffC => ?_), hJ0, hJ2, hJ1⟩
  · obtain ⟨j, hj, h1, h2⟩ := hgen g hg
    exact ⟨_, DL_mem d hj, h1, h2⟩
  · obtain ⟨j, hj, rfl⟩ := mem_DD d hC
    exact hJ j hj hoffC

theorem spec_caseAM (d : Dat) {n : ℕ} (hdn : d.n = n) (hd : Ok d) (k : Mod)
    (hc : caseOf n (mIdx k) = 0) (hM : chkModM d (mIdx k) = true) :
    (∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∧
    (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
      rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) = i + 1) ∧
    (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
      ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (Dsub n).map (Mod.act n k)) ∧
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((1 : ℚ) : WithTop ℚ) := by
  subst hdn
  have hn := hd.n5
  obtain ⟨-, ⟨S, hS⟩, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, hA0⟩, -, hdj, hDs⟩ := named_facts d hd
  have hmo := mod_ok d hd k hM
  have hcls := offenders d hd k hM
  rw [hc] at hcls
  have hoff : ∀ A : Subgroup (Gp d.n), IsOffG d.n k A ↔
      ∃ i < d.n / 2, A ∈ conjClass (Am d.n (i + 1)) := by
    intro A
    rw [hcls A]
    constructor
    · rintro ⟨L, hL, hP, γ, rfl⟩
      obtain ⟨i, hi, hLi⟩ := (repA_iff d hd hL).1 hP
      exact ⟨i, hi, mem_conjClass.2 ⟨γ, by rw [hLi]⟩⟩
    · rintro ⟨i, hi, hA⟩
      obtain ⟨γ, rfl⟩ := mem_conjClass.1 hA
      refine ⟨d.DL (d.ix i), DL_mem d (hAm i hi).1,
        (repA_iff d hd (DL_mem d (hAm i hi).1)).2 ⟨i, hi, (hAm i hi).2.symm⟩, γ, ?_⟩
      rw [(hAm i hi).2]
  refine ⟨hoff, fun i hi => ?_, ⟨S, fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · have hr := hmo.ranks0 hc i hi
    simp only [rankOK, Bool.and_eq_true, beq_iff_eq] at hr
    have := rank_data hn k (hsubD _ (DL_mem d (hAm i hi).1)) hr.1 hr.2
    rw [(hAm i hi).2]
    exact ⟨this.1, this.2.1⟩
  · rw [(hAm i hi).2]
    exact le_T d hd hS (DL_mem d (hAm i hi).1)
  · rw [hA0]
    exact le_T d hd hS (DL_mem d h0)
  · obtain ⟨JL, hJok, hJ, hJ0, -, -⟩ := ffJ_mod d hd k hM
    rw [hS, hJ, hDs, subOf_eq_of_iff hJok (hsubD _ (DL_mem d hdj)) (hJ0 hc)]
  · have hq := hmo.q
    rw [hc] at hq
    simp only [↓reduceIte] at hq
    obtain ⟨hrows, j, hj, hP, hw⟩ := hq
    have := q_valueD hn k (P := RepL d 0) (snum := 1) (sden := 1) hcls hsubD
      (fun C hC hP => by
        obtain ⟨j, hj, rfl⟩ := mem_DD d hC
        exact hrows j hj hP)
      ⟨_, DL_mem d hj, hP, hw⟩ (by norm_num) le_rfl
    simpa using this

theorem offenders_B (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) ≠ 0)
    (hM : chkModM d (mIdx k) = true) :
    ∀ A : Subgroup (Gp d.n), IsOffG d.n k A ↔
      (A ∈ conjClass (Dsub d.n ⊓ alternatingGroup (Fin d.n)) ∨ A ∈ conjClass (A0 d.n) ∨
        (∃ i < d.n / 2, A ∈ conjClass (Am d.n (i + 1))) ∨ A ∈ Hset d.n) ∨
      (caseOf d.n (mIdx k) = 2 ∧ d.n = 8 ∧ A ∈ Rset d.n) := by
  obtain ⟨hTs, ⟨S, hS⟩, hD, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨-, hmem, -⟩ := chkEA_spec hD
  obtain ⟨hAm, ⟨h0, hA0⟩, ⟨hl, hDL⟩, hdj, hDs⟩ := named_facts d hd
  have hcls := offenders d hd k hM
  have hrep : ∀ {B : Subgroup (Gp d.n)} {L : List Tab}, L ∈ d.DD →
      RepL d (caseOf d.n (mIdx k)) L → subOf d.n L = B → ∀ γ : Gp d.n,
      ∃ L ∈ d.DD, RepL d (caseOf d.n (mIdx k)) L ∧ ∃ γ' : Gp d.n, cj γ B = cj γ' (subOf d.n L) :=
    fun hL hP hB γ => ⟨_, hL, hP, γ, by rw [hB]⟩
  intro A
  rw [hcls A]
  constructor
  · rintro ⟨L, hL, hP, γ, rfl⟩
    obtain ⟨hLok, -, hLc, hLs⟩ := hmem L hL
    rcases (repB_iff d hd hc hL).1 hP with ⟨i, hi, h⟩ | h | h | ⟨h1, h2, h3⟩ | ⟨h2', hE8⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨i, hi, mem_conjClass.2 ⟨γ, by rw [h]⟩⟩)))
    · exact Or.inl (Or.inl (mem_conjClass.2 ⟨γ, by rw [h]⟩))
    · exact Or.inl (Or.inr (Or.inl (mem_conjClass.2 ⟨γ, by rw [h]⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨γ, subOf d.n L, h1, h2, h3, rfl⟩)))
    · have hn8 : d.n = 8 := by
        simp only [isE8T, Bool.and_eq_true, beq_iff_eq] at hE8
        exact hE8.1.1.1
      exact Or.inr ⟨h2', hn8, Rset_cj (isE8T_mem_Rset hLok hLc hLs hE8) γ⟩
  · rintro ((h | h | ⟨i, hi, h⟩ | ⟨γ, H, hH, hcard, hne, rfl⟩) | ⟨h2, hn8, hR⟩)
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 h
      exact hrep (DL_mem d hl) ((repB_iff d hd hc (DL_mem d hl)).2 (Or.inr (Or.inl hDL.symm)))
        hDL.symm γ
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 h
      exact hrep (DL_mem d h0)
        ((repB_iff d hd hc (DL_mem d h0)).2 (Or.inr (Or.inr (Or.inl hA0.symm)))) hA0.symm γ
    · obtain ⟨γ, rfl⟩ := mem_conjClass.1 h
      have hj := DL_mem d (hAm i hi).1
      exact hrep hj ((repB_iff d hd hc hj).2 (Or.inl ⟨i, hi, (hAm i hi).2.symm⟩))
        (hAm i hi).2.symm γ
    · have hDc := hsubD _ (DL_mem d hdj)
      obtain ⟨-, hDT, hDcomm, hDsq⟩ := hmem _ (DL_mem d hdj)
      have hHD : ∀ x ∈ H, x ∈ subOf d.n (d.DL (d.ix (d.n / 2 - 1))) := fun x hx => by
        rw [← hDs]
        exact hH hx
      obtain ⟨C, hC, hCok, hHC⟩ := exists_mem_D hTs hD H
        (fun x hx => hDT _ ((mem_subOf hDc).1 (hHD x hx)))
        (fun a ha b hb => subOf_comm hDc hDcomm a (hHD a ha) b (hHD b hb))
        (fun a ha => subOf_sq hDc hDsq a (hHD a ha))
      have hHeq : subOf d.n C = H := (subOf_eq hCok hHC).symm
      refine hrep hC ((repB_iff d hd hc hC).2 (Or.inr (Or.inr (Or.inr (Or.inl ?_))))) hHeq γ
      rw [hHeq]
      exact ⟨hH, hcard, hne⟩
    · obtain ⟨γ, hγ⟩ := exists_conj_le_sylow S A (isPGroup_of_sq hR.2.2.1)
      have hK := Rset_cj hR γ
      obtain ⟨C, hC, hCok, hKC⟩ := exists_mem_D hTs hD (cj γ A)
        (fun x hx => by
          have := hγ hx
          rw [hS] at this
          exact (mem_subOf hTs).1 this) hK.2.1 hK.2.2.1
      have hE8 : isE8T d.n C = true := isE8T_of_mem_Rset hCok hn8 hK hKC
      refine ⟨C, hC, (repB_iff d hd hc hC).2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, hE8⟩)))),
        γ⁻¹, ?_⟩
      rw [← subOf_eq hCok hKC, cj_inv_cj]

theorem ranks_BM (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) ≠ 0)
    (hM : chkModM d (mIdx k) = true) :
    (∀ i < d.n / 2, rk (Am d.n (i + 1)) = i + 1 ∧
      rkIdx (fixV ((Am d.n (i + 1)).map (Mod.act d.n k))) =
        if i + 1 = d.n / 2 then d.n / 2 - 1 else i + 1) ∧
    (rk (A0 d.n) = d.n / 2 ∧ rkIdx (fixV ((A0 d.n).map (Mod.act d.n k))) = d.n / 2) ∧
    rAV ((Dsub d.n).map (Mod.act d.n k)) < 1 := by
  have hn := hd.n5
  obtain ⟨-, -, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, hA0⟩, -, -, -⟩ := named_facts d hd
  obtain ⟨hR1, hR2⟩ := (mod_ok d hd k hM).ranksB hc
  have hrk : ∀ i < d.n / 2, rk (Am d.n (i + 1)) = i + 1 ∧
      rkIdx (fixV ((Am d.n (i + 1)).map (Mod.act d.n k))) =
        (if i + 1 = d.n / 2 then d.n / 2 - 1 else i + 1) ∧
      rAV ((Am d.n (i + 1)).map (Mod.act d.n k)) =
        ((if i + 1 = d.n / 2 then d.n / 2 - 1 else i + 1 : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ) := by
    intro i hi
    have hr := hR1 i hi
    simp only [rankOK, Bool.and_eq_true, beq_iff_eq] at hr
    rw [(hAm i hi).2]
    exact rank_data hn k (hsubD _ (DL_mem d (hAm i hi).1)) hr.1 hr.2
  refine ⟨fun i hi => ⟨(hrk i hi).1, (hrk i hi).2.1⟩, ?_, ?_⟩
  · have hr := hR2
    simp only [rankOK, Bool.and_eq_true, beq_iff_eq] at hr
    rw [hA0]
    have := rank_data hn k (hsubD _ (DL_mem d h0)) hr.1 hr.2
    exact ⟨this.1, this.2.1⟩
  · have hj : d.n / 2 - 1 < d.n / 2 := by omega
    have h1 := (hrk _ hj).2.2
    have he : d.n / 2 - 1 + 1 = d.n / 2 := by omega
    rw [if_pos he] at h1
    have hD : Dsub d.n = Am d.n (d.n / 2 - 1 + 1) := by
      unfold Dsub
      rw [he]
    rw [hD, h1]
    have hpos : (0 : ℚ) < ((d.n / 2 - 1 + 1 : ℕ) : ℚ) := by positivity
    rw [div_lt_one hpos]
    exact_mod_cast Nat.lt_succ_self _

theorem Dsub_off (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) ≠ 0)
    (hM : chkModM d (mIdx k) = true) : IsOffG d.n k (Dsub d.n) := by
  have hn := hd.n5
  refine (offenders_B d hd k hc hM _).2
    (Or.inl (Or.inr (Or.inr (Or.inl ⟨d.n / 2 - 1, by omega, mem_conjClass.2 ⟨1, ?_⟩⟩))))
  rw [cj_one]
  unfold Dsub
  congr 1
  omega

theorem strong_BM (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) ≠ 0)
    (hM : chkModM d (mIdx k) = true) {A : Subgroup (Gp d.n)} (hAT : A ≤ subOf d.n d.TL) :
    IsStrongFFStarOffender ((subOf d.n d.TL).map (Mod.act d.n k)) (A.map (Mod.act d.n k)) ↔
      A = Dsub d.n := by
  obtain ⟨hTs, -, hD, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨-, -, -, hdj, hDs⟩ := named_facts d hd
  refine strong_iffT hd.n5 k hTs hD (fun C hC hoffC hlt => ?_) (Dsub_off d hd k hc hM)
    (ranks_BM d hd k hc hM).2.2 hAT
  obtain ⟨j, hj, rfl⟩ := mem_DD d hC
  rw [hDs]
  exact subOf_eq_of_iff (hsubD _ hC) (hsubD _ (DL_mem d hdj))
    (((mod_ok d hd k hM).strong hc j hj hoffC).1 hlt)

theorem q_BM (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) ≠ 0)
    (hM : chkModM d (mIdx k) = true) :
    qOf ((⊤ : Subgroup (Gp d.n)).map (Mod.act d.n k)) =
      ((((d.n : ℚ) - 2) / d.n : ℚ) : WithTop ℚ) := by
  have hn := hd.n5
  obtain ⟨-, -, -, hsubD, -, -⟩ := base_facts d hd
  have hq := (mod_ok d hd k hM).q
  simp only [hc, ↓reduceIte] at hq
  obtain ⟨hrows, j, hj, hP, hw⟩ := hq
  have := q_valueD hn k (P := RepL d (caseOf d.n (mIdx k))) (snum := d.n - 2) (sden := d.n)
    (offenders d hd k hM) hsubD
    (fun C hC hP => by
      obtain ⟨j, hj, rfl⟩ := mem_DD d hC
      exact hrows j hj hP)
    ⟨_, DL_mem d hj, hP, hw⟩ (by omega) (by omega)
  rw [Nat.cast_sub (by omega : 2 ≤ d.n)] at this
  simpa using this

theorem J_5M (d : Dat) (hd : Ok d) (k : Mod) (hc : caseOf d.n (mIdx k) = 1)
    (hM : chkModM d (mIdx k) = true) :
    ffJ ((subOf d.n d.TL).map (Mod.act d.n k)) =
      (Dsub d.n ⊔ Subgroup.closure
        {x : Gp d.n | x ∈ subOf d.n d.TL ∧ IsConj (ti d.n 0 * ti d.n 1) x}).map
          (Mod.act d.n k) := by
  have hn := hd.n5
  obtain ⟨hTs, -, -, hsubD, -, -⟩ := base_facts d hd
  obtain ⟨-, -, -, hdj, hDs⟩ := named_facts d hd
  obtain ⟨-, -, -, hsupp, hdt⟩ :=
    chkNamedM_sound d hd.n5 hd.n8 hd.bp hd.tm hd.ea hd.named hd.amT hd.a0T
  obtain ⟨JL, hJok, hJ, -, -, hJ1⟩ := ffJ_mod d hd k hM
  obtain ⟨G5, S5, hch, hGS, hSJ, hG5, hDcJ, hDTJ⟩ := hJ1 hc
  have hDc := hsubD _ (DL_mem d hdj)
  have hcl := closure_eq_of_chain hJok hch hGS hSJ
  have hconj : ∀ x : Gp d.n, x ∈ subOf d.n d.TL → (IsConj (ti d.n 0 * ti d.n 1) x ↔
      mulT (tab x) (tab x) = idT d.n ∧ suppCardT (tab x) = 4) :=
    fun x hx => isConj_iff_dt (by omega) hsupp hdt ((mem_subOf hTs).1 hx)
  rw [hJ]
  refine congrArg (Subgroup.map (Mod.act d.n k)) (le_antisymm ?_ ?_)
  · rw [← hcl, Subgroup.closure_le]
    intro x hx
    rcases hG5 _ hx with h | ⟨hT, hsq, hs⟩
    · refine Subgroup.mem_sup_left ?_
      rw [hDs, mem_subOf hDc]
      exact h
    · have hxT : x ∈ subOf d.n d.TL := (mem_subOf hTs).2 hT
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hxT, (hconj x hxT).2 ⟨hsq, hs⟩⟩)
  · refine sup_le ?_ ?_
    · intro x hx
      rw [hDs, mem_subOf hDc] at hx
      rw [mem_subOf hJok]
      exact hDcJ _ hx
    · rw [Subgroup.closure_le]
      rintro x ⟨hxT, hcj⟩
      obtain ⟨hsq, hs⟩ := (hconj x hxT).1 hcj
      rw [SetLike.mem_coe, mem_subOf hJok]
      exact hDTJ _ ((mem_subOf hTs).1 hxT) hsq hs

theorem spec_caseB5M (d : Dat) {n : ℕ} (hdn : d.n = n) (hd : Ok d) (k : Mod)
    (hc : caseOf n (mIdx k) = 1) (hM : chkModM d (mIdx k) = true) :
    (∀ A : Subgroup (Gp n), IsOffG n k A ↔
      A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
        (∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∨ A ∈ Hset n) ∧
    (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
      rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) =
        if i + 1 = n / 2 then n / 2 - 1 else i + 1) ∧
    (rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
    (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
      ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) =
        (Dsub n ⊔ Subgroup.closure
          {x : Gp n | x ∈ (T : Subgroup (Gp n)) ∧ IsConj (ti n 0 * ti n 1) x}).map
            (Mod.act n k) ∧
      ∀ A : Subgroup (Gp n), A ≤ T →
        (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k))
          (A.map (Mod.act n k)) ↔ A = Dsub n)) ∧
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) =
      ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ) := by
  subst hdn
  have hc0 : caseOf d.n (mIdx k) ≠ 0 := by
    rw [hc]
    norm_num
  obtain ⟨-, ⟨S, hS⟩, -, -, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, hA0⟩, -, -, -⟩ := named_facts d hd
  have hoff : ∀ A : Subgroup (Gp d.n), IsOffG d.n k A ↔
      A ∈ conjClass (Dsub d.n ⊓ alternatingGroup (Fin d.n)) ∨ A ∈ conjClass (A0 d.n) ∨
        (∃ i < d.n / 2, A ∈ conjClass (Am d.n (i + 1))) ∨ A ∈ Hset d.n := by
    intro A
    rw [offenders_B d hd k hc0 hM A, hc]
    constructor
    · rintro (h | ⟨h2, -⟩)
      · exact h
      · exact absurd h2 (by norm_num)
    · exact Or.inl
  obtain ⟨hRanksAm, hRanksA0, -⟩ := ranks_BM d hd k hc0 hM
  refine ⟨hoff, hRanksAm, hRanksA0, ⟨S, fun i hi => ?_, ?_, ?_, fun A hAT => ?_⟩,
    q_BM d hd k hc0 hM⟩
  · rw [(hAm i hi).2]
    exact le_T d hd hS (DL_mem d (hAm i hi).1)
  · rw [hA0]
    exact le_T d hd hS (DL_mem d h0)
  · rw [hS]
    exact J_5M d hd k hc hM
  · rw [hS] at hAT ⊢
    exact strong_BM d hd k hc0 hM hAT

theorem spec_caseB6M (d : Dat) {n : ℕ} (hdn : d.n = n) (hd : Ok d) (k : Mod) (hn8 : n = 8)
    (hc : caseOf n (mIdx k) = 2) (hM : chkModM d (mIdx k) = true) :
    (∀ A : Subgroup (Gp n), IsOffG n k A ↔
      A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
        (∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∨ A ∈ Hset n ∨ A ∈ Rset n) ∧
    (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
      rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) =
        if i + 1 = n / 2 then n / 2 - 1 else i + 1) ∧
    (rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
    (∀ A ∈ Rset n, rkIdx (fixV (A.map (Mod.act n k))) = 3) ∧
    (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
      ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (T : Subgroup (Gp n)).map (Mod.act n k) ∧
      ∀ A : Subgroup (Gp n), A ≤ T →
        (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k))
          (A.map (Mod.act n k)) ↔ A = Dsub n)) ∧
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) =
      ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ) := by
  subst hdn
  have hn := hd.n5
  have hc0 : caseOf d.n (mIdx k) ≠ 0 := by
    rw [hc]
    norm_num
  obtain ⟨hTs, ⟨S, hS⟩, hD, -, -, -⟩ := base_facts d hd
  obtain ⟨hAm, ⟨h0, hA0⟩, -, -, -⟩ := named_facts d hd
  have hoff : ∀ A : Subgroup (Gp d.n), IsOffG d.n k A ↔
      A ∈ conjClass (Dsub d.n ⊓ alternatingGroup (Fin d.n)) ∨ A ∈ conjClass (A0 d.n) ∨
        (∃ i < d.n / 2, A ∈ conjClass (Am d.n (i + 1))) ∨ A ∈ Hset d.n ∨ A ∈ Rset d.n := by
    intro A
    rw [offenders_B d hd k hc0 hM A]
    constructor
    · rintro ((h1 | h2 | h3 | h4) | ⟨-, -, h5⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
    · rintro (h1 | h2 | h3 | h4 | h5)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inl h2))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h4)))
      · exact Or.inr ⟨hc, hn8, h5⟩
  obtain ⟨hRanksAm, hRanksA0, -⟩ := ranks_BM d hd k hc0 hM
  refine ⟨hoff, hRanksAm, hRanksA0,
    fun A hA => rank_E8T hn k hS hTs hD (fun C hC hE => ?_) hn8 hA,
    ⟨S, fun i hi => ?_, ?_, ?_, fun A hAT => ?_⟩, q_BM d hd k hc0 hM⟩
  · obtain ⟨j, hj, rfl⟩ := mem_DD d hC
    exact (mod_ok d hd k hM).ranksE8 hc j hj hE
  · rw [(hAm i hi).2]
    exact le_T d hd hS (DL_mem d (hAm i hi).1)
  · rw [hA0]
    exact le_T d hd hS (DL_mem d h0)
  · obtain ⟨JL, hJok, hJ, -, hJ2, -⟩ := ffJ_mod d hd k hM
    rw [hS, hJ, subOf_eq_of_iff hJok hTs (hJ2 hc)]
  · rw [hS] at hAT ⊢
    exact strong_BM d hd k hc0 hM hAT

end CFSG.KC.B3M

end
