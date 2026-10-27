module

public import Certificates.Data.Kernel.SetOrb
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KC.SetOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Fischer CFSG.KC.Bfs

@[expose] noncomputable def codeArr (w len C : Nat) : Array Nat :=
  Array.ofFn (n := len) fun t => pg w (mask w) C t.val

theorem mem_orRec (f : Nat → Nat) (x : Nat) : ∀ len : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor acc (Nat.shiftLeft 1 (f t))) len :
      Nat).testBit x = true ↔ ∃ t < len, f t = x
  | 0 => by simp
  | len + 1 => by
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => Nat.lor acc (Nat.shiftLeft 1 (f t))) len) (Nat.shiftLeft 1 (f len))).testBit x
        = true ↔ _
    rw [show ∀ a b : Nat, Nat.lor a b = a ||| b from fun _ _ => rfl, Nat.testBit_or,
      Bool.or_eq_true, mem_orRec f x len, show ∀ a : Nat, Nat.shiftLeft 1 a = 1 <<< a from
        fun _ => rfl, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (⟨t, ht, e⟩ | e)
      · exact ⟨t, by omega, e⟩
      · exact ⟨len, by omega, e⟩
    · rintro ⟨t, ht, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
      · exact Or.inl ⟨t, h, e⟩
      · subst h
        exact Or.inr e

theorem mem_maskK {w len C x : Nat} :
    (maskK w len C).testBit x = true ↔ ∃ t < len, pg w (mask w) C t = x :=
  mem_orRec (fun t => pg w (mask w) C t) x len

theorem mem_imgK {w len P C x : Nat} :
    (imgK w len P C).testBit x = true ↔ ∃ t < len, pg w (mask w) P (pg w (mask w) C t) = x :=
  mem_orRec (fun t => pg w (mask w) P (pg w (mask w) C t)) x len

theorem mem_eqMaskK {w P Q x : Nat} : ∀ n : Nat,
    (eqMaskK n w P Q).testBit x = true ↔ x < n ∧ pg w (mask w) P x = pg w (mask w) Q x
  | 0 => by simp [eqMaskK]
  | n + 1 => by
    have ih := mem_eqMaskK (w := w) (P := P) (Q := Q) (x := x) n
    change (Bool.rec (motive := fun _ => Nat) (eqMaskK n w P Q)
      (Nat.lor (eqMaskK n w P Q) (Nat.shiftLeft 1 n))
      (Nat.beq (pg w (mask w) P n) (pg w (mask w) Q n))).testBit x = true ↔ _
    cases e : Nat.beq (pg w (mask w) P n) (pg w (mask w) Q n)
    · have hne := Nat.ne_of_beq_eq_false e
      change (eqMaskK n w P Q).testBit x = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact h
        · subst h
          exact absurd h2 hne
    · have he := Nat.eq_of_beq_eq_true e
      change (Nat.lor (eqMaskK n w P Q) (Nat.shiftLeft 1 n)).testBit x = true ↔ _
      rw [show ∀ a b : Nat, Nat.lor a b = a ||| b from fun _ _ => rfl, Nat.testBit_or,
        Bool.or_eq_true, ih, show ∀ a : Nat, Nat.shiftLeft 1 a = 1 <<< a from fun _ => rfl,
        Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨by omega, h2⟩
        · subst h
          exact ⟨by omega, he⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr h.symm

theorem eq_of_pairwise_lt : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | e
      · exact e
      · rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e' | e'
        · exact e'.symm
        · exact absurd (h₁.1 b e') (Nat.lt_asymm (h₂.1 a e))
    subst hab
    refine congrArg (a :: ·) (eq_of_pairwise_lt h₁.2 h₂.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (h₁.1 x hx) (by omega)
      · exact e
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (h₂.1 x hx) (by omega)
      · exact e

theorem band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem unpack_get {n w P p : Nat} (hp : p < n) : (unpack n w P)[p]! = pg w (mask w) P p := by
  rw [unpack, getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]

theorem codeOK_facts {n w len C M : Nat} (h : codeOK n w len C M = true) :
    (∀ t < len, pg w (mask w) C t < n) ∧
      (∀ t, t + 1 < len → pg w (mask w) C t < pg w (mask w) C (t + 1)) ∧ maskK w len C = M := by
  unfold codeOK at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  rw [Orb.allN_iff] at h1 h2
  exact ⟨fun t ht => Nat.blt_eq.mp (h1 t ht), fun t ht => Nat.blt_eq.mp (h2 t (by change t < len - 1; omega)),
    Nat.eq_of_beq_eq_true h3⟩

theorem codeArr_size (w len C : Nat) : (codeArr w len C).size = len := by
  unfold codeArr
  exact Array.size_ofFn

theorem codeArr_get {w len C t : Nat} (ht : t < len) : (codeArr w len C)[t]! = pg w (mask w) C t := by
  unfold codeArr
  rw [getElem!_pos _ t (by simp [ht])]
  simp

theorem mem_codeArr {w len C x : Nat} : x ∈ (codeArr w len C).toList ↔ ∃ t < len, pg w (mask w) C t = x := by
  unfold codeArr
  rw [Array.mem_toList_iff, Array.mem_ofFn]
  exact ⟨fun ⟨t, e⟩ => ⟨t.val, t.isLt, e⟩, fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e⟩⟩

theorem strict_of_succ {f : Nat → Nat} {len : Nat} (h : ∀ t, t + 1 < len → f t < f (t + 1)) :
    ∀ i j, i < j → j < len → f i < f j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (by omega)) (h j hj)
    · subst h'
      exact h i hj

theorem pairwise_codeArr {n w len C M : Nat} (h : codeOK n w len C M = true) :
    (codeArr w len C).toList.Pairwise (· < ·) := by
  obtain ⟨-, h2, -⟩ := codeOK_facts h
  unfold codeArr
  rw [Array.toList_ofFn, List.pairwise_ofFn]
  intro i j hij
  exact strict_of_succ (f := fun t => pg w (mask w) C t) h2 i j hij j.isLt

theorem act_code {n w len P C C' M M' : Nat}
    (hinj : ∀ a < n, ∀ b < n, pg w (mask w) P a = pg w (mask w) P b → a = b)
    (hC : codeOK n w len C M = true) (hC' : codeOK n w len C' M' = true)
    (himg : imgK w len P C = M') :
    ((((codeArr w len C).toList.map fun i => (unpack n w P)[i]!).mergeSort
      fun a b => decide (a ≤ b)).toArray) = codeArr w len C' := by
  obtain ⟨c1, -, -⟩ := codeOK_facts hC
  obtain ⟨-, -, m'⟩ := codeOK_facts hC'
  have hget : ∀ i ∈ (codeArr w len C).toList, (unpack n w P)[i]! = pg w (mask w) P i := by
    intro i hi
    obtain ⟨t, ht, rfl⟩ := mem_codeArr.1 hi
    exact unpack_get (c1 t ht)
  have hl : (codeArr w len C).toList.map (fun i => (unpack n w P)[i]!) =
      (codeArr w len C).toList.map (pg w (mask w) P) := List.map_congr_left hget
  have hnd : ((codeArr w len C).toList.map (pg w (mask w) P)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy e => ?_) (pairwise_codeArr hC).nodup
    obtain ⟨t, ht, rfl⟩ := mem_codeArr.1 hx
    obtain ⟨s, hs, rfl⟩ := mem_codeArr.1 hy
    exact hinj _ (c1 t ht) _ (c1 s hs) e
  rw [hl]
  have hs := pairwise_lt_mergeSort hnd
  have e := eq_of_pairwise_lt hs (pairwise_codeArr hC') fun x => by
    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_map, mem_codeArr, ← mem_maskK, m', ← himg,
      mem_imgK]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨t, ht, rfl⟩ := mem_codeArr.1 hi
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, mem_codeArr.2 ⟨t, ht, rfl⟩, rfl⟩
  rw [e]

theorem filter_code {n w len P Q C M : Nat} (hC : codeOK n w len C M = true)
    (hm : eqMaskK n w P Q = M) :
    ((List.range n).filter fun i => (unpack n w P)[i]! == (unpack n w Q)[i]!).toArray =
      codeArr w len C := by
  obtain ⟨-, -, m⟩ := codeOK_facts hC
  have hs : ((List.range n).filter fun i => (unpack n w P)[i]! == (unpack n w Q)[i]!).Pairwise
      (· < ·) := List.pairwise_lt_range.filter _
  have e := eq_of_pairwise_lt hs (pairwise_codeArr hC) fun x => by
    rw [List.mem_filter, List.mem_range, mem_codeArr, ← mem_maskK, m, ← hm, mem_eqMaskK]
    constructor
    · rintro ⟨h1, h2⟩
      rw [unpack_get h1, unpack_get h1] at h2
      exact ⟨h1, by simpa using h2⟩
    · rintro ⟨h1, h2⟩
      rw [unpack_get h1, unpack_get h1]
      exact ⟨h1, by simpa using h2⟩
  rw [e]

theorem foldl_code (b w C : Nat) : ∀ len : Nat,
    (codeArr w len C).foldl (fun acc i => acc * b + i) 0 = keyK b w len C
  | 0 => rfl
  | len + 1 => by
    rw [← Array.foldl_toList]
    unfold codeArr
    rw [Array.toList_ofFn, List.ofFn_succ_last, List.foldl_append]
    have ih := foldl_code b w C len
    rw [← Array.foldl_toList] at ih
    unfold codeArr at ih
    rw [Array.toList_ofFn] at ih
    simp only [Fin.coe_castSucc, Fin.val_last] at ih ⊢
    rw [ih]
    rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem closK_spec {w len ng Np i : Nat} {G C M X E : Nat → Nat}
    (h : closK w len ng Np G C M X E i = true) :
    ∀ k < ng, ∃ j < Np, imgK w len (G k) (C (X i)) = M (X j) := by
  unfold closK at h
  rw [Orb.allN_iff] at h
  intro k hk
  have h1 := h k hk
  rw [strictB_eq] at h1
  obtain ⟨h2, h3⟩ := band h1
  exact ⟨_, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem treeK_spec {w len ng i : Nat} {G C M X D : Nat → Nat}
    (h : treeK w len ng G C M X D i = true) (hi : 0 < i) :
    D i % 65536 < i ∧ D i / 65536 < ng ∧
      imgK w len (G (D i / 65536)) (C (X (D i % 65536))) = M (X i) := by
  unfold treeK at h
  have hb : Nat.beq i 0 = false := by
    cases e : Nat.beq i 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  rw [hb] at h
  change strictB (Nat.mod (D i) 65536) (fun p => strictB (Nat.div (D i) 65536) fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l ng, Nat.beq (imgK w len (G l) (C (X p))) (M (X i))))) = true
    at h
  rw [strictB_eq, strictB_eq] at h
  obtain ⟨h1, h2⟩ := band h
  obtain ⟨h2, h3⟩ := band h2
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem orbit_of_pinned {act : Nat → Array Nat → Array Nat} {ngen : Nat}
    {valid : Array Nat → Bool} {key : Array Nat → Nat} {root : Array Nat} {fuel N : Nat}
    {V : Nat → Array Nat} {par lab : Nat → Nat} (h0 : 0 < N) (hroot : V 0 = root)
    (hcl : ∀ i < N, ∀ k < ngen, ∃ j < N, act k (V i) = V j)
    (htr : ∀ i < N, 0 < i → par i < i ∧ lab i < ngen ∧ V i = act (lab i) (V (par i)))
    (hv : ∀ i < N, valid (V i) = true)
    (hkey : ∀ a < N, ∀ b < N, key (V a) = key (V b) → V a = V b)
    (hinj : ∀ a < N, ∀ b < N, V a = V b → a = b) (hf : N ≤ fuel) :
    arrCertOK act ngen valid key root (arrBfs act ngen key root fuel) = true ∧
      (∀ x, x ∈ (arrBfs act ngen key root fuel).pts ↔ ∃ i < N, V i = x) ∧
      (arrBfs act ngen key root fuel).pts.size = N := by
  classical
  let S : Finset (Array Nat) := (Finset.range N).image V
  have memS : ∀ x, x ∈ S ↔ ∃ i < N, V i = x := fun x => by
    simp only [S, Finset.mem_image, Finset.mem_range]
  have hrootS : root ∈ S := (memS _).2 ⟨0, h0, hroot⟩
  have hclS : ∀ x ∈ S, ∀ k < ngen, act k x ∈ S := by
    intro x hx k hk
    obtain ⟨i, hi, rfl⟩ := (memS x).1 hx
    obtain ⟨j, hj, e⟩ := hcl i hi k hk
    exact (memS _).2 ⟨j, hj, e.symm⟩
  have hreach : ∀ i < N, Reach act ngen root (V i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        rw [hroot]
        exact Reach.root
      · obtain ⟨hp, hl, e⟩ := htr i hi h
        rw [e]
        exact Reach.step _ hl (ih _ hp (by omega))
  have hR : ∀ x ∈ S, Reach act ngen root x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (memS x).1 hx
    exact hreach i hi
  have hcard : S.card = N := by
    simp only [S]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e
  obtain ⟨h1, h2, h3, -⟩ := arrBfs_spec (act := act) (ngen := ngen) (valid := valid) (key := key)
    (root := root) (fuel := fuel) S (reach_iff_of_closed hrootS hclS hR)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := (memS x).1 hx
      exact hv i hi)
    (fun x hx y hy e => by
      obtain ⟨i, hi, rfl⟩ := (memS x).1 hx
      obtain ⟨j, hj, rfl⟩ := (memS y).1 hy
      exact hkey i hi j hj e)
    (by rw [hcard]; exact hf)
  refine ⟨h1, fun x => (h2 x).trans (memS x), by rw [h3, hcard]⟩

end CFSG.KC.SetOrb

end
