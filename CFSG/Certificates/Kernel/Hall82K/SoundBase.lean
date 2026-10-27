module

public import CFSG.Certificates.Kernel.Hall82K.Linear
public import Certificates.Data.Kernel.Hall82K.Bridge
public import Certificates.Data.Kernel.Hall82K.C5
public import CFSG.CGT.Hall82.DModelFacts

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa

theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem bor_eq_true {a b : Bool} : bor a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [bor]

theorem band_eq_true {a b : Bool} : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [band]

theorem bnot_eq_true {a : Bool} : Bool.rec (motive := fun _ => Bool) true false a = true ↔
    a = false := by
  cases a <;> simp

theorem beqB_eq_true {a b : Bool} : beqB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [beqB]

theorem b2n_eq (b : Bool) : b2n b = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem allL_iff {p : ℕ → Bool} {L : List ℕ} : allL p L = true ↔ ∀ x ∈ L, p x = true := by
  induction L with
  | nil => simp [allL]
  | cons h t ih =>
    change band (p h) (allL p t) = true ↔ _
    rw [band_eq_true, ih, List.forall_mem_cons]

theorem memL_iff {z : ℕ} {L : List ℕ} : memL z L = true ↔ z ∈ L := by
  induction L with
  | nil => simp [memL]
  | cons h t ih =>
    change bor (Nat.beq z h) (memL z t) = true ↔ _
    rw [bor_eq_true, ih, nbeq_iff, List.mem_cons]

theorem allN_iff {p : ℕ → Bool} {n : ℕ} : allN p n = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change band (p n) (allN p n) = true ↔ _
    rw [band_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem testBit_orL {f : ℕ → ℕ} {L : List ℕ} {k : ℕ} :
    (orL f L).testBit k = true ↔ ∃ h ∈ L, (f h).testBit k = true := by
  induction L with
  | nil => simp [orL]
  | cons h t ih =>
    change (f h ||| orL f t).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp

theorem allLL_iff {p : List ℕ → Bool} {A : List (List ℕ)} :
    allLL p A = true ↔ ∀ L ∈ A, p L = true := by
  induction A with
  | nil => simp [allLL]
  | cons h t ih =>
    change band (p h) (allLL p t) = true ↔ _
    rw [band_eq_true, ih, List.forall_mem_cons]

theorem anyLL_iff {p : List ℕ → Bool} {A : List (List ℕ)} :
    anyLL p A = true ↔ ∃ L ∈ A, p L = true := by
  induction A with
  | nil => simp [anyLL]
  | cons h t ih =>
    change bor (p h) (anyLL p t) = true ↔ _
    rw [bor_eq_true, ih]
    simp

theorem bitN_eq_one_iff {m x : ℕ} : bitN m x = 1 ↔ m.testBit x = true := by
  have h := bitN_mul m x 1
  have e : Nat.mul (bitN m x) 1 = bitN m x := Nat.mul_one _
  rw [e] at h
  rw [h]
  cases m.testBit x <;> simp

theorem lowB_spec {m : ℕ} (hm : m ≠ 0) : ∃ j r, m = r <<< (j + 1) ||| 2 ^ j ∧
    lowB m = 2 ^ j ∧ Nat.sub m (lowB m) = r <<< (j + 1) := by
  obtain ⟨j, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  obtain ⟨r, rfl⟩ := hq
  have hj : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
  have hj1 := Nat.one_le_two_pow (n := j)
  have hs : r <<< (j + 1) = 2 ^ j * (2 * r) := by
    rw [Nat.shiftLeft_eq, pow_succ]
    ring
  have e1 : 2 ^ j * (2 * r + 1) = r <<< (j + 1) ||| 2 ^ j := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hj, hs]
    ring
  have e2 : 2 ^ j * (2 * r + 1) - 1 = r <<< (j + 1) ||| (2 ^ j - 1) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : 2 ^ j - 1 < 2 ^ (j + 1)), hs]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hand : (r <<< (j + 1) ||| 2 ^ j) &&& (r <<< (j + 1) ||| (2 ^ j - 1)) = r <<< (j + 1) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow,
      Nat.testBit_two_pow_sub_one]
    by_cases h1 : j + 1 ≤ i
    · have h2 : j ≠ i := by omega
      have h3 : ¬ i < j := by omega
      simp [h1, h2, h3]
    · have h1' : ¬ i ≥ j + 1 := h1
      simp only [ge_iff_le, h1, decide_false, Bool.false_and, Bool.false_or]
      by_cases h2 : j = i
      · subst h2
        simp
      · simp [h2]
  have hlow : lowB (2 ^ j * (2 * r + 1)) = 2 ^ j := by
    unfold lowB
    change 2 ^ j * (2 * r + 1) - (2 ^ j * (2 * r + 1) &&& (2 ^ j * (2 * r + 1) - 1)) = _
    rw [e2, e1, hand, ← Nat.shiftLeft_add_eq_or_of_lt hj]
    omega
  refine ⟨j, r, e1, hlow, ?_⟩
  change 2 ^ j * (2 * r + 1) - lowB (2 ^ j * (2 * r + 1)) = _
  rw [hlow, e1, ← Nat.shiftLeft_add_eq_or_of_lt hj]
  omega

theorem forBitsK_sound (hidx : idxBridgeK = true) {p : ℕ → Bool} {n m : ℕ} (hm : m < 2 ^ 64)
    (h : forBitsK p n m = true) : ∀ x < 64, bitN m x = 1 → p x = true := by
  induction n generalizing m with
  | zero =>
    intro x _ hb
    change Nat.beq m 0 = true at h
    rw [nbeq_iff] at h
    subst h
    rw [bitN_eq_one_iff, Nat.zero_testBit] at hb
    exact absurd hb (by simp)
  | succ n ih =>
    intro x hx hb
    change bor (Nat.beq m 0) (band (p (idxB (lowB m))) (forBitsK p n (Nat.sub m (lowB m)))) =
      true at h
    rw [bor_eq_true, band_eq_true, nbeq_iff] at h
    rw [bitN_eq_one_iff] at hb
    rcases h with h0 | ⟨hp, hrest⟩
    · subst h0
      rw [Nat.zero_testBit] at hb
      exact absurd hb (by simp)
    · have hm0 : m ≠ 0 := by
        rintro rfl
        rw [Nat.zero_testBit] at hb
        exact absurd hb (by simp)
      obtain ⟨j, r, em, hl, hs⟩ := lowB_spec hm0
      rw [hl] at hp
      rw [hs] at hrest
      have hle : r <<< (j + 1) ≤ m := by
        have hj : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j)
        rw [em, ← Nat.shiftLeft_add_eq_or_of_lt hj]
        omega
      rw [em, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with hb | hb
      · exact ih (lt_of_le_of_lt hle hm) hrest x hx (bitN_eq_one_iff.2 hb)
      · subst hb
        have hi := nbeq_iff.1 (allN_iff.1 hidx j hx)
        change idxB (1 <<< j) = j at hi
        rw [Nat.one_shiftLeft] at hi
        rwa [hi] at hp

theorem fld_lt64 (c s : ℕ) : fld c s < 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem ite_lt64 (b : Bool) {a : ℕ} (ha : a < 64) : (if b = true then a else 0) < 64 := by
  cases b <;> simp [ha]

theorem xor_lt64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem apL_lt (c v : ℕ) : apL c v < 64 := by
  unfold apL
  simp only [bitN_mul]
  have hx : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
  simp only [hx]
  refine xor_lt64 (xor_lt64 (xor_lt64 ?_ ?_) (xor_lt64 ?_ ?_)) (xor_lt64 ?_ ?_) <;>
    exact ite_lt64 _ (fld_lt64 _ _)

theorem ite_xor_bool (p q : Bool) (a : ℕ) :
    (if (p ^^ q) = true then a else 0) = (if p = true then a else 0) ^^^ (if q = true then a else 0) := by
  cases p <;> cases q <;> simp

theorem apL_xor (c a b : ℕ) : apL c (a ^^^ b) = apL c a ^^^ apL c b := by
  unfold apL
  simp only [bitN_mul, Nat.testBit_xor, ite_xor_bool]
  have hx : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
  simp only [hx]
  ac_rfl

@[expose] def fnL (c : ℕ) : Fin 64 → Fin 64 := fun v => ⟨apL c v.val, apL_lt c v.val⟩

theorem fnL_val (c : ℕ) (v : Fin 64) : (fnL c v).val = apL c v.val := rfl

theorem fnL_add (c : ℕ) : ∀ v w, fnL c (xorF v w) = xorF (fnL c v) (fnL c w) := fun v w =>
  Fin.ext (apL_xor c v.val w.val)

theorem apL_pow (c : ℕ) :
    apL c 1 = fld c 0 ∧ apL c 2 = fld c 6 ∧ apL c 4 = fld c 12 ∧ apL c 8 = fld c 18 ∧
      apL c 16 = fld c 24 ∧ apL c 32 = fld c 30 := by
  unfold apL
  simp only [bitN_mul]
  have hx : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
  simp (config := { decide := true }) only [hx, if_true, if_false, Nat.xor_zero, Nat.zero_xor,
    Bool.false_eq_true]

theorem enc6_fld {c : ℕ} (hc : c < 2 ^ 36) :
    enc6 (fld c 0) (fld c 6) (fld c 12) (fld c 18) (fld c 24) (fld c 30) = c := by
  simp only [fld_eq, enc6]
  norm_num at hc ⊢
  omega

theorem enc6_lt {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64)
    (h3 : a3 < 64) (h4 : a4 < 64) (h5 : a5 < 64) : enc6 a0 a1 a2 a3 a4 a5 < 2 ^ 36 := by
  unfold enc6
  norm_num
  omega

theorem codeL_fnL {c : ℕ} (hc : c < 2 ^ 36) : codeL (fnL c) = c := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := apL_pow c
  change enc6 (apL c 1) (apL c 2) (apL c 4) (apL c 8) (apL c 16) (apL c 32) = c
  rw [e0, e1, e2, e3, e4, e5]
  exact enc6_fld hc

theorem codeL_lt (f : Fin 64 → Fin 64) : codeL f < 2 ^ 36 :=
  enc6_lt (f 1).2 (f 2).2 (f 4).2 (f 8).2 (f 16).2 (f 32).2

theorem fnL_inj {c d : ℕ} (hc : c < 2 ^ 36) (hd : d < 2 ^ 36) (h : fnL c = fnL d) : c = d := by
  rw [← codeL_fnL hc, ← codeL_fnL hd, h]

theorem compL_eq_enc6 (f g : ℕ) : compL f g = enc6 (apL f (fld g 0)) (apL f (fld g 6))
    (apL f (fld g 12)) (apL f (fld g 18)) (apL f (fld g 24)) (apL f (fld g 30)) :=
  lorTree_eq_enc6 (apL_lt _ _) (apL_lt _ _) (apL_lt _ _) (apL_lt _ _) (apL_lt _ _)

theorem compL_lt (f g : ℕ) : compL f g < 2 ^ 36 := by
  rw [compL_eq_enc6]
  exact enc6_lt (apL_lt _ _) (apL_lt _ _) (apL_lt _ _) (apL_lt _ _) (apL_lt _ _) (apL_lt _ _)

theorem compL_eq_codeL (f g : ℕ) : compL f g = codeL (fun v => fnL f (fnL g v)) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := apL_pow g
  rw [compL_eq_enc6]
  change _ = enc6 (apL f (apL g 1)) (apL f (apL g 2)) (apL f (apL g 4)) (apL f (apL g 8))
    (apL f (apL g 16)) (apL f (apL g 32))
  rw [e0, e1, e2, e3, e4, e5]

theorem apL_compL (f g : ℕ) (v : Fin 64) : apL (compL f g) v.val = apL f (apL g v.val) := by
  rw [compL_eq_codeL, apL_codeL (fun v w => by rw [fnL_add, fnL_add]) v]
  rfl

theorem fnL_compL (f g : ℕ) : fnL (compL f g) = fun v => fnL f (fnL g v) :=
  funext fun v => Fin.ext (apL_compL f g v)

theorem fnL_codeL {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) :
    fnL (codeL f) = f :=
  funext fun v => Fin.ext (apL_codeL hf v)

theorem codeL_inj {f g : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (hg : ∀ v w, g (xorF v w) = xorF (g v) (g w)) (h : codeL f = codeL g) : f = g := by
  rw [← fnL_codeL hf, ← fnL_codeL hg, h]

theorem codeArrK_spec {c : ℕ} {a : Array ℕ} (h : codeArrK c a = true) :
    a.size = 64 ∧ ∀ v < 64, a.getD v 0 = apL c v := by
  unfold codeArrK at h
  rw [band_eq_true, nbeq_iff, allN_iff] at h
  exact ⟨h.1, fun v hv => nbeq_iff.1 (h.2 v hv)⟩

theorem codeArrK_getElem {c : ℕ} {a : Array ℕ} (h : codeArrK c a = true) {v : ℕ} (hv : v < 64) :
    a[v]! = apL c v := by
  obtain ⟨hs, h⟩ := codeArrK_spec h
  rw [← h v hv, getElem!_pos a v (by omega), Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega), Option.getD_some]

theorem zipArrK_spec {L : List ℕ} {A : List (Array ℕ)} (h : zipArrK L A = true) :
    List.Forall₂ (fun c a => codeArrK c a = true) L A := by
  induction L generalizing A with
  | nil =>
    cases A with
    | nil => exact List.Forall₂.nil
    | cons a A => exact absurd h (by simp [zipArrK])
  | cons c L ih =>
    cases A with
    | nil => exact absurd h (by simp [zipArrK])
    | cons a A =>
      change band (codeArrK c a) (zipArrK L A) = true at h
      rw [band_eq_true] at h
      exact List.Forall₂.cons h.1 (ih h.2)

theorem forall₂_mem_right {R : ℕ → Array ℕ → Prop} {L : List ℕ} {A : List (Array ℕ)}
    (h : List.Forall₂ R L A) {a : Array ℕ} (ha : a ∈ A) : ∃ c ∈ L, R c a := by
  induction h with
  | nil => simp at ha
  | cons hr _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨c, hc, hr'⟩ := ih ha
      exact ⟨c, List.mem_cons_of_mem _ hc, hr'⟩

theorem forall₂_mem_left {R : ℕ → Array ℕ → Prop} {L : List ℕ} {A : List (Array ℕ)}
    (h : List.Forall₂ R L A) {c : ℕ} (hc : c ∈ L) : ∃ a ∈ A, R c a := by
  induction h with
  | nil => simp at hc
  | cons hr _ ih =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hr'⟩ := ih hc
      exact ⟨a, List.mem_cons_of_mem _ ha, hr'⟩

theorem s40K_lt : ∀ c ∈ s40K, c < 2 ^ 36 := by decide +kernel

theorem fnL_mem_hallS40 (hs40 : zipArrK s40K CFSG.CGT.Hall82.hallS40Arr = true) {c : ℕ}
    (hc : c ∈ s40K) : fnL c ∈ CFSG.CGT.Hall82.hallS40 := by
  obtain ⟨a, ha, hca⟩ := forall₂_mem_left (zipArrK_spec hs40) hc
  exact ⟨a, ha, fun k => ((codeArrK_spec hca).2 k.val k.2).symm⟩

theorem mem_hallS40_iff (hs40 : zipArrK s40K CFSG.CGT.Hall82.hallS40Arr = true)
    {z : Fin 64 → Fin 64} (hz : ∀ v w, z (xorF v w) = xorF (z v) (z w)) :
    z ∈ CFSG.CGT.Hall82.hallS40 ↔ codeL z ∈ s40K := by
  constructor
  · rintro ⟨a, ha, hza⟩
    obtain ⟨c, hc, hca⟩ := forall₂_mem_right (zipArrK_spec hs40) ha
    have he : z = fnL c := funext fun k => Fin.ext (by
      rw [hza k, (codeArrK_spec hca).2 k.val k.2, fnL_val])
    rw [he, codeL_fnL (s40K_lt c hc)]
    exact hc
  · intro hc
    have h := fnL_mem_hallS40 hs40 hc
    rwa [fnL_codeL hz] at h

end CFSG.KC.Hall82K
