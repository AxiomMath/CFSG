module

public import Certificates.Data.Kernel.Tower.Chi
public import CFSG.Certificates.Kernel.Tower.T2Sound
public import CFSG.Certificates.Kernel.Tower.TreeSound

public section

namespace Certificates.KernelTower

open CFSG.OddStandard.AltStdSmall4.Tower

theorem anyB_eq_true {n : Nat} {p : Nat → Bool} : anyB n p = true ↔ ∃ k < n, p k = true := by
  induction n with
  | zero =>
    refine ⟨fun h => ?_, fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k)⟩
    change false = true at h
    exact absurd h Bool.false_ne_true
  | succ n ih =>
    have e : anyB (n + 1) p = (p n || anyB n p) := rfl
    rw [e, Bool.or_eq_true, ih]
    refine ⟨fun h => ?_, fun ⟨k, hk, hp⟩ => ?_⟩
    · rcases h with h | ⟨k, hk, hp⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, by omega, hp⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr ⟨k, hk, hp⟩
      · exact Or.inl hp

theorem bitS_mono {a a' k : Nat} (hle : ∀ i, a.testBit i = true → a'.testBit i = true)
    (h : bitS a k = true) : bitS a' k = true := by
  unfold bitS at h ⊢
  rw [Nat.blt_eq] at h ⊢
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero (Nat.pos_iff_ne_zero.1 h)
  have hi' : (a &&& (1 <<< k)).testBit i = true := hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi'
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have h1 : (a' &&& (1 <<< k)).testBit i = true := by
    simp only [Nat.testBit_and, hle i hi'.1, hi'.2, Bool.and_self]
  have h0' : a' &&& (1 <<< k) = 0 := h0
  rw [h0', Nat.zero_testBit] at h1
  exact absurd h1 Bool.false_ne_true

theorem bitS_or_left {a b k : Nat} (h : bitS a k = true) : bitS (Nat.lor a b) k = true :=
  bitS_mono (fun i hi => by
    have e : (a ||| b).testBit i = true := by rw [Nat.testBit_or, hi, Bool.true_or]
    exact e) h

theorem bitS_or_right {a b k : Nat} (h : bitS b k = true) : bitS (Nat.lor a b) k = true :=
  bitS_mono (fun i hi => by
    have e : (a ||| b).testBit i = true := by rw [Nat.testBit_or, hi, Bool.or_true]
    exact e) h

theorem bitS_union {S : Nat → Nat} {k : Nat} :
    ∀ n, ∀ j < n, bitS (S j) k = true →
      bitS (Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor (S j) acc) n) k = true := by
  intro n
  induction n with
  | zero => exact fun j hj => absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro j hj h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact bitS_or_right (ih j hj h)
    · exact bitS_or_left h

theorem bitN_le (S k : Nat) : bitN S k ≤ 1 := Nat.and_le_right

theorem bitN_eq (S k : Nat) : bitN S k = S / 2 ^ k % 2 := by
  change (S >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  have := Nat.xor_lt_two_pow (n := 1) (x := a) (y := b) (by omega) (by omega)
  omega

theorem chiV_le (C c : Nat) : chiV C c ≤ 1 := xor_le_one (bitN_le _ _) (bitN_le _ _)

theorem shr (a n : Nat) : Nat.shiftRight a n = a / 2 ^ n := Nat.shiftRight_eq_div_pow a n

theorem div_pow_add_mod {C s w : Nat} (h : s + w ≤ 134) :
    (C + 2 ^ 134) / 2 ^ s % 2 ^ w = C / 2 ^ s % 2 ^ w := by
  have e : 2 ^ 134 = 2 ^ w * 2 ^ (134 - s - w) * 2 ^ s := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [e, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem chiV_add {C c : Nat} (hc : c < 8192) :
    chiV (Nat.add C 21778071482940061661655974875633165533184) c = chiV C c := by
  have eL : Nat.add C 21778071482940061661655974875633165533184 = C + 2 ^ 134 := by
    rw [Nat.add_eq]
    norm_num
  rw [eL]
  have e1 : Nat.land (Nat.shiftRight (C + 2 ^ 134) 128) 63 = Nat.land (Nat.shiftRight C 128) 63 := by
    rw [and63, and63, shr, shr]
    exact div_pow_add_mod (s := 128) (w := 6) (by omega)
  have e2 : bitN (C + 2 ^ 134) (Nat.shiftRight c 6) = bitN C (Nat.shiftRight c 6) := by
    rw [bitN_eq, bitN_eq, shr6]
    exact div_pow_add_mod (w := 1) (by omega)
  unfold chiV
  rw [e1, e2]

theorem shr1 (k : Nat) : Nat.shiftRight k 1 = k / 2 :=
  (Nat.shiftRight_eq_div_pow k 1).trans (by rw [pow_one])

theorem chiT_eq (T k : Nat) : chiT T k = chiV T (k / 2) ^^^ (k % 2 * bitN T 134) := by
  have e7 : Nat.shiftRight k 7 = Nat.shiftRight (k / 2) 6 := by
    rw [shr, shr, Nat.div_div_eq_div_mul] <;> rfl
  have ed : Nat.land k (bitN T 134) = k % 2 * bitN T 134 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (bitN_le T 134) with h | h
    · rw [h, Nat.mul_zero]
      exact Nat.and_zero k
    · rw [h, Nat.mul_one]
      exact Nat.and_one_is_mod k
  unfold chiT chiV
  rw [e7, ed, shr1] <;> rfl

theorem chiT_le (T k : Nat) : chiT T k ≤ 1 := by
  rw [chiT_eq]
  refine xor_le_one (chiV_le _ _) ?_
  have h1 : k % 2 ≤ 1 := by omega
  have h2 := Nat.mul_le_mul h1 (bitN_le T 134)
  omega

theorem xbit_eq (T k : Nat) : xbit T k = chiT T k := by
  change chiT T k &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.mod_eq_of_lt (by have := chiT_le T k; omega)]

theorem parOK_sound (h : parOK = true) {a b : Nat} (ha : a < 64) (hb : b < 64) :
    bitN par64 (a ^^^ b) = bitN par64 a ^^^ bitN par64 b := by
  simp only [parOK, Bool.and_eq_true, allB_eq_true] at h
  exact Nat.eq_of_beq_eq_true (h.2 a ha b hb)

theorem chiWOK_parts {SM AC C : Nat} (h : chiWOK SM AC C = true) :
    (∀ i < 128, ∀ j < 128, bitN C (lane SM 7 127 (128 * i + j)) = bitN C i ^^^ bitN C j) ∧
      ∀ i < 128, ∀ v < 64, bitN par64 (lane AC 6 63 (64 * i + v) &&& ((C >>> 128) &&& 63)) =
        bitN par64 (v &&& ((C >>> 128) &&& 63)) := by
  simp only [chiWOK, Bool.and_eq_true, allB_eq_true] at h
  exact ⟨fun i hi j hj => Nat.eq_of_beq_eq_true (h.1 i hi j hj),
    fun i hi v hv => Nat.eq_of_beq_eq_true (h.2 i hi v hv)⟩

theorem chiV_hom {SM AC C : Nat} (hP : parOK = true) (hC : chiWOK SM AC C = true) {a b : Nat}
    (ha : a < 8192) (hb : b < 8192) :
    chiV C (wm SM AC a b) = chiV C a ^^^ chiV C b := by
  obtain ⟨hS, hA⟩ := chiWOK_parts hC
  have hsa : a / 64 < 128 := by omega
  have hsb : b / 64 < 128 := by omega
  have hva : a % 64 < 64 := Nat.mod_lt a (by omega)
  have hvb : b % 64 < 64 := Nat.mod_lt b (by omega)
  have hS' := hS _ hsa _ hsb
  have hA' := hA _ hsa _ hvb
  have ew : wm SM AC a b = 64 * lane SM 7 127 (128 * (a / 64) + b / 64) +
      (a % 64 ^^^ lane AC 6 63 (64 * (a / 64) + b % 64)) := by
    rw [← shr6 a, ← shr6 b, ← and63 a, ← and63 b]
    rfl
  have ev : ∀ c, chiV C c =
      bitN par64 (c % 64 &&& ((C >>> 128) &&& 63)) ^^^ bitN C (c / 64) := by
    intro c
    rw [← and63 c, ← shr6 c]
    rfl
  rw [ev, ev, ev, ew]
  have hsm : lane SM 7 127 (128 * (a / 64) + b / 64) ≤ 127 := lane_le _ _ _ _
  have hac : lane AC 6 63 (64 * (a / 64) + b % 64) ≤ 63 := lane_le _ _ _ _
  generalize lane SM 7 127 (128 * (a / 64) + b / 64) = sm at hS' hsm ⊢
  generalize lane AC 6 63 (64 * (a / 64) + b % 64) = ac at hA' hac ⊢
  generalize (C >>> 128) &&& 63 = l at hA' ⊢
  have hx : a % 64 ^^^ ac < 64 := Nat.xor_lt_two_pow (n := 6) hva (by omega)
  have e1 : (64 * sm + (a % 64 ^^^ ac)) % 64 = a % 64 ^^^ ac := by omega
  have e2 : (64 * sm + (a % 64 ^^^ ac)) / 64 = sm := by omega
  have hal : a % 64 &&& l < 64 := lt_of_le_of_lt Nat.and_le_left hva
  have hacl : ac &&& l < 64 := lt_of_le_of_lt Nat.and_le_left (by omega)
  rw [e1, e2, hS', Nat.and_xor_distrib_right, parOK_sound hP hal hacl, hA']
  ac_rfl

variable {X : Type*} [Group X] {mul : Nat → Nat → Nat} {dec : Nat → X}

theorem chiV_hom_of_chiX {SM AC : Nat} {CL : Nat → Nat} (hP : parOK = true)
    (hCL : ∀ i < 16, chiWOK SM AC (CL i) = true) {FA g GS T : Nat}
    (hX : chiXOK CL FA g GS T = true) (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    {a b : Nat} (ha : a < 8192) (hb : b < 8192) :
    chiV T (wm SM AC a b) = chiV T a ^^^ chiV T b := by
  simp only [chiXOK, Bool.and_eq_true, anyB_eq_true, Bool.or_eq_true] at hX
  obtain ⟨i, hi, hT⟩ := hX.1.1
  have hab := M.mul_lt a ha b hb
  rcases hT with hT | hT
  · rw [Nat.eq_of_beq_eq_true hT]
    exact chiV_hom hP (hCL i hi) ha hb
  · rw [Nat.eq_of_beq_eq_true hT]
    rw [chiV_add hab, chiV_add ha, chiV_add hb]
    exact chiV_hom hP (hCL i hi) ha hb

theorem chiV_alpha {SM AC : Nat} {CL : Nat → Nat} (hP : parOK = true)
    (hCL : ∀ i < 16, chiWOK SM AC (CL i) = true) {FA g GS PT T : Nat}
    (hX : chiXOK CL FA g GS T = true) (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    (hT : treeB 8192 4 (wm SM AC) GS PT = true) (α : X →* X)
    (hFA : ∀ c < 8192, l16 FA c < 8192 ∧ α (dec c) = dec (l16 FA c)) :
    ∀ c < 8192, chiV T (l16 FA c) = chiV T c := by
  have hX' := hX
  simp only [chiXOK, Bool.and_eq_true, allB_eq_true] at hX'
  have hgen : ∀ i < 4, chiV T (l16 FA (l16 GS i)) = chiV T (l16 GS i) :=
    fun i hi => Nat.eq_of_beq_eq_true (hX'.1.2 i hi)
  have hom : ∀ {a b : Nat}, a < 8192 → b < 8192 →
      chiV T (wm SM AC a b) = chiV T a ^^^ chiV T b := fun ha hb =>
    chiV_hom_of_chiX hP hCL hX M ha hb
  suffices H : ∀ d, ∀ c < 8192, ptDep PT c = d → chiV T (l16 FA c) = chiV T c from
    fun c hc => H _ c hc rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro c hc hd
    by_cases h0 : c = 0
    · subst h0
      have e : l16 FA 0 = 0 := by
        obtain ⟨h1, h2⟩ := hFA 0 (by omega)
        rw [M.dec_zero, map_one, ← M.dec_zero] at h2
        exact (M.inj _ (by omega) _ h1 h2).symm
      rw [e]
    · obtain ⟨hgi, hpar, hdep, hmul⟩ := treeB_get hT hc h0
      have ih2 := ih _ (hd ▸ hdep) _ hpar rfl
      have hg := treeB_gen hT hgi
      obtain ⟨hF1, hα1⟩ := hFA _ hg
      obtain ⟨hF2, hα2⟩ := hFA _ hpar
      have e : l16 FA c = wm SM AC (l16 FA (l16 GS (ptGi PT c))) (l16 FA (ptPar PT c)) := by
        obtain ⟨hF, hα⟩ := hFA c hc
        have e0 : dec c = dec (l16 GS (ptGi PT c)) * dec (ptPar PT c) := by
          rw [← M.dec_mul _ hg _ hpar, hmul]
        refine M.inj _ hF _ (M.mul_lt _ hF1 _ hF2) ?_
        rw [← hα, e0, map_mul, hα1, hα2, ← M.dec_mul _ hF1 _ hF2]
      rw [e, hom hF1 hF2, hgen _ hgi, ih2, ← hom hg hpar, hmul]

theorem xbit_tm {SM AC : Nat} {CL : Nat → Nat} (hP : parOK = true)
    (hCL : ∀ i < 16, chiWOK SM AC (CL i) = true) {FA g GS PT T : Nat}
    (hX : chiXOK CL FA g GS T = true) (M : IsModel (⊤ : Subgroup X) 8192 (wm SM AC) dec)
    (hT : treeB 8192 4 (wm SM AC) GS PT = true) (α : X →* X)
    (hFA : ∀ c < 8192, l16 FA c < 8192 ∧ α (dec c) = dec (l16 FA c)) (hg : g < 8192)
    {a b : Nat} (ha : a < 16384) (hb : b < 16384) :
    xbit T (tm (wm SM AC) FA g a b) = xbit T a ^^^ xbit T b := by
  have hX' := hX
  simp only [chiXOK, Bool.and_eq_true] at hX'
  have hg0 : chiV T g = 0 := Nat.eq_of_beq_eq_true hX'.2
  have hom : ∀ {a b : Nat}, a < 8192 → b < 8192 →
      chiV T (wm SM AC a b) = chiV T a ^^^ chiV T b := fun ha hb =>
    chiV_hom_of_chiX hP hCL hX M ha hb
  have hal := chiV_alpha hP hCL hX M hT α hFA
  have ha2 : a / 2 < 8192 := by omega
  have hb2 : b / 2 < 8192 := by omega
  have hF := (hFA _ hb2).1
  have hx : chiV T (a / 2) < 2 := Nat.lt_succ_of_le (chiV_le _ _)
  have hy : chiV T (b / 2) < 2 := Nat.lt_succ_of_le (chiV_le _ _)
  have hd : bitN T 134 < 2 := Nat.lt_succ_of_le (bitN_le _ _)
  simp only [xbit_eq, chiT_eq]
  rw [tm_eq]
  have q : ∀ m r, r < 2 → (2 * m + r) / 2 = m ∧ (2 * m + r) % 2 = r := fun m r hr =>
    ⟨by omega, by omega⟩
  have q0 : ∀ m, 2 * m / 2 = m ∧ 2 * m % 2 = 0 := fun m => ⟨by omega, by omega⟩
  split_ifs with h1 h2
  · obtain ⟨e1, e2⟩ := q0 (wm SM AC (wm SM AC (a / 2) (l16 FA (b / 2))) g)
    rw [e1, e2, h1, h2, hom (M.mul_lt _ ha2 _ hF) hg, hom ha2 hF, hg0, hal _ hb2]
    have L : ∀ x < 2, ∀ y < 2, ∀ d < 2,
        ((x ^^^ y) ^^^ 0) ^^^ 0 * d = (x ^^^ 1 * d) ^^^ (y ^^^ 1 * d) := by decide
    exact L _ hx _ hy _ hd
  · have hb0 : b % 2 = 0 := by omega
    obtain ⟨e1, e2⟩ := q (wm SM AC (a / 2) (l16 FA (b / 2))) 1 (by omega)
    rw [e1, e2, h1, hb0, hom ha2 hF, hal _ hb2]
    have L : ∀ x < 2, ∀ y < 2, ∀ d < 2,
        (x ^^^ y) ^^^ 1 * d = (x ^^^ 1 * d) ^^^ (y ^^^ 0 * d) := by decide
    exact L _ hx _ hy _ hd
  · have ha0 : a % 2 = 0 := by omega
    obtain ⟨e1, e2⟩ := q (wm SM AC (a / 2) (b / 2)) (b % 2) (by omega)
    rw [e1, e2, ha0, hom ha2 hb2]
    have L : ∀ x < 2, ∀ y < 2, ∀ d < 2, ∀ r < 2,
        (x ^^^ y) ^^^ r * d = (x ^^^ 0 * d) ^^^ (y ^^^ r * d) := by decide
    exact L _ hx _ hy _ hd _ (by omega)

end Certificates.KernelTower
