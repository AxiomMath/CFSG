module

public import Certificates.Data.Kernel.E8K
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.GroupTheory.E8GenFacts
import CFSG.Certificates.Kernel.Misc.KGrpSound
import CFSG.GroupTheory.CommuteOfSqEqOne
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ElemAbList
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.KC.E8K

open Equiv CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG

open scoped Pointwise

variable {n : ℕ}

def mset (n : ℕ) (E : ℕ → ℕ) (N M : ℕ) : Set (Perm (Fin n)) :=
  {x | ∃ k < N, bit M k = true ∧ pcode x = E k}

theorem allW_iff (W : List Wit) (f : Wit → Bool) : allW W f = true ↔ ∀ w ∈ W, f w = true := by
  induction W with
  | nil => simp [allW]
  | cons w W ih =>
    change andB (f w) (allW W f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyW_iff (W : List Wit) (f : Wit → Bool) : anyW W f = true ↔ ∃ w ∈ W, f w = true := by
  induction W with
  | nil => simp [anyW]
  | cons w W ih =>
    change orB (f w) (anyW W f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem allP_iff (L : PL) (f : ℕ → List ℕ → Bool) :
    allP L f = true ↔ ∀ p ∈ L, f p.1 p.2 = true := by
  induction L with
  | nil => simp [allP]
  | cons p L ih =>
    change andB (f p.1 p.2) (allP L f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyP_iff (L : PL) (f : ℕ → List ℕ → Bool) :
    anyP L f = true ↔ ∃ p ∈ L, f p.1 p.2 = true := by
  induction L with
  | nil => simp [anyP]
  | cons p L ih =>
    change orB (f p.1 p.2) (anyP L f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem nthP_get (L : PL) (f : ℕ → List ℕ → ℕ) {i : ℕ} (hi : i < L.length) :
    nthP L f i = f L[i].1 L[i].2 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons p L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa using hi)

theorem brec_true {a b : Bool} : Bool.rec (motive := fun _ => Bool) a b true = b := rfl

theorem brec_false {a b : Bool} : Bool.rec (motive := fun _ => Bool) a b false = a := rfl

theorem notB_true : notB true = false := rfl

theorem notB_false : notB false = true := rfl

theorem eqB_iff {a b : Bool} : eqB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [eqB, notB]

theorem bit_iff (m i : ℕ) : bit m i = true ↔ m.testBit i = true := by
  change Nat.beq ((m >>> i) &&& 1) 1 = true ↔ _
  rw [beq_true_iff, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff]

theorem bit_land (a b i : ℕ) : bit (Nat.land a b) i = true ↔ bit a i = true ∧ bit b i = true := by
  rw [bit_iff, bit_iff, bit_iff]
  change (a &&& b).testBit i = true ↔ _
  rw [Nat.testBit_and, Bool.and_eq_true]

theorem bit_maskL (L : List ℕ) (k : ℕ) : bit (maskL L) k = true ↔ k ∈ L := by
  rw [bit_iff]
  induction L with
  | nil =>
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | cons x L ih =>
    change (1 <<< x ||| maskL L).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_iff, List.mem_cons, eq_comm]

theorem nodupL_nodup {L : List ℕ} (h : nodupL L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x t ih =>
    change andB (notB (P.anyL t fun y => Nat.beq y x)) (nodupL t) = true at h
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    exact List.nodup_cons.2
      ⟨fun hx => notB_iff.1 h1 ((anyL_iff _ _).2 ⟨x, hx, Nat.beq_refl x⟩), ih h2⟩

theorem spanL_eq (a b c ab ac bc abc : ℕ) :
    spanL a b c ab ac bc abc = [0, a, b, c, ab, ac, bc, abc] := rfl

theorem pos_eq (hn : n ≤ 32) {T : Subgroup (Perm (Fin n))} {N : ℕ} {E : ℕ → ℕ}
    (hE : ExactList pcode T N E) {i j : ℕ} (hi : i < N) (hj : j < N) {x y : Perm (Fin n)}
    (hx : pcode x = E i) (hy : pcode y = E j) : x = y ↔ i = j := by
  constructor
  · rintro rfl
    exact hE.2.2 i hi j hj (hx.symm.trans hy)
  · rintro rfl
    exact (pcode_inj hn).1 (hx.trans hy.symm)

theorem inv_sound (hn : n ≤ 32) {E MK : ℕ → ℕ} {k : ℕ} (h : invAt n E MK k = true)
    {x : Perm (Fin n)} (hx : pcode x = E k) : inI MK k = true ↔ 0 < k ∧ x ^ 2 = 1 := by
  rw [invAt, eqB_iff, andB_iff, Nat.blt_eq, beq_true_iff, ← hx, pcode_mul hn, pcode_one hn,
    pcode_inj hn, ← pow_two] at h
  exact h

theorem cell_sound (hn : n ≤ 32) {N : ℕ} {E MK R : ℕ → ℕ} {k l : ℕ}
    (hp : pairAt n N E MK R k = true) (hik : inI MK k = true) (hl : l < N)
    {x y : Perm (Fin n)} (hx : pcode x = E k) (hy : pcode y = E l) :
    (bit (MK k) l = true ↔ inI MK l = true ∧ x * y = y * x) ∧
      (inI MK l = true → x * y = y * x → fd (R k) l < N ∧ pcode (x * y) = E (fd (R k) l)) := by
  have h := (allN_iff _ _).1 (impB_iff.1 hp hik) l hl
  simp only [cellAt, letB_eq, andB_iff, eqB_iff, impB_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hc : P.comm n (E k) (E l) = true ↔ x * y = y * x := by
    rw [← hx, ← hy]
    exact comm_iff hn x y
  rcases Bool.eq_false_or_eq_true (Nat.beq (fd (R k) l) (nat_lit 255)) with hb | hb
  · simp only [hb, notB_true, brec_false, Bool.false_eq_true, and_false, iff_false] at h1 h2
    exact ⟨⟨fun hb' => absurd hb' h1, fun ⟨hi, hxy⟩ => absurd (hc.2 hxy) (notB_iff.1 (h2 hi))⟩,
      fun hi hxy => absurd (hc.2 hxy) (notB_iff.1 (h2 hi))⟩
  · simp only [hb, notB_false, brec_true, and_true] at h1 h2
    have h3 : inI MK l = true →
        fd (R k) l < N ∧ pcode (x * y) = E (fd (R k) l) ∧ x * y = y * x := by
      intro hi
      obtain ⟨h4, h5, h6⟩ := And.imp_right andB_iff.1 (andB_iff.1 (h2 hi))
      refine ⟨Nat.blt_eq.mp h4, ((beq_true_iff.1 h5).trans ?_).symm, hc.1 h6⟩
      rw [← hx, ← hy, pcode_mul hn]
    exact ⟨⟨fun hb' => ⟨h1.1 hb', (h3 (h1.1 hb')).2.2⟩, fun ⟨hi, _⟩ => h1.2 hi⟩,
      fun hi _ => ⟨(h3 hi).1, (h3 hi).2.1⟩⟩

theorem wit_span (hn : n ≤ 32) {A : ℕ → ℕ} {nA s N : ℕ} {E MK R : ℕ → ℕ}
    {T : Subgroup (Perm (Fin n))} (hE : ExactList pcode T N E)
    (hi : ∀ k < N, invAt n E MK k = true) (hp : ∀ a < N, pairAt n N E MK R a = true) {w : Wit}
    (h : witAt n A nA s N E MK R w = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 8 ∧ (∀ k ∈ L, k < N) ∧ Wit.mask w = maskL L := by
  obtain ⟨⟨a, b, c, o, M⟩, ⟨cent, cw⟩, ⟨cj, jw⟩, ⟨three, ow⟩⟩ := w
  simp only [witAt, letB_eq, andB_iff] at h
  obtain ⟨⟨⟨ha, hb, hc⟩, hia, hib, hic⟩, ⟨hab, hac, hbc⟩, ⟨hnd, hM⟩, -⟩ := h
  have ha' : a < N := Nat.blt_eq.mp ha
  have hb' : b < N := Nat.blt_eq.mp hb
  have hc' : c < N := Nat.blt_eq.mp hc
  obtain ⟨xa, -, hxa⟩ := hE.1 a ha'
  obtain ⟨xb, -, hxb⟩ := hE.1 b hb'
  obtain ⟨xc, -, hxc⟩ := hE.1 c hc'
  have Cab := cell_sound hn (hp a ha') hia hb' hxa hxb
  have Cac := cell_sound hn (hp a ha') hia hc' hxa hxc
  have Cbc := cell_sound hn (hp b hb') hib hc' hxb hxc
  obtain ⟨-, hcab⟩ := Cab.1.1 hab
  obtain ⟨-, hcac⟩ := Cac.1.1 hac
  obtain ⟨-, hcbc⟩ := Cbc.1.1 hbc
  obtain ⟨hab', heab⟩ := Cab.2 hib hcab
  obtain ⟨hac', -⟩ := Cac.2 hic hcac
  obtain ⟨hbc', -⟩ := Cbc.2 hic hcbc
  have hnd' := nodupL_nodup hnd
  have h0ab : 0 < fd (R a) b := by
    rcases Nat.eq_zero_or_pos (fd (R a) b) with h0 | h0
    · rw [spanL_eq, h0] at hnd'
      simp at hnd'
    · exact h0
  have hsq : ∀ {k : ℕ} {x : Perm (Fin n)}, k < N → pcode x = E k → inI MK k = true →
      x ^ 2 = 1 := fun hk hx hik => ((inv_sound hn (hi _ hk) hx).1 hik).2
  have hsqab : (xa * xb) ^ 2 = 1 := by
    rw [Commute.mul_pow hcab, hsq ha' hxa hia, hsq hb' hxb hib, one_mul]
  have hiab := (inv_sound hn (hi _ hab') heab).2 ⟨h0ab, hsqab⟩
  have Cabc := cell_sound hn (hp _ hab') hiab hc' heab hxc
  obtain ⟨habc', -⟩ := Cabc.2 hic (Commute.mul_left hcac hcbc)
  refine ⟨_, hnd', rfl, ?_, beq_true_iff.1 hM⟩
  intro k hk
  rw [spanL_eq] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.zero_lt_of_lt ha'
  all_goals assumption

theorem mset_ncard (hn : n ≤ 32) {T : Subgroup (Perm (Fin n))} {N : ℕ} {E : ℕ → ℕ}
    (hE : ExactList pcode T N E) {L : List ℕ} (hL : ∀ k ∈ L, k < N) (hnd : L.Nodup) :
    (mset n E N (maskL L)).ncard = L.length := by
  classical
  choose! f hfT hf using hE.1
  have hset : mset n E N (maskL L) = f '' {k | k ∈ L} := by
    ext x
    simp only [mset, bit_maskL, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨k, hk, hkL, hx⟩
      exact ⟨k, hkL, (pcode_inj hn).1 ((hf k hk).trans hx.symm)⟩
    · rintro ⟨k, hkL, rfl⟩
      exact ⟨k, hL k hkL, hkL, hf k (hL k hkL)⟩
  have hL' : {k | k ∈ L} = (L.toFinset : Set ℕ) := by
    ext
    simp
  have hinj : Set.InjOn f {k | k ∈ L} := by
    intro i hi j hj hij
    exact hE.2.2 i (hL i hi) j (hL j hj)
      ((hf i (hL i hi)).symm.trans ((congrArg pcode hij).trans (hf j (hL j hj))))
  rw [hset, hinj.ncard_image, hL', Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

theorem gensK_mem (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
    (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {S : Set (Perm (Fin n))} {B : ℕ → ℕ}
    {k : ℕ} (hB : ∀ i < k, ∃ y ∈ S, pcode y = B i) {ws : List (List ℕ)}
    (h : gensK n A gs.length B k ws = true) :
    ∀ j < gs.length, gs.getD j 1 ∈ Subgroup.closure S := by
  classical
  choose! f hfS hfe using hB
  let ys : List (Perm (Fin n)) := (List.range k).map f
  have hlen : ys.length = k := by simp [ys]
  have hB' : ∀ i < ys.length, B i = pcode (ys.getD i 1) := by
    intro i hi
    rw [hlen] at hi
    simp [ys, List.getD_eq_getElem?_getD, hi, hfe i hi]
  intro j hj
  obtain ⟨h1, h2⟩ := andB_iff.1 ((allN_iff _ _).1 h j hj)
  rw [← hlen] at h1 h2
  obtain ⟨g, hg, he⟩ := word_mem hn ys hB' h1
  rw [← (pcode_inj hn).1 (he.trans ((beq_true_iff.1 h2).trans (hA j hj)))]
  refine Subgroup.closure_mono ?_ hg
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  exact hfS i (List.mem_range.1 hi)

theorem s0_exact (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
    (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {nG N : ℕ} {sw : ℕ → List ℕ}
    {G E PA SG CT : ℕ → ℕ} (hN : 0 < N)
    (hg : ∀ l < nG, wordAt n A gs.length sw G l = true)
    (ht : ∀ k < N, treeAt (P.mul n) (P.one n) G nG E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true)
    (hc : ∀ k < N, closedAt (P.mul n) G nG N E CT k = true) :
    ∃ T : Subgroup (Perm (Fin n)), T ≤ Subgroup.closure {g | g ∈ gs} ∧ Nat.card T = N ∧
      ExactList pcode T N E := by
  classical
  have hw : ∀ l < nG, ∃ g ∈ Subgroup.closure {g | g ∈ gs}, pcode g = G l := by
    intro l hl
    obtain ⟨h1, h2⟩ := andB_iff.1 (hg l hl)
    obtain ⟨g, hg, he⟩ := word_mem hn gs hA h1
    exact ⟨g, hg, he.trans (beq_true_iff.1 h2)⟩
  choose! f hfQ hfe using hw
  let sgs : List (Perm (Fin n)) := (List.range nG).map f
  have hlen : sgs.length = nG := by simp [sgs]
  have hget : ∀ j < nG, sgs.getD j 1 = f j := by
    intro j hj
    simp [sgs, List.getD_eq_getElem?_getD, hj]
  have hG : ∀ j < sgs.length, G j = pcode (sgs.getD j 1) := by
    intro j hj
    rw [hlen] at hj
    rw [hget j hj, hfe j hj]
  have ht' : ∀ k < N, treeAt (P.mul n) (P.one n) G sgs.length E PA k = true := by
    rw [hlen]
    exact ht
  have hc' : ∀ k < N, closedAt (P.mul n) G sgs.length N E CT k = true := by
    rw [hlen]
    exact hc
  have clos := clos_card (pcode_enc hn) sgs hG hN ht' hs
  refine ⟨Subgroup.closure {g | g ∈ sgs}, ?_, (clos.2.2 hc').1,
    ⟨clos.1, (clos.2.2 hc').2, sort_distinct hs⟩⟩
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact hfQ j (List.mem_range.1 hj)

theorem tri_sound (hn : n ≤ 32) {T : Subgroup (Perm (Fin n))} {N : ℕ} {E MK R : ℕ → ℕ}
    {W : List Wit} {A : ℕ → ℕ} {nA s : ℕ} (hE : ExactList pcode T N E) (hE0 : E 0 = P.one n)
    (hi : ∀ k < N, invAt n E MK k = true) (hp : ∀ a < N, pairAt n N E MK R a = true)
    (htr : ∀ a < N, triAt N MK R W a = true)
    (hw : ∀ w ∈ W, witAt n A nA s N E MK R w = true)
    {a b c : Perm (Fin n)} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (ha2 : a ^ 2 = 1)
    (hb2 : b ^ 2 = 1) (hc2 : c ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ∉ [1, a])
    (hc1 : c ∉ [1, a, b, a * b]) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) :
    ∃ w ∈ W, a ∈ mset n E N (Wit.mask w) ∧ b ∈ mset n E N (Wit.mask w) ∧
      c ∈ mset n E N (Wit.mask w) ∧
      (∀ x ∈ mset n E N (Wit.mask w), x ∈ Subgroup.closure ({a, b, c} : Set (Perm (Fin n)))) ∧
      (∀ x ∈ T, x ^ 2 = 1 → x * a = a * x → x * b = b * x → x * c = c * x →
        x ∈ mset n E N (Wit.mask w)) ∧
      (mset n E N (Wit.mask w) : Set (Perm (Fin n))).ncard = 8 := by
  classical
  obtain ⟨pa, hpa, hea⟩ := hE.2.1 a ha
  obtain ⟨pb, hpb, heb⟩ := hE.2.1 b hb
  obtain ⟨pc, hpc, hec⟩ := hE.2.1 c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb1 hc1
  obtain ⟨hb1', hba⟩ := hb1
  obtain ⟨hc1', hca, hcb, hcab⟩ := hc1
  have he1 : pcode (1 : Perm (Fin n)) = E 0 := (hE0.trans (pcode_one hn)).symm
  have hpos : ∀ {k : ℕ} {x : Perm (Fin n)}, k < N → pcode x = E k → x ≠ 1 → 0 < k := by
    intro k x hk hx hx1
    refine Nat.pos_of_ne_zero fun h0 => hx1 ((pcode_inj hn).1 ?_)
    rw [hx, h0, he1]
  have hinv : ∀ {k : ℕ} {x : Perm (Fin n)}, k < N → pcode x = E k → x ≠ 1 → x ^ 2 = 1 →
      inI MK k = true := fun hk hx hx1 hx2 =>
    (inv_sound hn (hi _ hk) hx).2 ⟨hpos hk hx hx1, hx2⟩
  have hne : ∀ {i j : ℕ} {x y : Perm (Fin n)}, i < N → j < N → pcode x = E i → pcode y = E j →
      x ≠ y → i ≠ j := fun hi' hj' hx hy hxy h => hxy ((pos_eq hn hE hi' hj' hx hy).2 h)
  have hia := hinv hpa hea ha1 ha2
  have hib := hinv hpb heb hb1' hb2
  have hic := hinv hpc hec hc1' hc2
  have Cab := cell_sound hn (hp pa hpa) hia hpb hea heb
  have Cac := cell_sound hn (hp pa hpa) hia hpc hea hec
  have Cbc := cell_sound hn (hp pb hpb) hib hpc heb hec
  obtain ⟨hpab, heab⟩ := Cab.2 hib hab
  obtain ⟨hpac, heac⟩ := Cac.2 hic hac
  obtain ⟨hpbc, hebc⟩ := Cbc.2 hic hbc
  have hab1 : a * b ≠ 1 := by
    intro h
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])
    exact hba (h1.trans h2)
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [Commute.mul_pow hab, ha2, hb2, one_mul]
  have hiab := hinv hpab heab hab1 hab2
  have Cabc := cell_sound hn (hp _ hpab) hiab hpc heab hec
  obtain ⟨hpabc, heabc⟩ := Cabc.2 hic (Commute.mul_left (hac : Commute a c) hbc)
  have ht := impB_iff.1 (htr pa hpa) hia
  simp only [triAt, letB_eq, impB_iff, allN_iff, andB_iff, notB_iff, orB_iff, beq_true_iff,
    anyW_iff, bit_land] at ht
  obtain ⟨hXS, w, hwW, hwS⟩ := ht pb hpb ⟨Cab.1.2 ⟨hib, hab⟩, hne hpb hpa heb hea hba⟩ pc hpc
    ⟨⟨Cac.1.2 ⟨hic, hac⟩, Cbc.1.2 ⟨hic, hbc⟩⟩, by
      rintro (h | h | h)
      · exact hne hpc hpa hec hea hca h
      · exact hne hpc hpb hec heb hcb h
      · exact hne hpc hpab hec heab hcab h⟩
  have memS : ∀ k, bit (Wit.mask w) k = true ↔ k ∈ [0, pa, pb, pc, fd (R pa) pb, fd (R pa) pc,
      fd (R pb) pc, fd (R (fd (R pa) pb)) pc] := by
    intro k
    rw [hwS, bit_maskL, spanL_eq]
  have inM : ∀ {k : ℕ} {x : Perm (Fin n)}, k < N → pcode x = E k →
      k ∈ [0, pa, pb, pc, fd (R pa) pb, fd (R pa) pc, fd (R pb) pc, fd (R (fd (R pa) pb)) pc] →
      x ∈ mset n E N (Wit.mask w) := fun hk hx hkL => ⟨_, hk, (memS _).2 hkL, hx⟩
  refine ⟨w, hwW, inM hpa hea (by simp), inM hpb heb (by simp), inM hpc hec (by simp), ?_, ?_, ?_⟩
  · rintro x ⟨k, hk, hbk, hxk⟩
    rw [memS] at hbk
    have key : ∀ {y : Perm (Fin n)}, pcode y = E k → x = y := fun hy =>
      (pcode_inj hn).1 (hxk.trans hy.symm)
    have hsa : a ∈ Subgroup.closure ({a, b, c} : Set (Perm (Fin n))) :=
      Subgroup.subset_closure (by simp)
    have hsb : b ∈ Subgroup.closure ({a, b, c} : Set (Perm (Fin n))) :=
      Subgroup.subset_closure (by simp)
    have hsc : c ∈ Subgroup.closure ({a, b, c} : Set (Perm (Fin n))) :=
      Subgroup.subset_closure (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbk
    rcases hbk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [key he1]
      exact Subgroup.one_mem _
    · rw [key hea]
      exact hsa
    · rw [key heb]
      exact hsb
    · rw [key hec]
      exact hsc
    · rw [key heab]
      exact Subgroup.mul_mem _ hsa hsb
    · rw [key heac]
      exact Subgroup.mul_mem _ hsa hsc
    · rw [key hebc]
      exact Subgroup.mul_mem _ hsb hsc
    · rw [key heabc]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsa hsb) hsc
  · intro x hx hx2 hxa hxb hxc
    obtain ⟨k, hk, hxk⟩ := hE.2.1 x hx
    by_cases hx1 : x = 1
    · subst hx1
      exact inM (Nat.zero_lt_of_lt hpa) he1 (by simp)
    · have hik := hinv hk hxk hx1 hx2
      have h1 := (cell_sound hn (hp pa hpa) hia hk hea hxk).1.2 ⟨hik, hxa.symm⟩
      have h2 := (cell_sound hn (hp pb hpb) hib hk heb hxk).1.2 ⟨hik, hxb.symm⟩
      have h3 := (cell_sound hn (hp pc hpc) hic hk hec hxk).1.2 ⟨hik, hxc.symm⟩
      refine ⟨k, hk, ?_, hxk⟩
      have hX := (bit_land _ _ k).2 ⟨(bit_land _ _ k).2 ⟨h1, h2⟩, h3⟩
      rw [← hXS, bit_land] at hX
      rw [hwS]
      exact hX.2
  · obtain ⟨L, hnd, hlen, hLN, hm⟩ := wit_span hn hE hi hp (hw w hwW)
    rw [hm, mset_ncard hn hE hLN hnd, hlen]

theorem wit_sound (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
    (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {s N : ℕ} {E MK R : ℕ → ℕ}
    {T : Subgroup (Perm (Fin n))} (hE : ExactList pcode T N E) (hE0 : E 0 = P.one n)
    (hi : ∀ k < N, invAt n E MK k = true) (hp : ∀ a < N, pairAt n N E MK R a = true) {w : Wit}
    (h : witAt n A gs.length s N E MK R w = true) :
    (∀ j < gs.length, gs.getD j 1 ∈ Subgroup.closure {y | y ∈ Subgroup.closure {g | g ∈ gs} ∧
      ∃ x ∈ mset n E N (Wit.mask w), x ≠ 1 ∧ y * x = x * y}) ∧
    (∀ j < gs.length, gs.getD j 1 ∈ Subgroup.closure {y | ∃ x ∈ mset n E N (Wit.mask w),
      ∃ g ∈ Subgroup.closure {g | g ∈ gs}, y = g * x * g⁻¹}) ∧
    (∀ x ∈ mset n E N (Wit.mask w), x ≠ 1 →
      ∃ t ∈ Subgroup.closure {g | g ∈ gs}, t ≠ 1 ∧ t ^ 3 = 1 ∧ t * x = x * t) ∧
    (∃ o ∈ mset n E N (Wit.mask w), ∃ u : List ℕ, lettersK gs.length u = true ∧
      pcode o = wordK n A gs.length u ∧ oddW gs.length s u = true) := by
  classical
  obtain ⟨L, -, -, hLN, hmask⟩ := wit_span hn hE hi hp h
  have hbitN : ∀ k, bit (Wit.mask w) k = true → k < N := fun k hk =>
    hLN k ((bit_maskL L k).1 (hmask ▸ hk))
  have helt : ∀ k, bit (Wit.mask w) k = true →
      ∃ x ∈ mset n E N (Wit.mask w), pcode x = E k := by
    intro k hk
    obtain ⟨x, -, hx⟩ := hE.1 k (hbitN k hk)
    exact ⟨x, ⟨k, hbitN k hk, hk, hx⟩, hx⟩
  have he1 : pcode (1 : Perm (Fin n)) = E 0 := (hE0.trans (pcode_one hn)).symm
  have hne1 : ∀ {k : ℕ} {x : Perm (Fin n)}, k < N → pcode x = E k → 0 < k → x ≠ 1 := by
    intro k x hk hx h0 h1
    have h := hE.2.2 k hk 0 (Nat.zero_lt_of_lt hk) (by rw [← hx, h1, he1])
    omega
  obtain ⟨⟨a, b, c, o, M⟩, ⟨cent, cw⟩, ⟨cj, jw⟩, ⟨three, ow⟩⟩ := w
  simp only [witAt, letB_eq, andB_iff] at h
  obtain ⟨-, -, -, hcent, hgc, hcj, hgj, hthree, hcov, hoM, hol, how, hodd⟩ := h
  refine ⟨gensK_mem hn gs hA (fun i hi => ?_) hgc, gensK_mem hn gs hA (fun i hi => ?_) hgj,
    ?_, ?_⟩
  · obtain ⟨hb, h0, hl, hc⟩ := (And.imp_right (fun h => And.imp_right andB_iff.1 (andB_iff.1 h))
      (andB_iff.1 ((allP_iff _ _).1 hcent cent[i] (List.getElem_mem hi))))
    obtain ⟨y, hyQ, hy⟩ := word_mem hn gs hA hl
    obtain ⟨x, hx, hxe⟩ := helt _ hb
    refine ⟨y, ⟨hyQ, x, hx, hne1 (hbitN _ hb) hxe (Nat.blt_eq.mp h0), ?_⟩, ?_⟩
    · rw [← hxe, ← hy, comm_iff hn] at hc
      exact hc.symm
    · rw [nthP_get _ _ hi, hy]
  · obtain ⟨hb, hl⟩ := andB_iff.1 ((allP_iff _ _).1 hcj cj[i] (List.getElem_mem hi))
    obtain ⟨g, hgQ, hg⟩ := word_mem hn gs hA hl
    obtain ⟨x, hx, hxe⟩ := helt _ hb
    refine ⟨g * x * g⁻¹, ⟨x, hx, g, hgQ, rfl⟩, ?_⟩
    rw [nthP_get _ _ hi]
    change pcode _ = P.mul n (P.mul n _ _) (P.inv n _)
    rw [← hg, ← hxe, pcode_inv hn, pcode_mul hn, pcode_mul hn]
  · rintro x ⟨k, hk, hbk, hxk⟩ hx1
    have h0 : 0 < k := Nat.pos_of_ne_zero fun h0 => hx1 ((pcode_inj hn).1 (by rw [hxk, h0, he1]))
    obtain ⟨p, hp3, hpk⟩ := (anyP_iff _ _).1 (impB_iff.1 ((allN_iff _ _).1 hcov k hk)
      (andB_iff.2 ⟨hbk, Nat.blt_eq.mpr h0⟩))
    have h3 := (allP_iff _ _).1 hthree p hp3
    simp only [letB_eq, andB_iff, notB_iff] at h3
    obtain ⟨-, hl, ht1, ht3, htc⟩ := h3
    obtain ⟨t, htQ, ht⟩ := word_mem hn gs hA hl
    rw [beq_true_iff.1 hpk] at htc
    rw [← ht, ← hxk, comm_iff hn] at htc
    rw [← ht, pcode_one hn, beq_iff hn] at ht1
    rw [← ht, pcode_mul hn, pcode_mul hn, pcode_one hn, beq_iff hn] at ht3
    exact ⟨t, htQ, ht1, by rw [pow_three]; exact ht3, htc.symm⟩
  · obtain ⟨x, hx, hxe⟩ := helt o hoM
    exact ⟨x, hx, ow, hol, hxe.trans (beq_true_iff.1 how).symm, hodd⟩

theorem exists_e8Triple (A : Subgroup (Perm (Fin n)))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hA8 : 8 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
      a ≠ 1 ∧ b ∉ [1, a] ∧ c ∉ [1, a, b, a * b] ∧
        a * b = b * a ∧ a * c = c * a ∧ b * c = c * b := by
  classical
  have hAexp : ∀ g : A, g ^ 2 = 1 := fun g => Subtype.ext (by simpa using hA2 g g.2)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    CFSG.commute_of_sq_eq_one (hA2 x hx) (hA2 y hy) (hA2 _ (A.mul_mem hx hy))
  have hApg : IsPGroup 2 A := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    exact ⟨1, by simpa using hAexp g⟩
  obtain ⟨k, hk⟩ := hApg.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have hk2 : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  obtain ⟨H, hHcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 (n := 3)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 hk3)
  let S : Subgroup (Perm (Fin n)) := H.map A.subtype
  have hScard : Nat.card S = 8 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hHcard]
    norm_num
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    exact hcomm x' x'.2 y' y'.2
  have hSsq : ∀ x ∈ S, x * x = 1 := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    simpa [pow_two] using hA2 x' x'.2
  obtain ⟨a, b, c, haS, hbS, hcS, ha1, hb, hc, -⟩ :=
    CFSG.OddStandard.SmallF3.Omega.exists_basis_three S hScard hScomm hSsq
  have haA : a ∈ A := Subgroup.map_subtype_le H haS
  have hbA : b ∈ A := Subgroup.map_subtype_le H hbS
  have hcA : c ∈ A := Subgroup.map_subtype_le H hcS
  refine ⟨a, haA, b, hbA, c, hcA, ha1, ?_, ?_, hcomm a haA b hbA, hcomm a haA c hcA,
    hcomm b hbA c hcA⟩
  · simpa [CFSG.OddStandard.SmallF3.Omega.adjoinL] using hb
  · have hlist : CFSG.OddStandard.SmallF3.Omega.adjoinL b
        (CFSG.OddStandard.SmallF3.Omega.adjoinL a [1]) = [1, a, b, a * b] := by
      simp [CFSG.OddStandard.SmallF3.Omega.adjoinL, hcomm b hbA a haA]
    rwa [hlist] at hc

theorem exists_wit (hn : n ≤ 32) {T : Subgroup (Perm (Fin n))} {N : ℕ} {E MK R : ℕ → ℕ}
    {W : List Wit} {A : ℕ → ℕ} {nA s : ℕ} (hE : ExactList pcode T N E) (hE0 : E 0 = P.one n)
    (hi : ∀ k < N, invAt n E MK k = true) (hp : ∀ a < N, pairAt n N E MK R a = true)
    (htr : ∀ a < N, triAt N MK R W a = true)
    (hw : ∀ w ∈ W, witAt n A nA s N E MK R w = true)
    {B : Subgroup (Perm (Fin n))} (hBT : B ≤ T) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hB8 : 8 ≤ Nat.card B) :
    ∃ w ∈ W, (B : Set (Perm (Fin n))) = mset n E N (Wit.mask w) ∧ Nat.card B = 8 := by
  obtain ⟨a, ha, b, hb, c, hc, ha1, hb1, hc1, hab, hac, hbc⟩ := exists_e8Triple B hB2 hB8
  obtain ⟨w, hwW, -, -, -, hsub, hall, hcard⟩ := tri_sound hn hE hE0 hi hp htr hw (hBT ha)
    (hBT hb) (hBT hc) (hB2 a ha) (hB2 b hb) (hB2 c hc) ha1 hb1 hc1 hab hac hbc
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    CFSG.commute_of_sq_eq_one (hB2 x hx) (hB2 y hy) (hB2 _ (B.mul_mem hx hy))
  have hset : (B : Set (Perm (Fin n))) = mset n E N (Wit.mask w) := by
    ext x
    constructor
    · intro hx
      exact hall x (hBT hx) (hB2 x hx) (hcomm x hx a ha) (hcomm x hx b hb) (hcomm x hx c hc)
    · intro hx
      have h1 := hsub x hx
      have hle : Subgroup.closure ({a, b, c} : Set (Perm (Fin n))) ≤ B := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hc
      exact hle h1
  refine ⟨w, hwW, hset, ?_⟩
  have h1 : Nat.card B = (B : Set (Perm (Fin n))).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, hcard]

theorem e8Facts_of_set {gs : List (Perm (Fin n))} {Q : Subgroup (Perm (Fin n))}
    (hQ : Subgroup.closure {g | g ∈ gs} = Q) {X : Set (Perm (Fin n))} {A : Subgroup ↥Q}
    (hAX : ∀ x, x ∈ A.map Q.subtype ↔ x ∈ X) (hcard : Nat.card A = 8)
    (h1 : ∀ j < gs.length, gs.getD j 1 ∈ Subgroup.closure {y | y ∈ Q ∧
      ∃ x ∈ X, x ≠ 1 ∧ y * x = x * y})
    (h2 : ∀ j < gs.length, gs.getD j 1 ∈ Subgroup.closure {y | ∃ x ∈ X, ∃ g ∈ Q, y = g * x * g⁻¹})
    (h3 : ∀ x ∈ X, x ≠ 1 → ∃ t ∈ Q, t ≠ 1 ∧ t ^ 3 = 1 ∧ t * x = x * t) :
    CFSG.GroupTheory.E8Facts ↥Q A := by
  classical
  have hgs : ∀ g ∈ gs, ∃ j < gs.length, gs.getD j 1 = g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]⟩
  have htop : ∀ H : Subgroup ↥Q, (∀ j < gs.length, gs.getD j 1 ∈ H.map Q.subtype) → H = ⊤ := by
    intro H hH
    have hle0 : Subgroup.closure {g | g ∈ gs} ≤ H.map Q.subtype := by
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨j, hj, rfl⟩ := hgs g hg
      exact hH j hj
    have hle : Q ≤ H.map Q.subtype := hQ.symm.trans_le hle0
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hle x.2)
    rwa [show y = x from Subtype.ext (by simpa using hyx)] at hy
  have hX : ∀ x ∈ X, ∃ a ∈ A, (a : Perm (Fin n)) = x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp ((hAX x).2 hx)
    exact ⟨a, ha, hax⟩
  refine ⟨hcard, ?_, ?_, ?_⟩
  · apply htop
    intro j hj
    refine (Subgroup.closure_le _).2 ?_ (h1 j hj)
    rintro y ⟨hyQ, x, hx, hx1, hyx⟩
    obtain ⟨a, haA, rfl⟩ := hX x hx
    have ha1 : a ≠ 1 := fun h => hx1 (by rw [h]; rfl)
    have hmem : (⟨y, hyQ⟩ : ↥Q) ∈ Subgroup.centralizer ({a} : Set ↥Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subtype.ext hyx.symm
    exact Subgroup.mem_map_of_mem Q.subtype (Subgroup.mem_iSup_of_mem (x := (⟨y, hyQ⟩ : ↥Q)) a
      (Subgroup.mem_iSup_of_mem (x := (⟨y, hyQ⟩ : ↥Q)) haA
        (Subgroup.mem_iSup_of_mem (x := (⟨y, hyQ⟩ : ↥Q)) ha1 hmem)))
  · apply htop
    intro j hj
    refine (Subgroup.closure_le _).2 ?_ (h2 j hj)
    rintro y ⟨x, hx, g, hg, rfl⟩
    obtain ⟨a, haA, rfl⟩ := hX x hx
    let h : ↥Q := ⟨g, hg⟩
    have hmem : h * a * h⁻¹ ∈ Subgroup.normalClosure (A : Set ↥Q) :=
      Subgroup.normalClosure_normal.conj_mem a (Subgroup.subset_normalClosure haA) h
    exact Subgroup.mem_map_of_mem Q.subtype hmem
  · intro a haA ha1
    have hx : (a : Perm (Fin n)) ∈ X := (hAX _).1 (Subgroup.mem_map_of_mem Q.subtype haA)
    have hxa : (a : Perm (Fin n)) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨t, htQ, ht1, ht3, htc⟩ := h3 _ hx hxa
    let t' : ↥Q := ⟨t, htQ⟩
    have htord : orderOf t' = 3 := by
      rw [Subgroup.orderOf_mk t htQ]
      exact orderOf_eq_prime ht3 ht1
    have htmem : t' ∈ Subgroup.centralizer ({a} : Set ↥Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subtype.ext htc.symm
    have := Subgroup.orderOf_dvd_natCard (Subgroup.centralizer ({a} : Set ↥Q)) htmem
    rwa [htord] at this

theorem exists_sylow {Q T : Subgroup (Perm (Fin n))} {N N0 : ℕ} (hTQ : T ≤ Q)
    (hcardT : Nat.card T = N) (hpow : N = 2 ^ Nat.log 2 N) (hQ : Nat.card Q = N0)
    (hodd : N0 / N % 2 = 1) :
    ∃ S : Sylow 2 ↥Q, (S : Subgroup ↥Q) = T.subgroupOf Q := by
  have hcardS : Nat.card (T.subgroupOf Q) = N := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, hcardT]
  have hS2 : IsPGroup 2 (T.subgroupOf Q) := IsPGroup.of_card (by rw [hcardS, ← hpow])
  have hindex : (T.subgroupOf Q).index = N0 / N := by
    rw [Subgroup.index_eq_card_div, hcardS, hQ]
  have hodd' : ¬ 2 ∣ (T.subgroupOf Q).index := by
    rw [hindex]
    intro hd
    have h0 : N0 / N % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  exact ⟨hS2.toSylow hodd', IsPGroup.toSylow_coe hS2 hodd'⟩

section Assembly

variable (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
  (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {s nG N N0 : ℕ} {sw : ℕ → List ℕ}
  {G E PA SG CT MK R : ℕ → ℕ} {W : List Wit}
  (hN : 0 < N) (hpow : N = 2 ^ Nat.log 2 N)
  (hQ : Nat.card (Subgroup.closure {g | g ∈ gs}) = N0) (hodd : N0 / N % 2 = 1)
  (hg : ∀ l < nG, wordAt n A gs.length sw G l = true)
  (ht : ∀ k < N, treeAt (P.mul n) (P.one n) G nG E PA k = true)
  (hs : ∀ i < N, sortAt N E SG i = true)
  (hc : ∀ k < N, closedAt (P.mul n) G nG N E CT k = true)
  (hi : ∀ k < N, invAt n E MK k = true) (hp : ∀ a < N, pairAt n N E MK R a = true)
  (htr : ∀ a < N, triAt N MK R W a = true)
  (hw : allW W (witAt n A gs.length s N E MK R) = true)

include hn hA hN hpow hQ hodd hg ht hs hc hi hp htr hw

theorem e8GenFacts_of_checks :
    CFSG.GroupTheory.E8GenFacts ↥(Subgroup.closure {g | g ∈ gs}) := by
  classical
  set Q := Subgroup.closure {g | g ∈ gs} with hQdef
  obtain ⟨T, hTQ, hcardT, hE⟩ := s0_exact hn gs hA hN hg ht hs hc
  have hE0 : E 0 = P.one n := Nat.eq_of_beq_eq_true (ht 0 hN)
  have hw' := (allW_iff _ _).1 hw
  obtain ⟨S, hS⟩ := exists_sylow hTQ hcardT hpow hQ hodd
  refine CFSG.GroupTheory.E8GenFacts.of_sylow S ?_
  intro A' hAS hA2 hA8
  have hAS' : A' ≤ T.subgroupOf Q := by rwa [← hS]
  let B : Subgroup (Perm (Fin n)) := A'.map Q.subtype
  have hBT : B ≤ T := by
    calc B ≤ (T.subgroupOf Q).map Q.subtype := Subgroup.map_mono hAS'
      _ = T := Subgroup.map_subgroupOf_eq_of_le hTQ
  have hB2 : ∀ x ∈ B, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa using congrArg (fun y : ↥Q => (y : Perm (Fin n))) (hA2 a ha)
  have hBcard : Nat.card B = Nat.card A' := Subgroup.card_subtype Q A'
  obtain ⟨w, hwW, hset, hB8⟩ := exists_wit hn hE hE0 hi hp htr hw' hBT hB2 (by rw [hBcard]; exact hA8)
  obtain ⟨h1, h2, h3, -⟩ := wit_sound hn gs hA hE hE0 hi hp (hw' w hwW)
  exact e8Facts_of_set rfl (X := mset n E N (Wit.mask w)) (fun x => by
    rw [← hset]; rfl) (by rw [← hBcard]; exact hB8) h1 h2 h3

theorem not_le_of_checks {K : Subgroup (Perm (Fin n))} (hs' : s < gs.length)
    (hPQ : ∀ g ∈ Subgroup.closure {g | g ∈ gs}, ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (hgP : ∀ j < gs.length, j ≠ s → gs.getD j 1 ∈ K) (hsP : gs.getD s 1 ∉ K)
    (h2 : ∀ x ∈ Subgroup.closure {g | g ∈ gs}, ∀ y ∈ Subgroup.closure {g | g ∈ gs},
      x ∉ K → y ∉ K → x * y ∈ K)
    (B : Subgroup (Perm (Fin n))) (hBQ : B ≤ Subgroup.closure {g | g ∈ gs})
    (hB : ∀ b ∈ B, b ^ 2 = 1) (h8 : 8 ≤ Nat.card B) : ¬ B ≤ K := by
  classical
  set Q := Subgroup.closure {g | g ∈ gs} with hQdef
  obtain ⟨T, hTQ, hcardT, hE⟩ := s0_exact hn gs hA hN hg ht hs hc
  have hE0 : E 0 = P.one n := Nat.eq_of_beq_eq_true (ht 0 hN)
  have hw' := (allW_iff _ _).1 hw
  obtain ⟨S, hScoe⟩ := exists_sylow hTQ hcardT hpow hQ hodd
  let BQ : Subgroup ↥Q := B.subgroupOf Q
  have hBQ2 : IsPGroup 2 BQ := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro b
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hbB : (b : Perm (Fin n)) ∈ B := (Subgroup.mem_subgroupOf).mp b.2
    simpa using hB _ hbB
  obtain ⟨S', hBQle⟩ := hBQ2.exists_le_sylow
  obtain ⟨g, hg'⟩ := MulAction.exists_smul_eq (↥Q) S' S
  let B' : Subgroup (Perm (Fin n)) := B.map (MulAut.conj (g : Perm (Fin n))).toMonoidHom
  have hB'leT : B' ≤ T := by
    intro x hx
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hx
    have hbQ : b ∈ Q := hBQ hbB
    let bQ : ↥Q := ⟨b, hbQ⟩
    have hbQBQ : bQ ∈ BQ := (Subgroup.mem_subgroupOf).mpr hbB
    have hconjBQ : MulAut.conj g bQ ∈ (S : Subgroup ↥Q) := by
      have h1 : MulAut.conj g bQ ∈ MulAut.conj g • (S' : Subgroup ↥Q) :=
        Subgroup.mem_map_of_mem _ (hBQle hbQBQ)
      rwa [← Sylow.coe_subgroup_smul, hg'] at h1
    have hxT : ((MulAut.conj g bQ : ↥Q) : Perm (Fin n)) ∈ T := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hTQ, ← hScoe]
      exact Subgroup.mem_map_of_mem Q.subtype hconjBQ
    have hval : ((MulAut.conj g bQ : ↥Q) : Perm (Fin n)) =
        (g : Perm (Fin n)) * b * (g : Perm (Fin n))⁻¹ := by
      simp [bQ]
    rwa [hval] at hxT
  have hB'2 : ∀ x ∈ B', x ^ 2 = 1 := by
    intro x hx
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hx
    have hb2 : b * b = 1 := by simpa [pow_two] using hB b hbB
    change ((g : Perm (Fin n)) * b * (g : Perm (Fin n))⁻¹) ^ 2 = 1
    rw [pow_two]
    calc ((g : Perm (Fin n)) * b * (g : Perm (Fin n))⁻¹) *
          ((g : Perm (Fin n)) * b * (g : Perm (Fin n))⁻¹) =
        (g : Perm (Fin n)) * (b * b) * (g : Perm (Fin n))⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hB'card : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj (g : Perm (Fin n))).injective
  obtain ⟨w, hwW, hset, -⟩ :=
    exists_wit hn hE hE0 hi hp htr hw' hB'leT hB'2 (by rw [hB'card]; exact h8)
  obtain ⟨-, -, -, o, ho, u, hu, hou, hodd'⟩ := wit_sound hn gs hA hE hE0 hi hp (hw' w hwW)
  intro hBP
  have hB'P : B' ≤ K := by
    intro x hx
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hx
    exact hPQ (g : Perm (Fin n)) g.2 b (hBP hbB)
  have hoP : o ∈ K := hB'P (by rw [← SetLike.mem_coe, hset]; exact ho)
  have hpar : ∀ u : List ℕ, lettersK gs.length u = true →
      ∃ x ∈ Q, pcode x = wordK n A gs.length u ∧ (x ∈ K ↔ oddW gs.length s u = false) := by
    intro u
    induction u with
    | nil => exact fun _ => ⟨1, Q.one_mem, (pcode_enc hn).enc_one, by simp [oddW, K.one_mem]⟩
    | cons l u ih =>
      intro hl
      change andB (Nat.blt l (gs.length + gs.length)) (lettersK gs.length u) = true at hl
      obtain ⟨hl1, hl2⟩ := andB_iff.1 hl
      have hl' : l < gs.length + gs.length := Nat.blt_eq.mp hl1
      obtain ⟨x, hxQ, hxc, hxP⟩ := ih hl2
      have hmem : ∀ a < gs.length, gs.getD a 1 ∈ Q := fun a ha =>
        Subgroup.subset_closure (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
          exact List.getElem_mem ha)
      obtain ⟨y, hyQ, hyc, hyP⟩ : ∃ y ∈ Q, pcode y = letterK n A gs.length l ∧
          (y ∈ K ↔ (Nat.beq l s || Nat.beq l (s + gs.length)) = false) := by
        unfold letterK
        cases hb : Nat.blt l gs.length
        · have hge : gs.length ≤ l := Nat.not_lt.1 fun h => by
            rw [Nat.blt_eq.mpr h] at hb
            cases hb
          have hlt : l - gs.length < gs.length := by omega
          refine ⟨(gs.getD (l - gs.length) 1)⁻¹, Q.inv_mem (hmem _ hlt), ?_, ?_⟩
          · change pcode _ = P.inv n (A (l - gs.length))
            rw [hA _ hlt, pcode_inv hn]
          · rw [inv_mem_iff]
            by_cases hj : l - gs.length = s
            · have : Nat.beq l (s + gs.length) = true := beq_true_iff.2 (by omega)
              simp only [this, Bool.or_true, Bool.true_eq_false, iff_false]
              rw [hj]
              exact hsP
            · have h1 : Nat.beq l s = false := by
                cases h : Nat.beq l s
                · rfl
                · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
              have h2' : Nat.beq l (s + gs.length) = false := by
                cases h : Nat.beq l (s + gs.length)
                · rfl
                · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
              simp only [h1, h2', Bool.or_false, iff_true]
              exact hgP _ hlt hj
        · have hlt : l < gs.length := Nat.blt_eq.mp hb
          refine ⟨gs.getD l 1, hmem l hlt, (hA l hlt).symm, ?_⟩
          have h2' : Nat.beq l (s + gs.length) = false := by
            cases h : Nat.beq l (s + gs.length)
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
          by_cases hj : l = s
          · subst hj
            simp only [Nat.beq_refl, Bool.true_or, Bool.true_eq_false, iff_false]
            exact hsP
          · have h1 : Nat.beq l s = false := by
              cases h : Nat.beq l s
              · rfl
              · exact absurd (Nat.eq_of_beq_eq_true h) hj
            simp only [h1, h2', Bool.or_false, iff_true]
            exact hgP _ hlt hj
      refine ⟨y * x, Q.mul_mem hyQ hxQ, ?_, ?_⟩
      · change pcode (y * x) = P.mul n (letterK n A gs.length l) (wordK n A gs.length u)
        rw [(pcode_enc hn).enc_mul, hyc, hxc]
      · change y * x ∈ K ↔ Bool.rec (motive := fun _ => Bool) (oddW gs.length s u)
          (notB (oddW gs.length s u)) (orB (Nat.beq l s) (Nat.beq l (s + gs.length))) = false
        have hor : orB (Nat.beq l s) (Nat.beq l (s + gs.length)) =
            (Nat.beq l s || Nat.beq l (s + gs.length)) := by
          cases Nat.beq l s <;> rfl
        rw [hor]
        cases hb : (Nat.beq l s || Nat.beq l (s + gs.length))
        · rw [hb] at hyP
          have hy : y ∈ K := hyP.2 rfl
          change y * x ∈ K ↔ oddW gs.length s u = false
          rw [← hxP]
          exact ⟨fun h => by simpa using K.mul_mem (K.inv_mem hy) h, fun h => K.mul_mem hy h⟩
        · rw [hb] at hyP
          have hy : y ∉ K := fun h => by simpa using hyP.1 h
          change y * x ∈ K ↔ notB (oddW gs.length s u) = false
          have hn' : notB (oddW gs.length s u) = false ↔ oddW gs.length s u = true := by
            cases oddW gs.length s u <;> simp [notB]
          rw [hn']
          constructor
          · intro h
            by_contra h'
            have hxP' : x ∈ K := hxP.2 (by simpa using h')
            exact hy (by simpa using K.mul_mem h (K.inv_mem hxP'))
          · intro h
            have hxP' : x ∉ K := fun hx => by
              have := hxP.1 hx
              rw [h] at this
              cases this
            exact h2 y hyQ x hxQ hy hxP'
  obtain ⟨x, -, hxc, hxP⟩ := hpar u hu
  have hxo : x = o := (pcode_enc hn).inj (hxc.trans hou.symm)
  rw [hxo, hodd'] at hxP
  exact absurd (hxP.1 hoP) (by simp)

end Assembly

end CFSG.KC.E8K

end
