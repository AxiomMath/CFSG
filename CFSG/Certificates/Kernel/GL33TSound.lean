module

public import CFSG.Certificates.Kernel.GL33KSound
public import Certificates.Data.Kernel.GL33TShape
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Phi

public section

namespace CFSG.KC.GL33T

open CFSG.GL33 CFSG.GL33.Native CFSG.KC.GL33K
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF79.GL33 (GL33At e0 e1 e2 decV dec decV_one decV_two
  decV_three decV_nine decV_negV decV_inj mem_span_e12 decV_coord0_eq_zero li_of_raw det_dec)

theorem one_shiftLeft' (c : ℕ) : Nat.shiftLeft 1 c = 2 ^ c := Nat.one_shiftLeft c

theorem bitT_eq (M c : ℕ) : bitT M c = bitK M c := by
  unfold bitT bitK
  rw [one_shiftLeft']
  cases h : M.testBit c
  · have h0 : Nat.land M (2 ^ c) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      change (M &&& 2 ^ c).testBit i = _
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : c = i
      · subst hi
        simp [h]
      · simp [hi]
    rw [h0]
    rfl
  · have h0 : Nat.land M (2 ^ c) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun x => Nat.testBit x c) h0
      change (M &&& 2 ^ c).testBit c = (0 : ℕ).testBit c at h1
      rw [Nat.testBit_and, Nat.testBit_two_pow, h, Nat.zero_testBit] at h1
      simp at h1
    rw [Nat.blt_eq]
    omega

theorem setT_eq (M c : ℕ) : setT M c = M ||| 2 ^ c := by
  unfold setT
  rw [one_shiftLeft']
  rfl

theorem bitT_setT (S a c : ℕ) : bitT (setT S a) c = true ↔ bitT S c = true ∨ c = a := by
  rw [bitT_eq, bitT_eq, setT_eq, bitK_two_pow_or]

theorem bitT_setT_zero (a c : ℕ) : bitT (setT 0 a) c = true ↔ c = a := by
  rw [bitT_setT, bitT_eq]
  simp [bitK]

theorem getF_eq (L : List ℕ) (d l : ℕ) : getF L d l = (L[l]?).getD d := by
  induction L generalizing l with
  | nil => rfl
  | cons a L ih =>
    cases l with
    | zero => rfl
    | succ l => exact ih l

theorem getG_eq (L : List ℕ) (l : ℕ) : getG L l = (L[l]?).getD oneK := by
  induction L generalizing l with
  | nil => rfl
  | cons a L ih =>
    cases l with
    | zero => rfl
    | succ l => exact ih l

theorem getT_eq (L : List ℕ) (l : ℕ) : getT L l = (L[l]?).getD 0 := by
  induction L generalizing l with
  | nil => rfl
  | cons a L ih =>
    cases l with
    | zero => rfl
    | succ l => exact ih l

theorem getD_mem_or {L : List ℕ} {l d : ℕ} : (L[l]?).getD d ∈ L ∨ (L[l]?).getD d = d := by
  cases h : L[l]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

theorem lenK_eq {α : Type} (L : List α) : lenK L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem uptoK_iff (p : ℕ → Bool) (n : ℕ) : uptoK p n = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [uptoK]
  | succ n ih =>
    change (uptoK p n && p n) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem zipK_idx {α β : Type} {p : α → β → Bool} {A : List α} {B : List β}
    (h : zipK p A B = true) : A.length = B.length ∧
      ∀ k (ha : k < A.length) (hb : k < B.length), p A[k] B[k] = true := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => simp
    | cons b B => exact absurd h (by simp [zipK])
  | cons a A ih =>
    cases B with
    | nil => exact absurd h (by simp [zipK])
    | cons b B =>
      change (p a b && zipK p A B) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨i1, i2⟩ := ih h.2
      refine ⟨by simp [i1], fun k ha hb => ?_⟩
      cases k with
      | zero => exact h.1
      | succ k => exact i2 k (by simpa using ha) (by simpa using hb)

theorem zipK_mem {α β : Type} {p : α → β → Bool} {A : List α} {B : List β}
    (h : zipK p A B = true) {a : α} (ha : a ∈ A) : ∃ b ∈ B, p a b = true := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨hl, hp⟩ := zipK_idx h
  exact ⟨B[k], List.getElem_mem _, hp k hk (hl ▸ hk)⟩

theorem toM_eq_dec (c : ℕ) : toM c = dec c := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [toM, dec, decV, ent, dig, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;> congr 1 <;> norm_num <;> omega

theorem good_iff_detT (c : ℕ) : Good c ↔ detT c = true := by
  have e : detT c = !Nat.beq (((((c % 27) % 3) * ((((c / 27) % 27) / 3) % 3) *
      ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 3) % 3) * ((((c / 27) % 27) / 9) % 3) * (((c / 729) % 27) % 3) +
      (((c % 27) / 9) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 3) % 3) +
    2 * ((((c % 27) % 3) * ((((c / 27) % 27) / 9) % 3) * ((((c / 729) % 27) / 3) % 3) +
      (((c % 27) / 3) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 9) % 3) * ((((c / 27) % 27) / 3) % 3) * (((c / 729) % 27) % 3))))) % 3) 0 :=
    rfl
  rw [e]
  unfold Good
  rw [toM_eq_dec, det_dec]
  generalize (((c % 27) % 3) * ((((c / 27) % 27) / 3) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 3) % 3) * ((((c / 27) % 27) / 9) % 3) * (((c / 729) % 27) % 3) +
      (((c % 27) / 9) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 3) % 3) +
    2 * ((((c % 27) % 3) * ((((c / 27) % 27) / 9) % 3) * ((((c / 729) % 27) / 3) % 3) +
      (((c % 27) / 3) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 9) % 3) * ((((c / 27) % 27) / 3) % 3) * (((c / 729) % 27) % 3)))) = n
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Bool.not_eq_true',
    Bool.eq_false_iff, Ne, Nat.beq_eq]

theorem good_of_mulK_left {a b : ℕ} (h : Good (mulK a b)) : Good b := by
  unfold Good at *
  rw [mulK_eq_mulC, toM_mulC, Matrix.det_mul] at h
  exact right_ne_zero_of_mul h

theorem good_of_mulK_right {a b : ℕ} (h : Good (mulK a b)) : Good a := by
  unfold Good at *
  rw [mulK_eq_mulC, toM_mulC, Matrix.det_mul] at h
  exact left_ne_zero_of_mul h

theorem good_of_mulK_eq_oneK {a b : ℕ} (h : mulK a b = oneK) : Good a ∧ Good b := by
  have h1 : Good (mulK a b) := by rw [h]; exact good_oneK
  exact ⟨good_of_mulK_right h1, good_of_mulK_left h1⟩

theorem encode_ofCode {c : ℕ} (hc : Good c) (hl : c < 3 ^ 9) :
    encode ((ofCode c : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = c := by
  rw [coe_ofCode hc]
  exact eq_of_toM_eq (encode_lt _) hl (toM_encode _)

theorem good_encode (g : G) : Good (encode (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) :=
  good_of_mem_glCodes (encode_mem_glCodes g)

theorem mulK_sentinel (d : ℕ) : mulK d 19683 = 0 := by
  simp [mulK, mul9]

theorem act_ofCode {c : ℕ} (hc : Good c) (u : Fin 3 → ZMod 3) :
    act33 (ofCode c) u = Matrix.vecMul u (toM c) := by
  rw [act33, coe_ofCode hc]

theorem toM_row0 (c : ℕ) : toM c 0 = decV (c % 27) := by
  rw [toM_eq_dec]
  rfl

theorem act_e0 {c : ℕ} (hc : Good c) : act33 (ofCode c) e0 = decV (c % 27) := by
  rw [act_ofCode hc, ← toM_row0]
  funext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e0]

theorem act_decV {c r : ℕ} (hc : Good c) (hr : r < 27) :
    act33 (ofCode c) (decV r) = decV (actT r c) := by
  rw [act_ofCode hc]
  change Matrix.vecMul (decV r) (toM c) = decV (mulK r c % 27)
  rw [← toM_row0, mulK_eq_mulC, toM_mulC]
  have h0 : toM r 0 = decV r := by rw [toM_row0, Nat.mod_eq_of_lt hr]
  rw [← h0]
  funext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem actT_lt (r c : ℕ) : actT r c < 27 := Nat.mod_lt _ (by norm_num)

theorem decV_eq_iff {r r' : ℕ} (hr : r < 27) (hr' : r' < 27) : decV r = decV r' ↔ r = r' :=
  ⟨decV_inj hr hr', fun h => h ▸ rfl⟩

theorem negT_lt (r : ℕ) : negT r < 27 := by
  unfold negT
  omega

theorem decV_negT (r : ℕ) : decV (negT r) = -decV r := decV_negV r

theorem fix_iff {c : ℕ} (hc : Good c) : act33 (ofCode c) e0 = e0 ↔ c % 27 = 1 := by
  rw [act_e0 hc, ← decV_one, decV_eq_iff (Nat.mod_lt _ (by norm_num)) (by norm_num)]

theorem neg_iff {c : ℕ} (hc : Good c) : act33 (ofCode c) e0 = -e0 ↔ c % 27 = 2 := by
  rw [act_e0 hc, ← decV_one, ← decV_negT,
    decV_eq_iff (Nat.mod_lt _ (by norm_num)) (negT_lt _)]
  rfl

theorem act_e1 {c : ℕ} (hc : Good c) : act33 (ofCode c) e1 = decV (actT 3 c) := by
  rw [← decV_three, act_decV hc (by norm_num)]

theorem act_e2 {c : ℕ} (hc : Good c) : act33 (ofCode c) e2 = decV (actT 9 c) := by
  rw [← decV_nine, act_decV hc (by norm_num)]

theorem blockT_iff {c : ℕ} (hc : Good c) : blockT c = true ↔
    ∀ w ∈ Submodule.span (ZMod 3) {e1, e2}, act33 (ofCode c) w ∈
      Submodule.span (ZMod 3) {e1, e2} := by
  have r1 : (act33 (ofCode c) e1) 0 = (((c / 27) % 3 : ℕ) : ZMod 3) := by
    rw [act_ofCode hc, toM_eq_dec]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e1, dec, decV]
  have r2 : (act33 (ofCode c) e2) 0 = (((c / 729) % 3 : ℕ) : ZMod 3) := by
    rw [act_ofCode hc, toM_eq_dec]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e2, dec, decV]
  have z : ∀ n : ℕ, ((n % 3 : ℕ) : ZMod 3) = 0 ↔ n % 3 = 0 := by
    intro n
    rw [ZMod.natCast_eq_zero_iff]
    omega
  unfold blockT
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    rw [mem_span_e12] at hw ⊢
    have hw' : w = w 1 • e1 + w 2 • e2 := by
      funext j
      fin_cases j <;> simp [e1, e2, hw]
    rw [hw', act33, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul]
    have q1 : (act33 (ofCode c) e1) 0 = 0 := by rw [r1, z]; exact h1
    have q2 : (act33 (ofCode c) e2) 0 = 0 := by rw [r2, z]; exact h2
    simp only [act33] at q1 q2
    simp [q1, q2]
  · intro h
    have h1 := h e1 (Submodule.subset_span (by simp))
    have h2 := h e2 (Submodule.subset_span (by simp))
    rw [mem_span_e12, r1, z] at h1
    rw [mem_span_e12, r2, z] at h2
    exact ⟨h1, h2⟩

@[expose] noncomputable def subL (gens : List ℕ) : Subgroup G :=
  Subgroup.closure {x | ∃ g ∈ gens, ofCode g = x}

theorem gen_mem_subL {gens : List ℕ} {g : ℕ} (h : g ∈ gens) : ofCode g ∈ subL gens :=
  Subgroup.subset_closure ⟨g, h, rfl⟩

theorem getG_mem {gens : List ℕ} (hg : ∀ g ∈ gens, Good g) (l : ℕ) :
    Good (getG gens l) ∧ ofCode (getG gens l) ∈ subL gens := by
  rw [getG_eq]
  rcases getD_mem_or (L := gens) (l := l) (d := oneK) with h | h
  · exact ⟨hg _ h, gen_mem_subL h⟩
  · rw [h]
    exact ⟨good_oneK, by rw [ofCode_oneK]; exact (subL gens).one_mem⟩

theorem subL_le {gens : List ℕ} {X : Subgroup G} (h : ∀ g ∈ gens, ofCode g ∈ X) :
    subL gens ≤ X := by
  rw [subL, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

theorem treeT_bits {gens : List ℕ} {M : ℕ} {R : List (ℕ × ℕ × ℕ)} :
    ∀ {S : ℕ}, treeT gens M R S = true →
      ∀ c, bitT M c = true ↔ bitT S c = true ∨ c ∈ R.map (·.1) := by
  induction R with
  | nil =>
    intro S hS c
    have : S = M := by simpa [treeT] using hS
    simp [this]
  | cons r R ih =>
    intro S hS c
    change (bitT S r.2.1 && !bitT S r.1 && Nat.beq r.1 (mulK r.2.1 (getG gens r.2.2)) &&
      treeT gens M R (setT S r.1)) = true at hS
    rw [Bool.and_eq_true] at hS
    rw [ih hS.2 c, bitT_setT, List.map_cons, List.mem_cons]
    tauto

theorem treeT_inv{gens : List ℕ} {M : ℕ} (hg : ∀ g ∈ gens, Good g) {R : List (ℕ × ℕ × ℕ)} :
    ∀ {S : ℕ}, treeT gens M R S = true →
      (∀ c, bitT S c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens) →
      (∀ c ∈ R.map (·.1), c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens ∧ bitT S c = false) ∧
        (R.map (·.1)).Nodup := by
  induction R with
  | nil => intro S _ _; simp
  | cons r R ih =>
    intro S hS hP
    change (bitT S r.2.1 && !bitT S r.1 && Nat.beq r.1 (mulK r.2.1 (getG gens r.2.2)) &&
      treeT gens M R (setT S r.1)) = true at hS
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at hS
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hS
    obtain ⟨p1, p2, p3⟩ := hP _ h1
    have hgm := getG_mem hg r.2.2
    have hc : r.1 < 3 ^ 9 ∧ Good r.1 ∧ ofCode r.1 ∈ subL gens := by
      rw [h3]
      exact ⟨mulK_lt _ _, good_mulK p2 hgm.1, by
        rw [ofCode_mulK p2 hgm.1]
        exact (subL gens).mul_mem p3 hgm.2⟩
    have hP' : ∀ c, bitT (setT S r.1) c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens := by
      intro c hc'
      rcases (bitT_setT S r.1 c).1 hc' with h | rfl
      · exact hP c h
      · exact hc
    obtain ⟨i1, i2⟩ := ih h4 hP'
    have hnot : ∀ c ∈ R.map (·.1), bitT S c = false ∧ c ≠ r.1 := by
      intro c hc'
      have hf := (i1 c hc').2.2.2
      have hS' : ¬ (bitT S c = true ∨ c = r.1) := fun h => by
        rw [(bitT_setT S r.1 c).2 h] at hf
        exact absurd hf (by decide)
      refine ⟨?_, fun e => hS' (Or.inr e)⟩
      cases h : bitT S c
      · rfl
      · exact absurd (Or.inl h) hS'
    refine ⟨fun c hc' => ?_, ?_⟩
    · rw [List.map_cons, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact ⟨hc.1, hc.2.1, hc.2.2, h2⟩
      · exact ⟨(i1 c hc').1, (i1 c hc').2.1, (i1 c hc').2.2.1, (hnot c hc').1⟩
    · rw [List.map_cons]
      exact List.nodup_cons.2 ⟨fun hm => (hnot _ hm).2 rfl, i2⟩

theorem closure_sub_submonoid (T : Submonoid G) (s : Set G) (h : s ⊆ T) :
    ∀ x ∈ Subgroup.closure s, x ∈ T := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h hx
  | one => exact T.one_mem
  | mul x y _ _ hx hy => exact T.mul_mem hx hy
  | inv x _ hx =>
    have h1 : x ^ (Nat.card G - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact T.pow_mem hx _

theorem memT_sound {gens : List ℕ} {M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memT gens M R = true)
    (hg : ∀ g ∈ gens, Good g) :
    (∀ c, bitT M c = true ↔ c ∈ oneK :: R.map (·.1)) ∧
      (∀ c, bitT M c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens) ∧
      (∀ x ∈ subL gens, bitT M (encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true) ∧
      (oneK :: R.map (·.1)).Nodup := by
  have hm := h
  change (treeT gens M R (setT 0 oneK) && closT gens M R) = true at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨ht, hcl⟩ := hm
  have hone : oneK < 3 ^ 9 ∧ Good oneK ∧ ofCode oneK ∈ subL gens :=
    ⟨by decide, good_oneK, by rw [ofCode_oneK]; exact (subL gens).one_mem⟩
  obtain ⟨i1, i2⟩ := treeT_inv hg ht (fun c hc => by
    rw [(bitT_setT_zero oneK c).1 hc]
    exact hone)
  have hL : ∀ c, bitT M c = true ↔ c ∈ oneK :: R.map (·.1) := by
    intro c
    rw [treeT_bits ht c, bitT_setT_zero, List.mem_cons]
  have hA : ∀ c, bitT M c = true → c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens := by
    intro c hc
    rcases List.mem_cons.1 ((hL c).1 hc) with rfl | hc'
    · exact hone
    · exact ⟨(i1 c hc').1, (i1 c hc').2.1, (i1 c hc').2.2.1⟩
  have hclos : ∀ c, bitT M c = true → ∀ g ∈ gens, bitT M (mulK c g) = true := by
    change (allK (fun g => bitT M (mulK oneK g)) gens &&
      allK (fun r => allK (fun g => bitT M (mulK r.1 g)) gens) R) = true at hcl
    rw [Bool.and_eq_true, allK_iff, allK_iff] at hcl
    intro c hc g hgm
    rcases List.mem_cons.1 ((hL c).1 hc) with rfl | hc'
    · exact hcl.1 g hgm
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
      exact (allK_iff _ _).1 (hcl.2 r hr) g hgm
  let T : Submonoid G :=
    { carrier := {x | ∀ y, (∃ c, bitT M c = true ∧ ofCode c = y) →
        ∃ c, bitT M c = true ∧ ofCode c = y * x}
      mul_mem' := by
        intro a b ha hb y hy
        rw [← mul_assoc]
        exact hb _ (ha y hy)
      one_mem' := by
        intro y hy
        simpa using hy }
  have hsub : {x | ∃ g ∈ gens, ofCode g = x} ⊆ (T : Set G) := by
    rintro _ ⟨g, hgm, rfl⟩ y ⟨c, hc, rfl⟩
    exact ⟨mulK c g, hclos c hc g hgm, ofCode_mulK (hA c hc).2.1 (hg g hgm)⟩
  have hB : ∀ x ∈ subL gens, ∃ c, bitT M c = true ∧ ofCode c = x := by
    intro x hx
    have := closure_sub_submonoid T _ hsub x hx 1 ⟨oneK, (hL oneK).2 (List.mem_cons_self ..),
      ofCode_oneK⟩
    rwa [one_mul] at this
  have hnd : (oneK :: R.map (·.1)).Nodup := by
    refine List.nodup_cons.2 ⟨fun hm => ?_, i2⟩
    have := (i1 _ hm).2.2.2
    rw [(bitT_setT_zero oneK oneK).2 rfl] at this
    exact absurd this (by decide)
  refine ⟨hL, hA, fun x hx => ?_, hnd⟩
  obtain ⟨c, hc, rfl⟩ := hB x hx
  rw [encode_ofCode (hA c hc).2.1 (hA c hc).1]
  exact hc

@[expose] noncomputable def stab0 : Subgroup G where
  carrier := {g | act33 g e0 = e0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, act33, Units.val_mul] at *
    rw [← Matrix.vecMul_vecMul, ha, hb]
  one_mem' := by simp [act33]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, act33] at *
    calc Matrix.vecMul e0 ((a⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3))
        = Matrix.vecMul (Matrix.vecMul e0 (a : Matrix (Fin 3) (Fin 3) (ZMod 3)))
            ((a⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by rw [ha]
      _ = e0 := by rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]

theorem mem_stab0 {g : G} : g ∈ stab0 ↔ act33 g e0 = e0 := Iff.rfl

theorem card_fix_eq (X : Subgroup G) :
    Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} = Nat.card (X ⊓ stab0 : Subgroup G) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [Subgroup.mem_inf, mem_stab0])

theorem stabL_cons (r : ℕ × ℕ × ℕ) (R : List (ℕ × ℕ × ℕ)) :
    stabL (r :: R) = if r.1 % 27 = 1 then r.1 :: stabL R else stabL R := by
  change Bool.rec (motive := fun _ => List ℕ) (stabL R) (r.1 :: stabL R) (Nat.beq (r.1 % 27) 1) = _
  cases h : Nat.beq (r.1 % 27) 1
  · have : r.1 % 27 ≠ 1 := fun e => by rw [e] at h; exact absurd h (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem stabN_eq (R : List (ℕ × ℕ × ℕ)) : stabN R = (stabL R).length := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    change Bool.rec (motive := fun _ => ℕ) (stabN R) (Nat.succ (stabN R))
      (Nat.beq (r.1 % 27) 1) = _
    rw [stabL_cons]
    cases h : Nat.beq (r.1 % 27) 1
    · have : r.1 % 27 ≠ 1 := fun e => by rw [e] at h; exact absurd h (by decide)
      simp [this, ih]
    · simp [Nat.eq_of_beq_eq_true h, ih]

theorem bitT_stabM (R : List (ℕ × ℕ × ℕ)) (c : ℕ) : bitT (stabM R) c = true ↔ c ∈ stabL R := by
  induction R with
  | nil =>
    change bitT (setT 0 oneK) c = true ↔ c ∈ [oneK]
    rw [bitT_setT_zero, List.mem_singleton]
  | cons r R ih =>
    change bitT (Bool.rec (motive := fun _ => ℕ) (stabM R) (setT (stabM R) r.1)
      (Nat.beq (r.1 % 27) 1)) c = true ↔ _
    rw [stabL_cons]
    cases h : Nat.beq (r.1 % 27) 1
    · have : r.1 % 27 ≠ 1 := fun e => by rw [e] at h; exact absurd h (by decide)
      simp [this, ih]
    · simp only [Nat.eq_of_beq_eq_true h, if_true]
      rw [bitT_setT, ih, List.mem_cons]
      tauto

theorem mem_stabL (R : List (ℕ × ℕ × ℕ)) (c : ℕ) :
    c ∈ stabL R ↔ c ∈ oneK :: R.map (·.1) ∧ c % 27 = 1 := by
  induction R with
  | nil =>
    simp only [stabL, List.map_nil, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, by decide⟩
    · exact fun h => h.1
  | cons r R ih =>
    rw [stabL_cons]
    have h1 : oneK % 27 = 1 := by decide
    split_ifs with h
    · rw [List.mem_cons, ih]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (rfl | ⟨h2 | h2, h3⟩)
        · exact ⟨Or.inr (Or.inl rfl), h⟩
        · exact ⟨Or.inl h2, h3⟩
        · exact ⟨Or.inr (Or.inr h2), h3⟩
      · rintro ⟨h2 | h2 | h2, h3⟩
        · exact Or.inr ⟨Or.inl h2, h3⟩
        · exact Or.inl h2
        · exact Or.inr ⟨Or.inr h2, h3⟩
    · rw [ih]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro ⟨h2 | h2, h3⟩
        · exact ⟨Or.inl h2, h3⟩
        · exact ⟨Or.inr (Or.inr h2), h3⟩
      · rintro ⟨h2 | h2 | h2, h3⟩
        · exact ⟨Or.inl h2, h3⟩
        · exact absurd (h2 ▸ h3) h
        · exact ⟨Or.inr h2, h3⟩

theorem stabL_sublist (R : List (ℕ × ℕ × ℕ)) :
    List.Sublist (stabL R) (R.map (·.1) ++ [oneK]) := by
  induction R with
  | nil => exact List.Sublist.refl _
  | cons r R ih =>
    rw [stabL_cons]
    split_ifs
    · exact ih.cons₂ _
    · exact ih.cons _

theorem stabL_nodup {R : List (ℕ × ℕ × ℕ)} (h : (oneK :: R.map (·.1)).Nodup) :
    (stabL R).Nodup := by
  refine (stabL_sublist R).nodup ?_
  have : (R.map (·.1) ++ [oneK]).Perm (oneK :: R.map (·.1)) := List.perm_append_singleton _ _
  exact this.nodup_iff.2 h

theorem bitT_orbM (R : List (ℕ × ℕ × ℕ)) (u : ℕ) :
    bitT (orbM R) u = true ↔ ∃ c ∈ oneK :: R.map (·.1), c % 27 = u := by
  induction R with
  | nil =>
    change bitT (setT 0 1) u = true ↔ _
    rw [bitT_setT_zero]
    simp only [List.map_nil, List.mem_singleton, exists_eq_left]
    constructor
    · rintro rfl
      decide
    · rintro rfl
      decide
  | cons r R ih =>
    change bitT (setT (orbM R) (r.1 % 27)) u = true ↔ _
    rw [bitT_setT, ih]
    simp only [List.map_cons, List.mem_cons]
    constructor
    · rintro (⟨c, hc | hc, rfl⟩ | rfl)
      · exact ⟨c, Or.inl hc, rfl⟩
      · exact ⟨c, Or.inr (Or.inr hc), rfl⟩
      · exact ⟨r.1, Or.inr (Or.inl rfl), rfl⟩
    · rintro ⟨c, hc | hc | hc, rfl⟩
      · exact Or.inl ⟨c, Or.inl hc, rfl⟩
      · exact Or.inr (by rw [hc])
      · exact Or.inl ⟨c, Or.inr hc, rfl⟩

theorem stab_sound {gens : List ℕ} {M : ℕ} {R : List (ℕ × ℕ × ℕ)} (h : memT gens M R = true)
    (hg : ∀ g ∈ gens, Good g) :
    (∀ c ∈ stabL R, c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens ⊓ stab0) ∧
      (∀ x ∈ subL gens ⊓ stab0, encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ stabL R) ∧
      Nat.card (subL gens ⊓ stab0 : Subgroup G) = stabN R := by
  classical
  obtain ⟨hL, hA, hB, hnd⟩ := memT_sound h hg
  have h1 : ∀ c ∈ stabL R, c < 3 ^ 9 ∧ Good c ∧ ofCode c ∈ subL gens ⊓ stab0 := by
    intro c hc
    have hc' := (mem_stabL R c).1 hc
    obtain ⟨a1, a2, a3⟩ := hA c ((hL c).2 hc'.1)
    exact ⟨a1, a2, Subgroup.mem_inf.2 ⟨a3, (fix_iff a2).2 hc'.2⟩⟩
  have h2 : ∀ x ∈ subL gens ⊓ stab0, encode (x : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ stabL R := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have hb := hB x hx1
    refine (mem_stabL R _).2 ⟨(hL _).1 hb, ?_⟩
    have := (fix_iff (good_encode x)).1 (by rw [ofCode_encode]; exact hx2)
    exact this
  refine ⟨h1, h2, ?_⟩
  have hmem : ∀ c ∈ stabL R, c ∈ glCodes () := fun c hc =>
    (mem_glCodes_iff c).2 ⟨(h1 c hc).1, (h1 c hc).2.1⟩
  have hnd' : ((stabL R).map ofCode).Nodup :=
    List.Nodup.map_on (fun c hc d hd e => ofCode_injOn (hmem c hc) (hmem d hd) e)
      (stabL_nodup hnd)
  have hiff : ∀ x, x ∈ subL gens ⊓ stab0 ↔ x ∈ ((stabL R).map ofCode).toFinset := by
    intro x
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · intro hx
      exact ⟨_, h2 x hx, ofCode_encode x⟩
    · rintro ⟨c, hc, rfl⟩
      exact (h1 c hc).2.2
  rw [stabN_eq]
  calc Nat.card (subL gens ⊓ stab0 : Subgroup G)
      = Nat.card {x // x ∈ ((stabL R).map ofCode).toFinset} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = ((stabL R).map ofCode).toFinset.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = (stabL R).length := by
        rw [List.toFinset_card_of_nodup hnd', List.length_map]

theorem covT_sound {M : ℕ} {reps : List ℕ} {blk : Bool} {C : List (ℕ × ℕ)}
    (h : covT M reps blk C = true) (a : ℕ) (ha : a < 729) (hd : detT (1 + 27 * a) = true)
    (hb : blk = true → blockT (1 + 27 * a) = true) :
    ∃ d k, bitT M d = true ∧ 1 + 27 * a = mulK d (getF reps 19683 k) := by
  unfold covT at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, lenK_eq] at h
  obtain ⟨⟨hl, -⟩, h⟩ := h
  suffices ∀ (C : List (ℕ × ℕ)) (a0 : ℕ), (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun r _ ih a => (!detT (1 + 27 * a) || (blk && !blockT (1 + 27 * a)) ||
        bitT M r.1 && Nat.beq (1 + 27 * a) (mulK r.1 (getF reps 19683 r.2))) && ih (Nat.succ a))
        C a0) = true → ∀ p < C.length, detT (1 + 27 * (a0 + p)) = true →
          (blk = true → blockT (1 + 27 * (a0 + p)) = true) →
          ∃ d k, bitT M d = true ∧ 1 + 27 * (a0 + p) = mulK d (getF reps 19683 k) by
    have := this C 0 h a (by omega) (by simpa using hd) (by simpa using hb)
    simpa using this
  intro C
  induction C with
  | nil => intro a0 _ p hp; simp at hp
  | cons r C ih =>
    intro a0 hC p hp hd hb
    change ((!detT (1 + 27 * a0) || (blk && !blockT (1 + 27 * a0)) ||
        bitT M r.1 && Nat.beq (1 + 27 * a0) (mulK r.1 (getF reps 19683 r.2))) &&
        _) = true at hC
    rw [Bool.and_eq_true] at hC
    cases p with
    | zero =>
      have h1 := hC.1
      simp only [Nat.add_zero] at hd hb ⊢
      rw [hd] at h1
      cases blk with
      | false =>
        simp only [Bool.not_true, Bool.false_or, Bool.false_and, Bool.and_eq_true,
          Nat.beq_eq] at h1
        exact ⟨r.1, r.2, h1⟩
      | true =>
        rw [hb rfl] at h1
        simp only [Bool.not_true, Bool.false_or, Bool.true_and, Bool.and_eq_true,
          Nat.beq_eq] at h1
        exact ⟨r.1, r.2, h1⟩
    | succ p =>
      have := ih (a0 + 1) hC.2 p (by simpa using hp) (by rwa [Nat.add_assoc, Nat.add_comm 1 p])
        (by rwa [Nat.add_assoc, Nat.add_comm 1 p])
      rwa [Nat.add_assoc, Nat.add_comm 1 p] at this

theorem ucovK_sound {OM M : ℕ} {orr : List ℕ} {C : List (ℕ × ℕ)} (h : ucovK OM M orr C = true)
    (u : ℕ) (hu1 : 1 ≤ u) (hu : u < 27) :
    bitT OM u = true ∨ ∃ s k, bitT M s = true ∧ actT u s = getF orr 27 k := by
  unfold ucovK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenK_eq] at h
  obtain ⟨hl, h⟩ := h
  suffices ∀ (C : List (ℕ × ℕ)) (u0 : ℕ), (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun r _ ih u => (bitT OM u || bitT M r.1 && Nat.beq (actT u r.1) (getF orr 27 r.2)) &&
        ih (Nat.succ u)) C u0) = true → ∀ p < C.length,
          bitT OM (u0 + p) = true ∨ ∃ s k, bitT M s = true ∧ actT (u0 + p) s = getF orr 27 k by
    have := this C 1 h (u - 1) (by omega)
    rwa [Nat.add_sub_cancel' hu1] at this
  intro C
  induction C with
  | nil => intro u0 _ p hp; simp at hp
  | cons r C ih =>
    intro u0 hC p hp
    change ((bitT OM u0 || bitT M r.1 && Nat.beq (actT u0 r.1) (getF orr 27 r.2)) && _) = true
      at hC
    rw [Bool.and_eq_true] at hC
    cases p with
    | zero =>
      have h1 := hC.1
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨r.1, r.2, h1⟩
    | succ p =>
      have := ih (u0 + 1) hC.2 p (by simpa using hp)
      rwa [Nat.add_assoc, Nat.add_comm 1 p] at this

theorem evalW_mem {L : List ℕ} {X : Subgroup G} (hL : ∀ g ∈ L, Good g ∧ ofCode g ∈ X)
    (w : List ℕ) : Good (evalW L w) ∧ ofCode (evalW L w) ∈ X ∧ evalW L w < 3 ^ 9 := by
  have hG : ∀ l, Good (getG L l) ∧ ofCode (getG L l) ∈ X := by
    intro l
    rw [getG_eq]
    rcases getD_mem_or (L := L) (l := l) (d := oneK) with h | h
    · exact hL _ h
    · rw [h]
      exact ⟨good_oneK, by rw [ofCode_oneK]; exact X.one_mem⟩
  suffices ∀ acc, Good acc → ofCode acc ∈ X → acc < 3 ^ 9 →
      Good (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulK acc (getG L l))) w acc) ∧
      ofCode (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulK acc (getG L l))) w acc) ∈ X ∧
      (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulK acc (getG L l))) w acc) < 3 ^ 9 from
    this oneK good_oneK (by rw [ofCode_oneK]; exact X.one_mem) (by decide)
  induction w with
  | nil => exact fun acc h1 h2 h3 => ⟨h1, h2, h3⟩
  | cons l w ih =>
    intro acc h1 h2 _
    refine ih _ (good_mulK h1 (hG l).1) ?_ (mulK_lt _ _)
    rw [ofCode_mulK h1 (hG l).1]
    exact X.mul_mem h2 (hG l).2

@[expose] noncomputable def presM (T : Set (Fin 3 → ZMod 3)) : Submonoid G where
  carrier := {g | ∀ x ∈ T, act33 g x ∈ T}
  mul_mem' := by
    intro a b ha hb x hx
    change Matrix.vecMul x ((a * b : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ T
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    exact hb _ (ha x hx)
  one_mem' := by
    intro x hx
    change Matrix.vecMul x ((1 : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ T
    rw [Units.val_one, Matrix.vecMul_one]
    exact hx

theorem subL_presM {gens : List ℕ} {T : Set (Fin 3 → ZMod 3)}
    (h : ∀ g ∈ gens, ∀ x ∈ T, act33 (ofCode g) x ∈ T) :
    ∀ x ∈ subL gens, ∀ v ∈ T, act33 x v ∈ T :=
  closure_sub_submonoid (presM T) _ (by rintro _ ⟨g, hgm, rfl⟩; exact h g hgm)

theorem pm_e0 {g : G} (h : act33 g e0 = e0 ∨ act33 g e0 = -e0) :
    ∀ x ∈ ({e0, -e0} : Set (Fin 3 → ZMod 3)), act33 g x ∈ ({e0, -e0} : Set (Fin 3 → ZMod 3)) := by
  intro x hx
  have hn : act33 g (-e0) = -act33 g e0 := Matrix.neg_vecMul _ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact h
  · rw [hn]
    rcases h with h | h
    · exact Or.inr (by rw [h])
    · refine Or.inl ?_
      rw [h]
      funext j
      fin_cases j <;> rfl

theorem block_mem {gens : List ℕ} (hg : ∀ g ∈ gens, Good g) (h : allK blockT gens = true) :
    ∀ x ∈ subL gens, ∀ w ∈ Submodule.span (ZMod 3) {e1, e2},
      act33 x w ∈ Submodule.span (ZMod 3) {e1, e2} := by
  refine subL_presM (T := (Submodule.span (ZMod 3) {e1, e2} : Set (Fin 3 → ZMod 3))) ?_
  intro g hgm
  exact (blockT_iff (hg g hgm)).1 ((allK_iff _ _).1 h g hgm)

theorem phiT_sound {gens : List ℕ} {M : ℕ} {R : List (ℕ × ℕ × ℕ)}
    {kind u1 u2 g1 g2 g3 : ℕ} (hm : memT gens M R = true) (hg : ∀ g ∈ gens, Good g)
    (h : phiT gens M R kind u1 u2 g1 g2 g3 = true) : GL33At (subL gens) e0 e1 e2 := by
  obtain ⟨hL, hA, -, -⟩ := memT_sound hm hg
  intro _ _ _ _ hE
  match kind, h with
  | 0, h =>
    exfalso
    change allK (fun g => Nat.beq (g % 27) 1 || Nat.beq (g % 27) 2) gens = true at h
    obtain ⟨x, hx, h1, h2⟩ := hE
    have := subL_presM (T := ({e0, -e0} : Set (Fin 3 → ZMod 3))) (fun g hgm => pm_e0 (by
      have := (allK_iff _ _).1 h g hgm
      rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at this
      rcases this with h3 | h3
      · exact Or.inl ((fix_iff (hg g hgm)).2 h3)
      · exact Or.inr ((neg_iff (hg g hgm)).2 h3))) x hx e0 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with h3 | h3
    · exact h1 h3
    · exact h2 h3
  | 1, h =>
    change (allK blockT gens && uptoK (fun u => Nat.beq (u % 3) 0 || bitT (orbM R) u ||
        bitT (orbM R) (negT u)) 27) = true at h
    rw [Bool.and_eq_true, uptoK_iff] at h
    refine Or.inl ⟨block_mem hg h.1, fun u hu => ?_⟩
    have hn := CFSG.RankThree.PartTwo.Sec21.FF79.GL33.encV_lt u
    have hdu := CFSG.RankThree.PartTwo.Sec21.FF79.GL33.decV_encV u
    generalize CFSG.RankThree.PartTwo.Sec21.FF79.GL33.encV u = n at hn hdu
    subst hdu
    have h3 := h.2 n hn
    simp only [Bool.or_eq_true, Nat.beq_eq] at h3
    have hn3 : n % 3 ≠ 0 := fun h0 => hu (mem_span_e12.2 (decV_coord0_eq_zero.2 h0))
    rcases h3 with (h3 | h3) | h3
    · exact absurd h3 hn3
    · obtain ⟨c, hc, rfl⟩ := (bitT_orbM R _).1 h3
      obtain ⟨-, hc2, hc3⟩ := hA c ((hL c).2 hc)
      exact ⟨ofCode c, hc3, Or.inl (act_e0 hc2)⟩
    · obtain ⟨c, hc, hc'⟩ := (bitT_orbM R _).1 h3
      obtain ⟨-, hc2, hc3⟩ := hA c ((hL c).2 hc)
      exact ⟨ofCode c, hc3, Or.inr (by rw [act_e0 hc2, hc', decV_negT])⟩
  | k + 2, h =>
    change (Nat.blt u1 27 && Nat.blt u2 27 && Nat.beq (u1 % 3) 0 && Nat.beq (u2 % 3) 0 &&
        !Nat.beq (((u1 / 3) % 3 * ((u2 / 9) % 3) + 2 * ((u1 / 9) % 3 * ((u2 / 3) % 3))) % 3) 0 &&
        allK (fun g => allK (fun x => elemK (actT x g) [1, 2, u1, negT u1, u2, negT u2])
          [1, 2, u1, negT u1, u2, negT u2]) gens &&
        bitT M g1 && Nat.beq (actT 1 g1) 2 && Nat.beq (actT u1 g1) u1 &&
        Nat.beq (actT u2 g1) u2 &&
        bitT M g2 && Nat.beq (actT 1 g2) u1 && Nat.beq (actT u1 g2) 1 &&
        Nat.beq (actT u2 g2) u2 &&
        bitT M g3 && Nat.beq (actT 1 g3) u1 && Nat.beq (actT u1 g3) u2 &&
        Nat.beq (actT u2 g3) 1) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Bool.not_eq_true', and_assoc] at h
    obtain ⟨hu1, hu2, hm1, hm2, hdet, hcl, b1, a1, a2, a3, b2, c1, c2, c3, b3, d1, d2, d3⟩ := h
    have hdet' : (((u1 / 3) % 3 * ((u2 / 9) % 3) + 2 * ((u1 / 9) % 3 * ((u2 / 3) % 3))) % 3) ≠ 0 :=
      fun e => by rw [e] at hdet; exact absurd hdet (by decide)
    have L6 : ∀ x ∈ [1, 2, u1, negT u1, u2, negT u2], x < 27 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | exact negT_lt _
    have back : ∀ y ∈ [1, 2, u1, negT u1, u2, negT u2], decV y ∈
        ({e0, -e0, decV u1, -decV u1, decV u2, -decV u2} : Set (Fin 3 → ZMod 3)) := by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [decV_one, decV_two, decV_negT]
    have fwd : ∀ x ∈ ({e0, -e0, decV u1, -decV u1, decV u2, -decV u2} : Set (Fin 3 → ZMod 3)),
        ∃ r ∈ [1, 2, u1, negT u1, u2, negT u2], decV r = x := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, decV_one⟩
      · exact ⟨2, by simp, decV_two⟩
      · exact ⟨u1, by simp, rfl⟩
      · exact ⟨negT u1, by simp, decV_negT u1⟩
      · exact ⟨u2, by simp, rfl⟩
      · exact ⟨negT u2, by simp, decV_negT u2⟩
    have act1 : ∀ c (hc : Good c) {r : ℕ}, r < 27 → act33 (ofCode c) (decV r) = decV (actT r c) :=
      fun c hc r hr => act_decV hc hr
    have hm : ∀ c, bitT M c = true → Good c ∧ ofCode c ∈ subL gens := fun c hc =>
      ⟨(hA c hc).2.1, (hA c hc).2.2⟩
    refine Or.inr ⟨decV u1, mem_span_e12.2 (decV_coord0_eq_zero.2 hm1), decV u2,
      mem_span_e12.2 (decV_coord0_eq_zero.2 hm2), li_of_raw hm1 hm2 hdet', ?_, ?_, ?_, ?_⟩
    · refine subL_presM (fun g hgm v hv => ?_)
      obtain ⟨x, hx, rfl⟩ := fwd v hv
      rw [act1 g (hg g hgm) (L6 x hx)]
      exact back _ ((elemK_iff _ _).1 ((allK_iff _ _).1 ((allK_iff _ _).1 hcl g hgm) x hx))
    · refine ⟨ofCode g1, (hm g1 b1).2, ?_, ?_, ?_⟩
      · rw [← decV_one, act1 g1 (hm g1 b1).1 (by norm_num), a1, decV_two, decV_one]
      · rw [act1 g1 (hm g1 b1).1 hu1, a2]
      · rw [act1 g1 (hm g1 b1).1 hu2, a3]
    · refine ⟨ofCode g2, (hm g2 b2).2, ?_, ?_, ?_⟩
      · rw [← decV_one, act1 g2 (hm g2 b2).1 (by norm_num), c1]
      · rw [act1 g2 (hm g2 b2).1 hu1, c2, decV_one]
      · rw [act1 g2 (hm g2 b2).1 hu2, c3]
    · refine ⟨ofCode g3, (hm g3 b3).2, ?_, ?_, ?_⟩
      · rw [← decV_one, act1 g3 (hm g3 b3).1 (by norm_num), d1]
      · rw [act1 g3 (hm g3 b3).1 hu1, d2]
      · rw [act1 g3 (hm g3 b3).1 hu2, d3, decV_one]

@[expose] def Claim (S : Subgroup G) : Prop := ∀ X : Subgroup G, S ≤ X → GL33At X e0 e1 e2

theorem anyRec_iff (p : ℕ → Bool) (Q : List ℕ) :
    List.rec (motive := fun _ => Bool) false (fun d _ ih => p d || ih) Q = true ↔
      ∃ d ∈ Q, p d = true := by
  induction Q with
  | nil => simp
  | cons d Q ih =>
    change (p d || List.rec (motive := fun _ => Bool) false (fun d _ ih => p d || ih) Q) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp

theorem nonemptyT_iff {α : Type} (L : List α) : nonemptyT L = true ↔ L ≠ [] := by
  cases L <;> simp [nonemptyT]

theorem childK_sound {G' : List (List ℕ)} {Ms : List ℕ} {i : ℕ} {g : List ℕ} {M QM : ℕ}
    {Q : List ℕ} {x : ℕ} {c : ℕ × ℕ × List (List ℕ)} (h : childK G' Ms i g M QM Q x c = true)
    (hg : ∀ g' ∈ g, Good g') {X : Subgroup G} (hle : subL g ≤ X) (hx : Good x)
    (hxX : ofCode x ∈ X) (hxS : bitT M x = true → False)
    (hj : ∀ j, i < j → j < lenK G' → Claim (subL (G'.getD j [])))
    (hq : 2 ≤ c.1 → nonemptyT c.2.2 = true ∧
      (Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} = 8 →
        X ⊓ stab0 ≤ subL g) ∧
      (∀ y ∈ subL g ⊓ stab0, bitT QM (encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true ∧
        encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ Q)) :
    GL33At X e0 e1 e2 := by
  obtain ⟨k, j, ws⟩ := c
  unfold childK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp, h⟩ := h
  have hL : ∀ a ∈ g ++ [x], Good a ∧ ofCode a ∈ X := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ⟨hg a ha, hle (gen_mem_subL ha)⟩
    · rw [List.mem_singleton.1 ha]
      exact ⟨hx, hxX⟩
  match k, h, hp, hq with
  | 0, h, _, _ => exact absurd h (fun h' => hxS h')
  | 1, h, hp, _ =>
    change (zipK (fun g' w => Nat.beq g' (evalW (g ++ [x]) w)) (G'.getD j []) ws &&
        allK (fun g' => bitT (Ms.getD j 0) g') g && bitT (Ms.getD j 0) x) = true at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    simp only [Bool.not_eq_true', Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hp
    have hp' : i < j ∧ j < lenK G' := by
      rcases hp with hp | hp
      · exact absurd hp (by decide)
      · exact hp
    refine hj j hp'.1 hp'.2 X (subL_le fun g' hg' => ?_)
    obtain ⟨w, -, hw⟩ := zipK_mem h.1.1 hg'
    rw [Nat.beq_eq] at hw
    rw [hw]
    exact (evalW_mem hL w).2.1
  | 2, h, _, hq =>
    intro _ hcard _ _ _
    exfalso
    obtain ⟨hne, hXS, hQS⟩ := hq (by norm_num)
    change allK (fun w => Nat.beq (evalW (g ++ [x]) w % 27) 1 &&
      !bitT QM (evalW (g ++ [x]) w)) ws = true at h
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ ((nonemptyT_iff _).1 hne)
    have h1 := (allK_iff _ _).1 h w hw
    simp only [Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h1
    obtain ⟨e1g, e2X, e3⟩ := evalW_mem hL w
    have hmem : ofCode (evalW (g ++ [x]) w) ∈ subL g ⊓ stab0 :=
      Subgroup.mem_inf.2 ⟨hXS hcard (Subgroup.mem_inf.2 ⟨e2X, (fix_iff e1g).2 h1.1⟩),
        (fix_iff e1g).2 h1.1⟩
    have := (hQS _ hmem).1
    rw [encode_ofCode e1g e3, h1.2] at this
    exact absurd this (by decide)
  | k + 3, h, _, hq =>
    intro _ hcard _ hD _
    exfalso
    obtain ⟨hne, hXS, hQS⟩ := hq (by omega)
    change allK (fun w => dBadT Q (evalW (g ++ [x]) w)) ws = true at h
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ ((nonemptyT_iff _).1 hne)
    have h1 := (allK_iff _ _).1 h w hw
    obtain ⟨e1g, e2X, e3⟩ := evalW_mem hL w
    generalize evalW (g ++ [x]) w = e at h1 e1g e2X e3
    unfold dBadT at h1
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h1
    obtain ⟨h0, h1⟩ := h1
    have hpm : act33 (ofCode e) e0 = e0 ∨ act33 (ofCode e) e0 = -e0 := by
      rcases h0 with h0 | h0
      · exact Or.inl ((fix_iff e1g).2 h0)
      · exact Or.inr ((neg_iff e1g).2 h0)
    obtain ⟨hW, d, hdX, hd0, hpmd⟩ := hD _ e2X hpm
    rw [← blockT_iff e1g] at hW
    have hdS : d ∈ subL g ⊓ stab0 :=
      Subgroup.mem_inf.2 ⟨hXS hcard (Subgroup.mem_inf.2 ⟨hdX, hd0⟩), hd0⟩
    have hdQ := (hQS d hdS).2
    have hdg := good_encode d
    have hdd : ofCode (encode (d : Matrix (Fin 3) (Fin 3) (ZMod 3))) = d := ofCode_encode d
    generalize encode (d : Matrix (Fin 3) (Fin 3) (ZMod 3)) = dc at hdQ hdg hdd
    subst hdd
    have e1m : e1 ∈ Submodule.span (ZMod 3) {e1, e2} := Submodule.subset_span (by simp)
    have e2m : e2 ∈ Submodule.span (ZMod 3) {e1, e2} := Submodule.subset_span (by simp)
    have hany : List.rec (motive := fun _ => Bool) false (fun d _ ih =>
        (Nat.beq (actT 3 e) (actT 3 d) && Nat.beq (actT 9 e) (actT 9 d)) ||
        (Nat.beq (actT 3 e) (negT (actT 3 d)) && Nat.beq (actT 9 e) (negT (actT 9 d))) || ih) Q =
          true := by
      refine (anyRec_iff (fun d => (Nat.beq (actT 3 e) (actT 3 d) &&
        Nat.beq (actT 9 e) (actT 9 d)) || (Nat.beq (actT 3 e) (negT (actT 3 d)) &&
        Nat.beq (actT 9 e) (negT (actT 9 d)))) Q).2 ⟨dc, hdQ, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq]
      rcases hpmd with hp | hp
      · have a1 := hp e1 e1m
        have a2 := hp e2 e2m
        rw [act_e1 e1g, act_e1 hdg] at a1
        rw [act_e2 e1g, act_e2 hdg] at a2
        exact Or.inl ⟨decV_inj (actT_lt _ _) (actT_lt _ _) a1,
          decV_inj (actT_lt _ _) (actT_lt _ _) a2⟩
      · have a1 := hp e1 e1m
        have a2 := hp e2 e2m
        rw [act_e1 e1g, act_e1 hdg, ← decV_negT] at a1
        rw [act_e2 e1g, act_e2 hdg, ← decV_negT] at a2
        exact Or.inr ⟨decV_inj (actT_lt _ _) (negT_lt _) a1,
          decV_inj (actT_lt _ _) (negT_lt _) a2⟩
    rw [hW, hany] at h1
    simp at h1

theorem act_mul (a b : G) (v : Fin 3 → ZMod 3) : act33 (a * b) v = act33 b (act33 a v) := by
  simp only [act33, Units.val_mul, Matrix.vecMul_vecMul]

theorem fix_of_same {y s : G} (h : act33 y e0 = act33 s e0) : act33 (y * s⁻¹) e0 = e0 := by
  rw [act_mul, h, ← act_mul, mul_inv_cancel]
  simp [act33]

theorem stab_le {S X : Subgroup G} (hle : S ≤ X) (hS : Nat.card (S ⊓ stab0 : Subgroup G) = 8)
    (hX : Nat.card {g : GL (Fin 3) (ZMod 3) // g ∈ X ∧ act33 g e0 = e0} = 8) :
    X ⊓ stab0 ≤ S := by
  have hle' : S ⊓ stab0 ≤ X ⊓ stab0 := inf_le_inf_right _ hle
  have he := Subgroup.eq_of_le_of_card_ge hle' (by rw [← card_fix_eq, hX, hS])
  intro z hz
  rw [← he] at hz
  exact (Subgroup.mem_inf.1 hz).1

theorem code_facts (y : G) (hy : act33 y e0 = e0) :
    Good (encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3))) ∧
      ofCode (encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3))) = y ∧
      encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
        1 + 27 * (encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) / 27) ∧
      encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) / 27 < 729 := by
  have h1 := good_encode y
  have h2 := ofCode_encode y
  have h3 : encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) < 19683 := by
    have := encode_lt (y : Matrix (Fin 3) (Fin 3) (ZMod 3))
    norm_num at this
    exact this
  have h4 := (fix_iff h1).1 (by rw [h2]; exact hy)
  refine ⟨h1, h2, by omega, by omega⟩

theorem shape_facts {g : List ℕ} {kind : ℕ} {chs : List (List (ℕ × ℕ × List (List ℕ)))}
    (h : shapeK g kind chs = true) : (∀ g' ∈ g, Good g') ∧
      ∀ grp ∈ chs, ∀ c ∈ grp, c.1 < 2 ∨ (kind ≠ 1 ∧ nonemptyT c.2.2 = true) := by
  unfold shapeK at h
  rw [Bool.and_eq_true, allK_iff, allK_iff] at h
  refine ⟨fun g' hg' => (good_iff_detT g').2 (h.1 g' hg'), fun grp hgrp c hc => ?_⟩
  have := (allK_iff _ _).1 (h.2 grp hgrp) c hc
  simp only [Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, Bool.not_eq_true'] at this
  rcases this with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨fun e => ?_, h2⟩
    rw [e] at h1
    exact absurd h1 (by decide)

theorem getD_mem_or' {α : Type} (L : List α) (l : ℕ) (d : α) : L.getD l d ∈ L ∨ L.getD l d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[l]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

theorem stage1_sound {G' : List (List ℕ)} {Ms : List ℕ} {i : ℕ} {g : List ℕ}
    {R : List (ℕ × ℕ × ℕ)} {M : ℕ} {reps : List ℕ} {cov : List (ℕ × ℕ)}
    {chs : List (List (ℕ × ℕ × List (List ℕ)))} (hm : memT g M R = true)
    (hg : ∀ g' ∈ g, Good g') (h : stage1K G' Ms i g R M reps cov chs = true)
    (hsh : ∀ grp ∈ chs, ∀ c ∈ grp, c.1 < 2)
    (hj : ∀ j, i < j → j < lenK G' → Claim (subL (G'.getD j []))) : Claim (subL g) := by
  intro X hle hτ hcard hnon hD hE
  obtain ⟨hL, hA, hB, -⟩ := memT_sound hm hg
  obtain ⟨-, -, hsc⟩ := stab_sound hm hg
  unfold stage1K at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h8, hcov⟩, hz⟩ := h
  have hex : ∃ y ∈ X ⊓ stab0, y ∉ subL g := by
    by_contra hne
    push Not at hne
    have hle2 : X ⊓ stab0 ≤ subL g ⊓ stab0 := fun z hz =>
      Subgroup.mem_inf.2 ⟨hne z hz, (Subgroup.mem_inf.1 hz).2⟩
    have he := le_antisymm (inf_le_inf_right stab0 hle) hle2
    have : stabN R = 8 := by rw [← hsc, he, ← card_fix_eq, hcard]
    rw [this] at h8
    exact absurd h8 (by decide)
  obtain ⟨y, hyX, hyS⟩ := hex
  obtain ⟨hyX, hy0⟩ := Subgroup.mem_inf.1 hyX
  obtain ⟨yg, yo, ye, ya⟩ := code_facts y hy0
  generalize encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) = yc at yg yo ye ya
  subst yo
  have hW := (hD _ hyX (Or.inl hy0)).1
  rw [← blockT_iff yg] at hW
  obtain ⟨d, k, hd, hdr⟩ := covT_sound hcov (yc / 27) ya (by rw [← ye]; exact (good_iff_detT _).1 yg)
    (fun _ => by rw [← ye]; exact hW)
  rw [← ye] at hdr
  have hrg : Good (getF reps 19683 k) := good_of_mulK_left (hdr ▸ yg)
  have hrm : getF reps 19683 k ∈ reps := by
    rcases (getF_eq reps 19683 k ▸ getD_mem_or (L := reps) (l := k) (d := 19683)) with h1 | h1
    · exact h1
    · rw [h1, mulK_sentinel] at hdr
      omega
  obtain ⟨-, hdg, hdS⟩ := hA d hd
  have hy : ofCode yc = ofCode d * ofCode (getF reps 19683 k) := by rw [hdr, ofCode_mulK hdg hrg]
  have hrX : ofCode (getF reps 19683 k) ∈ X := by
    have : ofCode (getF reps 19683 k) = (ofCode d)⁻¹ * ofCode yc := by rw [hy]; group
    rw [this]
    exact X.mul_mem (X.inv_mem (hle hdS)) hyX
  obtain ⟨c, hc, hck⟩ := zipK_mem hz hrm
  have hc1 : c.1 < 2 := by
    rcases getD_mem_or' chs 0 [] with h1 | h1
    · exact hsh _ h1 c hc
    · rw [h1] at hc
      simp at hc
  refine childK_sound hck hg hle hrg hrX (fun hb => ?_) hj (fun h2 => absurd h2 (by omega))
    hτ hcard hnon hD hE
  obtain ⟨-, -, hrS⟩ := hA _ hb
  exact hyS (by rw [hy]; exact (subL g).mul_mem hdS hrS)

theorem stage2_sound {G' : List (List ℕ)} {Ms : List ℕ} {i : ℕ} {g : List ℕ}
    {R : List (ℕ × ℕ × ℕ)} {M QM : ℕ} {qreps orr org ori : List ℕ} {uc : List (ℕ × ℕ)}
    {pw : List ℕ} {chs : List (List (ℕ × ℕ × List (List ℕ)))} (hm : memT g M R = true)
    (hg : ∀ g' ∈ g, Good g') (h : stage2K G' Ms i g R M QM qreps orr org ori uc pw chs = true)
    (hq : QM = 0 ∨ ∃ C, covT QM qreps false C = true)
    (hsh : ∀ grp ∈ chs, ∀ c ∈ grp, c.1 < 2 ∨ nonemptyT c.2.2 = true)
    (hj : ∀ j, i < j → j < lenK G' → Claim (subL (G'.getD j []))) : Claim (subL g) := by
  intro X hle hτ hcard hnon hD hE
  obtain ⟨hL, hA, hB, -⟩ := memT_sound hm hg
  obtain ⟨hs1, hs2, hsc⟩ := stab_sound hm hg
  unfold stage2K at h
  simp only [Bool.and_eq_true, Nat.beq_eq, and_assoc] at h
  obtain ⟨h8, hQM, hphi, hz1, hz2, huc, hz3⟩ := h
  subst hQM
  have hXS := stab_le hle (by rw [hsc, h8]) hcard
  have hQ : ∀ y ∈ subL g ⊓ stab0, bitT (stabM R) (encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3))) =
      true ∧ encode (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ stabL R := fun y hy =>
    ⟨(bitT_stabM R _).2 (hs2 y hy), hs2 y hy⟩
  have hQX : ∀ y ∈ X ⊓ stab0, y ∈ subL g ⊓ stab0 := fun y hy =>
    Subgroup.mem_inf.2 ⟨hXS hy, (Subgroup.mem_inf.1 hy).2⟩
  by_cases hall : ∀ y ∈ X, ∃ c ∈ oneK :: R.map (·.1), act33 y e0 = decV (c % 27)
  · have hXeq : X = subL g := by
      refine le_antisymm (fun y hy => ?_) hle
      obtain ⟨c, hc, hyc⟩ := hall y hy
      obtain ⟨-, hcg, hcS⟩ := hA c ((hL c).2 hc)
      have hz : y * (ofCode c)⁻¹ ∈ X ⊓ stab0 := by
        refine Subgroup.mem_inf.2 ⟨X.mul_mem hy (X.inv_mem (hle hcS)), ?_⟩
        rw [mem_stab0]
        exact fix_of_same (by rw [hyc, act_e0 hcg])
      have := (subL g).mul_mem (Subgroup.mem_inf.1 (hQX _ hz)).1 hcS
      rwa [inv_mul_cancel_right] at this
    subst hXeq
    exact phiT_sound hm hg hphi hτ hcard hnon hD hE
  push Not at hall
  obtain ⟨y, hyX, hy⟩ := hall
  have hnot : ∀ c ∈ oneK :: R.map (·.1), act33 y e0 ≠ decV (c % 27) := hy
  have hyS : y ∉ subL g := by
    intro hyS
    have hb := hB y hyS
    refine hnot _ ((hL _).1 hb) ?_
    rw [← act_e0 (good_encode y), ofCode_encode]
  have hn := CFSG.RankThree.PartTwo.Sec21.FF79.GL33.encV_lt (act33 y e0)
  have hdu := CFSG.RankThree.PartTwo.Sec21.FF79.GL33.decV_encV (act33 y e0)
  generalize CFSG.RankThree.PartTwo.Sec21.FF79.GL33.encV (act33 y e0) = n at hn hdu
  have hn1 : 1 ≤ n := by
    by_contra h0
    have h0' : n = 0 := by omega
    subst h0'
    have hz : decV 0 = 0 := by
      funext j
      fin_cases j <;> rfl
    have : act33 (y * y⁻¹) e0 = 0 := by
      rw [act_mul, ← hdu, hz]
      exact Matrix.zero_vecMul _
    rw [mul_inv_cancel] at this
    have h1 := congrFun this 0
    simp [act33, e0] at h1
  rcases ucovK_sound huc n hn1 hn with ho | ⟨s, k, hsM, hsk⟩
  · obtain ⟨c, hc, hcn⟩ := (bitT_orbM R n).1 ho
    exact absurd (by rw [← hdu, hcn]) (hnot c hc)
  obtain ⟨-, hsg, hsS⟩ := hA s hsM
  rw [getF_eq] at hsk
  cases hok : orr[k]? with
  | none =>
    rw [hok] at hsk
    exact absurd hsk (by have := actT_lt n s; simp at this ⊢; omega)
  | some r =>
  rw [hok] at hsk
  simp only [Option.getD_some] at hsk
  obtain ⟨hk, hkr⟩ := List.getElem?_eq_some_iff.1 hok
  obtain ⟨l1, p1⟩ := zipK_idx hz1
  obtain ⟨l2, p2⟩ := zipK_idx hz2
  obtain ⟨l3, p3⟩ := zipK_idx hz3
  have hk1 : k < org.length := l1 ▸ hk
  have q1 := p1 k hk hk1
  have q2 := p2 k hk1 (l2 ▸ hk1)
  have q3 := p3 k hk1 (l3 ▸ hk1)
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at q1 q2
  rw [hkr] at q1
  generalize org[k] = hc at q1 q2 q3
  obtain ⟨hcg, hcg'⟩ := good_of_mulK_eq_oneK q2
  set y' := y * ofCode s with hy'
  have hy'X : y' ∈ X := X.mul_mem hyX (hle hsS)
  have e1 : act33 y' e0 = act33 (ofCode hc) e0 := by
    rw [hy', act_mul, ← hdu, act_decV hsg hn, act_e0 hcg, q1.1, hsk]
  have hz0 := fix_of_same e1
  obtain ⟨zg, zo, ze, za⟩ := code_facts _ hz0
  generalize encode ((y' * (ofCode hc)⁻¹ : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = zc
    at zg zo ze za
  have hQ0 : stabM R ≠ 0 := by
    intro h0
    have := (bitT_stabM R oneK).2 ((mem_stabL R oneK).2 ⟨List.mem_cons_self .., by decide⟩)
    rw [h0, bitT_eq] at this
    simp [bitK] at this
  obtain ⟨C, hC⟩ := hq.resolve_left hQ0
  obtain ⟨d, k', hdM, hdt⟩ := covT_sound hC (zc / 27) za (by rw [← ze]; exact (good_iff_detT _).1 zg)
    (fun h => absurd h (by decide))
  rw [← ze] at hdt
  have htg : Good (getF qreps 19683 k') := good_of_mulK_left (hdt ▸ zg)
  have htm : getF qreps 19683 k' ∈ qreps := by
    rcases (getF_eq qreps 19683 k' ▸ getD_mem_or (L := qreps) (l := k') (d := 19683)) with h1 | h1
    · exact h1
    · rw [h1, mulK_sentinel] at hdt
      omega
  generalize getF qreps 19683 k' = t at htg htm hdt
  obtain ⟨-, hdg, hdS⟩ := hs1 d ((bitT_stabM R d).1 hdM)
  have hdS' := (Subgroup.mem_inf.1 hdS).1
  have e2 : ofCode d * ofCode t = y' * (ofCode hc)⁻¹ := by
    rw [← ofCode_mulK hdg htg, ← hdt, zo]
  have e3 : ofCode (mulK t hc) = (ofCode d)⁻¹ * y' := by
    rw [ofCode_mulK htg hcg, eq_inv_mul_of_mul_eq e2]
    group
  have hxX : ofCode (mulK t hc) ∈ X := by
    rw [e3]
    exact X.mul_mem (X.inv_mem (hle hdS')) hy'X
  obtain ⟨c, hc', hck⟩ := zipK_mem q3 htm
  refine childK_sound hck hg hle (good_mulK htg hcg) hxX (fun hb => ?_) hj (fun h2 => ?_)
    hτ hcard hnon hD hE
  · obtain ⟨-, -, hxS⟩ := hA _ hb
    apply hyS
    have h1 : y' ∈ subL g := by
      have := (subL g).mul_mem hdS' hxS
      rwa [e3, mul_inv_cancel_left] at this
    have := (subL g).mul_mem h1 ((subL g).inv_mem hsS)
    rwa [hy', mul_inv_cancel_right] at this
  · refine ⟨(hsh _ (List.getElem_mem _) c hc').resolve_left (by omega), fun _ => hXS, hQ⟩

theorem nodeK_sound {G' : List (List ℕ)} {Ms : List ℕ} {i : ℕ} {g : List ℕ}
    {R : List (ℕ × ℕ × ℕ)} {M kind QM : ℕ} {qreps reps : List ℕ} {cov : List (ℕ × ℕ)}
    {orr org ori : List ℕ} {uc : List (ℕ × ℕ)} {pw : List ℕ}
    {chs : List (List (ℕ × ℕ × List (List ℕ)))}
    (h : nodeK G' Ms i g R M kind QM qreps reps cov orr org ori uc pw chs = true)
    (hsh : shapeK g kind chs = true) (hq : QM = 0 ∨ ∃ C, covT QM qreps false C = true)
    (hj : ∀ j, i < j → j < lenK G' → Claim (subL (G'.getD j []))) : Claim (subL g) := by
  obtain ⟨hg, hsh⟩ := shape_facts hsh
  unfold nodeK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hm, h⟩ := h
  obtain ⟨-, hs2, hsc⟩ := stab_sound hm hg
  match kind, h, hsh with
  | 0, h, _ =>
    intro X hle _ hcard _ _ _
    exfalso
    change (!Nat.beq (8 % stabN R) 0) = true at h
    have hdv := Subgroup.card_dvd_of_le (inf_le_inf_right stab0 hle)
    rw [hsc, ← card_fix_eq, hcard] at hdv
    rw [Nat.mod_eq_zero_of_dvd hdv] at h
    exact absurd h (by decide)
  | 1, h, hsh =>
    exact stage1_sound hm hg h (fun grp hgrp c hc => (hsh grp hgrp c hc).resolve_right
      (fun h' => h'.1 rfl)) hj
  | 2, h, _ =>
    intro X hle _ hcard hnon _ _
    exfalso
    change (Nat.beq (stabN R) 8 && allK (fun a => allK (fun b => Nat.beq (mulK a b) (mulK b a))
      (stabL R)) (stabL R)) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    have hXS := stab_le hle (by rw [hsc, h.1]) hcard
    obtain ⟨a, haX, b, hbX, ha0, hb0, hab⟩ := hnon
    have hmem : ∀ z ∈ X, act33 z e0 = e0 → encode (z : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈
        stabL R := fun z hz hz0 =>
      hs2 z (Subgroup.mem_inf.2 ⟨hXS (Subgroup.mem_inf.2 ⟨hz, hz0⟩), hz0⟩)
    have hc := (allK_iff _ _).1 ((allK_iff _ _).1 h.2 _ (hmem a haX ha0)) _ (hmem b hbX hb0)
    rw [Nat.beq_eq] at hc
    apply hab
    have := congrArg ofCode hc
    rwa [ofCode_mulK (good_encode a) (good_encode b), ofCode_mulK (good_encode b) (good_encode a),
      ofCode_encode, ofCode_encode] at this
  | 3, h, hsh =>
    exact stage2_sound hm hg h hq (fun grp hgrp c hc => (hsh grp hgrp c hc).imp_right
      (fun h' => h'.2)) hj
  | k + 4, h, _ => exact absurd h (by simp)

theorem ofCode_tau {τ : G} (h0 : act33 τ e0 = e0) (h1 : act33 τ e1 = -e1)
    (h2 : act33 τ e2 = -e2) : ofCode 13285 = τ := by
  have hg : Good 13285 := (good_iff_detT _).2 (by decide)
  apply Units.ext
  rw [coe_ofCode hg, toM_eq_dec]
  have r0 : (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 = e0 := by
    rw [← h0]
    funext j
    simp [act33, Matrix.vecMul, dotProduct, Fin.sum_univ_three, e0]
  have r1 : (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 = -e1 := by
    rw [← h1]
    funext j
    simp [act33, Matrix.vecMul, dotProduct, Fin.sum_univ_three, e1]
  have r2 : (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 = -e2 := by
    rw [← h2]
    funext j
    simp [act33, Matrix.vecMul, dotProduct, Fin.sum_univ_three, e2]
  funext i
  fin_cases i
  · change dec 13285 0 = (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0
    rw [r0]
    funext j
    fin_cases j <;> decide
  · change dec 13285 1 = (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1
    rw [r1]
    funext j
    fin_cases j <;> decide
  · change dec 13285 2 = (τ : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2
    rw [r2]
    funext j
    fin_cases j <;> decide

theorem tree_sound {G' : List (List ℕ)} (hl : lenK G' = 48) (hroot : G'.getD 0 [] = [13285])
    (hn : ∀ i < 48, ∃ (Ms : List ℕ) (R : List (ℕ × ℕ × ℕ)) (M kind QM : ℕ)
      (qreps reps : List ℕ) (cov : List (ℕ × ℕ)) (orr org ori : List ℕ) (uc : List (ℕ × ℕ))
      (pw : List ℕ) (chs : List (List (ℕ × ℕ × List (List ℕ)))),
      nodeK G' Ms i (G'.getD i []) R M kind QM qreps reps cov orr org ori uc pw chs = true ∧
        shapeK (G'.getD i []) kind chs = true ∧ (QM = 0 ∨ ∃ C, covT QM qreps false C = true)) :
    ∀ X : Subgroup G, GL33At X e0 e1 e2 := by
  have key : ∀ n i, 48 - n ≤ i → i < 48 → Claim (subL (G'.getD i [])) := by
    intro n
    induction n with
    | zero => intro i h1 h2; omega
    | succ n ih =>
      intro i h1 h2
      by_cases h3 : 48 - n ≤ i
      · exact ih i h3 h2
      obtain ⟨Ms, R, M, kind, QM, qreps, reps, cov, orr, org, ori, uc, pw, chs, a1, a2, a3⟩ :=
        hn i h2
      exact nodeK_sound a1 a2 a3 (fun j hj1 hj2 => ih j (by omega) (by omega))
  intro X hτ
  obtain ⟨τ, hτX, t0, t1, t2⟩ := hτ
  have hroot' := key 48 0 (by omega) (by omega)
  rw [hroot] at hroot'
  refine hroot' X (subL_le fun g hg => ?_) ⟨τ, hτX, t0, t1, t2⟩
  rw [List.mem_singleton.1 hg, ofCode_tau t0 t1 t2]
  exact hτX

end CFSG.KC.GL33T

end
