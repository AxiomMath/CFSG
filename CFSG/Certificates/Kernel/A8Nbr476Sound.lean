module

public import Certificates.Data.Kernel.A8Nbr476K
import Mathlib.Tactic.ReduceModChar
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.KC.A8N476

open Certificates.A8Nbr476

theorem nadd (x y : ℕ) : Nat.add x y = x + y := rfl
theorem nmul (x y : ℕ) : Nat.mul x y = x * y := rfl
theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
theorem npow (x y : ℕ) : Nat.pow x y = x ^ y := rfl

theorem dec_mk (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : ℕ) :
    dec ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ =
      !![(a0 : ZMod 7), a1, a2, a3; b0, b1, b2, b3; c0, c1, c2, c3; d0, d1, d2, d3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dec_eta (A : Q) : A = ⟨⟨A.r0.x0, A.r0.x1, A.r0.x2, A.r0.x3⟩, ⟨A.r1.x0, A.r1.x1, A.r1.x2, A.r1.x3⟩,
    ⟨A.r2.x0, A.r2.x1, A.r2.x2, A.r2.x3⟩, ⟨A.r3.x0, A.r3.x1, A.r3.x2, A.r3.x3⟩⟩ := rfl

theorem cast_mod7 (x : ℕ) : ((Nat.mod x 7 : ℕ) : ZMod 7) = x := by
  rw [nmod, ZMod.natCast_mod]

theorem dot4_cast (c0 c1 c2 c3 y0 y1 y2 y3 : ℕ) :
    ((dot4 c0 c1 c2 c3 y0 y1 y2 y3 : ℕ) : ZMod 7) =
      c0 * y0 + c1 * y1 + c2 * y2 + c3 * y3 := by
  rw [dot4, cast_mod7]
  simp only [nadd, nmul]
  push_cast
  ring

theorem dec_mulQ (A B : Q) : dec (mulQ A B) = dec A * dec B := by
  rw [dec_eta A, dec_eta B]
  simp only [mulQ, linV, dec_mk, dot4_cast]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem dec_idQ : dec idQ = 1 := by
  rw [idQ, dec_mk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem six_eq : (6 : ZMod 7) = -1 := by decide

theorem five_eq : (5 : ZMod 7) = -2 := by decide

theorem four_eq : (4 : ZMod 7) = -3 := by decide

theorem dec_subI (A : Q) : dec (subI A) = dec A - 1 := by
  rw [dec_eta A]
  simp only [subI, dec_mk, nadd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [six_eq, sub_eq_add_neg]

theorem z7_iff (x : ℕ) : z7 x = true ↔ (x : ZMod 7) = 0 := by
  rw [z7, Nat.beq_eq, nmod]
  constructor
  · intro h
    rw [← ZMod.natCast_mod, h, Nat.cast_zero]
  · intro h
    have := (ZMod.natCast_eq_natCast_iff' x 0 7).1 (by rw [h, Nat.cast_zero])
    simpa using this

theorem zQ_iff (A : Q) : zQ A = true ↔ dec A = 0 := by
  rw [dec_eta A, dec_mk, ← Matrix.ext_iff]
  simp only [zQ, zV, Bool.and_eq_true, z7_iff, Fin.forall_fin_succ, Fin.forall_fin_one]
  simp [and_assoc]

theorem e2_iff (p q r s : ℕ) : e2 p q r s = true ↔ (p : ZMod 7) * s = q * r := by
  rw [e2, Nat.beq_eq, nmod, nmod, nmul, nmul, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  rfl

theorem m2_sound (u v : V) (h : m2 u v = true) (k l : Fin 4) :
    (u.get k : ZMod 7) * v.get l = u.get l * v.get k := by
  simp only [m2, Bool.and_eq_true, e2_iff] at h
  obtain ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ := h
  fin_cases k <;> fin_cases l <;> simp [V.get] <;> (first | assumption | (symm; assumption))

theorem m2_symm {u v : V} (h : ∀ k l : Fin 4, (u.get k : ZMod 7) * v.get l = u.get l * v.get k)
    (k l : Fin 4) : (v.get k : ZMod 7) * u.get l = v.get l * u.get k := by
  rw [mul_comm, h l k, mul_comm]

theorem m2_self (u : V) (k l : Fin 4) : (u.get k : ZMod 7) * u.get l = u.get l * u.get k :=
  mul_comm _ _

theorem minorsB_sound (A : Q) (h : minorsB A = true) (i j k l : Fin 4) :
    dec A i k * dec A j l = dec A i l * dec A j k := by
  simp only [minorsB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ := h
  have s01 := m2_sound _ _ h01
  have s02 := m2_sound _ _ h02
  have s03 := m2_sound _ _ h03
  have s12 := m2_sound _ _ h12
  have s13 := m2_sound _ _ h13
  have s23 := m2_sound _ _ h23
  have t01 := m2_symm s01
  have t02 := m2_symm s02
  have t03 := m2_symm s03
  have t12 := m2_symm s12
  have t13 := m2_symm s13
  have t23 := m2_symm s23
  have d0 := m2_self A.r0
  have d1 := m2_self A.r1
  have d2 := m2_self A.r2
  have d3 := m2_self A.r3
  simp only [dec, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp only [Q.row] <;> simp only [Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    apply_assumption

theorem transvB_sound (X : Q) (h : transvB X = true) : IsTransv (dec X) := by
  simp only [transvB, transvY, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [IsTransv, ← dec_subI]
  refine ⟨fun hX => ?_, ?_, minorsB_sound _ h3⟩
  · have : zQ (subI X) = true := (zQ_iff _).2 (by rw [dec_subI, hX, sub_self])
    rw [this] at h1
    exact Bool.noConfusion h1
  · rw [← dec_mulQ]
    exact (zQ_iff _).1 h2

theorem inv_eq_pow (y : ZMod 7) : y⁻¹ = y ^ 5 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h6 : y ^ 6 = 1 := ZMod.pow_card_sub_one_eq_one hy
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h6)).symm

theorem inv7_cast (x : ℕ) : ((inv7 x : ℕ) : ZMod 7) = (x : ZMod 7)⁻¹ := by
  rw [inv7, cast_mod7, npow, Nat.cast_pow, inv_eq_pow]

theorem val_cast (a : ZMod 7) : ((a.val : ℕ) : ZMod 7) = a := ZMod.natCast_zmod_val a

theorem dec_basQ (c : Case) : dec (basQ c.2.1.val c.2.2.1.val) = bas c := by
  rw [basQ, dec_mk, bas]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [val_cast, six_eq]

theorem dec_basInvQ (c : Case) : dec (basInvQ c.2.1.val c.2.2.1.val) = basInv c := by
  rw [basInvQ, basInvSD, dec_mk, basInv]
  simp only [dQ, nadd, nmul]
  push_cast
  simp only [inv7_cast]
  push_cast
  simp only [val_cast, six_eq, five_eq, four_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf

theorem blk_eq (M : M3) : blk M = !![1, 0, 0, 0; 0, M 0 0, M 0 1, M 0 2; 0, M 1 0, M 1 1, M 1 2;
    0, M 2 0, M 2 1, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blk_mul (M N : M3) : blk (M * N) = blk M * blk N := by
  rw [blk_eq, blk_eq, blk_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem dec_psiQ (c : Case) : dec (psiQ c.1 c.2.2.2.val) = blk (psi c) := by
  obtain ⟨t, a, b, m⟩ := c
  cases t <;> simp only [psiQ, dec_mk, blk_eq, psi] <;> ext i j <;>
    fin_cases i <;> fin_cases j <;> simp [val_cast, six_eq]

theorem dec_psiInvQ (c : Case) : dec (psiInvQ c.1 c.2.2.2.val) = blk (psiInv c) := by
  obtain ⟨t, a, b, m⟩ := c
  cases t <;> simp only [psiInvQ, psiInvN, dec_mk, blk_eq, psiInv, nmul] <;> ext i j <;>
    fin_cases i <;> fin_cases j <;> simp [val_cast, inv7_cast]

theorem dec_wQ (t : Bool) (i : Fin 3) : dec (wQ t i.val) = blk (wgen t i) := by
  cases t <;> fin_cases i <;> decide

theorem dec_genLQ (c : Case) (i : Fin 3) :
    dec (genLQ c.1 c.2.1.val c.2.2.1.val c.2.2.2.val i.val) = genL c i := by
  rw [genLQ, dec_mulQ, dec_mulQ, dec_mulQ, dec_mulQ, dec_basQ, dec_basInvQ, dec_psiQ, dec_psiInvQ,
    dec_wQ, genL, blk_mul, blk_mul]

theorem dec_genKQ (k : Fin 3) : dec (genKQ k.val) = genK k := by
  fin_cases k <;> decide

theorem dec_pick (c : Case) (k : Fin 6) : dec (pick (gensC c) k.val) = gens c k := by
  fin_cases k
  · exact dec_genLQ c 0
  · exact dec_genLQ c 1
  · exact dec_genLQ c 2
  · exact dec_genKQ 0
  · exact dec_genKQ 1
  · exact dec_genKQ 2

theorem dec_prodQ (c : Case) (w : List (Fin 6)) :
    dec (prodQ (gensC c) w) = (w.map (gens c)).prod := by
  induction w with
  | nil => exact dec_idQ
  | cons l w ih =>
    change dec (mulQ (pick (gensC c) l.val) (prodQ (gensC c) w)) = _
    rw [dec_mulQ, ih, dec_pick, List.map_cons, List.prod_cons]

theorem wordsB_sound (L : List (Case × List (Fin 6))) (h : wordsB L = true) :
    ∀ e ∈ L, IsTransv ((e.2.map (gens e.1)).prod) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    change (wordB e && wordsB L) = true at h
    rw [Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · rw [← dec_prodQ]
      exact transvB_sound _ h.1
    · exact ih h.2 e' he'

theorem mem_vals (x : ZMod 7) : x ∈ vals := by
  revert x
  decide

theorem mem_allCases (c : Case) : c ∈ allCases ↔ c.2.2.2 ≠ 0 ∧ c.2.1 * c.2.2.1 ≠ 1 := by
  obtain ⟨t, a, b, m⟩ := c
  cases t <;> simp [allCases, List.mem_flatMap, List.mem_filter, mem_vals]

theorem allBelow_sound (f : ℕ → Bool) (N : ℕ) (h : allBelow f N = true) : ∀ n < N, f n = true := by
  induction N with
  | zero => intro n hn; omega
  | succ N ih =>
    change (f N && allBelow f N) = true at h
    rw [Bool.and_eq_true] at h
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact ih h.2 n hn
    · exact h.1

theorem memN_sound (n : ℕ) (L : List ℕ) (h : memN n L = true) : n ∈ L := by
  induction L with
  | nil => exact Bool.noConfusion h
  | cons x L ih =>
    change (Nat.beq n x || memN n L) = true at h
    rw [Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem mem_codesL {β : Type} (L : List (Case × β)) (n : ℕ) (h : n ∈ codesL L) :
    ∃ e ∈ L, caseCode e.1 = n := by
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons e L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨e, List.mem_cons_self, rfl⟩
    · obtain ⟨e', he', hc⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hc⟩

theorem mem_codesC (L : List Case) (n : ℕ) (h : n ∈ codesC L) : ∃ c ∈ L, caseCode c = n := by
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons c L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨c, List.mem_cons_self, rfl⟩
    · obtain ⟨c', hc', hc⟩ := ih h
      exact ⟨c', List.mem_cons_of_mem _ hc', hc⟩

theorem caseCode_eq (t : Bool) (a b m : ZMod 7) : caseCode (t, a, b, m) =
    343 * (if t then 1 else 0) + 49 * a.val + 7 * b.val + m.val := by
  cases t <;> rfl

theorem caseCode_inj {c c' : Case} (h : caseCode c = caseCode c') : c = c' := by
  obtain ⟨t, a, b, m⟩ := c
  obtain ⟨t', a', b', m'⟩ := c'
  rw [caseCode_eq, caseCode_eq] at h
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hm := ZMod.val_lt m
  have ha' := ZMod.val_lt a'
  have hb' := ZMod.val_lt b'
  have hm' := ZMod.val_lt m'
  have e1 : m.val = m'.val := by split_ifs at h <;> omega
  have e2 : b.val = b'.val := by split_ifs at h <;> omega
  have e3 : a.val = a'.val := by split_ifs at h <;> omega
  have e4 : t = t' := by cases t <;> cases t' <;> simp at h <;> first | rfl | omega
  rw [ZMod.val_injective _ e1, ZMod.val_injective _ e2, ZMod.val_injective _ e3, e4]

theorem coverB_sound (h : coverB (codesL wordData) (codesC excCases) = true) (c : Case)
    (hc : c ∈ allCases) :
    (bas c * basInv c = 1 ∧ basInv c * bas c = 1 ∧ psi c * psiInv c = 1 ∧ psiInv c * psi c = 1) ∧
      (c ∉ excCases → c ∈ wordData.map Prod.fst) := by
  obtain ⟨t, a, b, m⟩ := c
  rw [mem_allCases] at hc
  simp only at hc
  have hn := allBelow_sound _ _ h (caseCode (t, a, b, m)) (by
    rw [caseCode_eq]
    have := ZMod.val_lt a
    have := ZMod.val_lt b
    have := ZMod.val_lt m
    split_ifs <;> omega)
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hm := ZMod.val_lt m
  have d0 : caseCode (t, a, b, m) % 7 = m.val := by rw [caseCode_eq]; split_ifs <;> omega
  have d1 : caseCode (t, a, b, m) / 7 % 7 = b.val := by rw [caseCode_eq]; split_ifs <;> omega
  have d2 : caseCode (t, a, b, m) / 49 % 7 = a.val := by rw [caseCode_eq]; split_ifs <;> omega
  have d4 : caseCode (t, a, b, m) / 343 = if t then 1 else 0 := by
    rw [caseCode_eq]
    split_ifs <;> omega
  have d3 : Nat.beq (caseCode (t, a, b, m) / 343) 1 = t := by
    rw [d4]
    cases t <;> rfl
  have h1 : z7 (caseCode (t, a, b, m)) = false := by
    rw [Bool.eq_false_iff, ne_eq, z7_iff, ← ZMod.natCast_mod, d0, val_cast]
    exact hc.1
  have h2 : Nat.beq (Nat.mod (Nat.mul (Nat.mod (Nat.div (caseCode (t, a, b, m)) 49) 7)
      (Nat.mod (Nat.div (caseCode (t, a, b, m)) 7) 7)) 7) 1 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq, nmod, nmod, nmod, ndiv, ndiv, nmul, d1, d2]
    intro h1
    have : Fact (1 < 7) := ⟨by decide⟩
    apply hc.2
    apply ZMod.val_injective
    rw [ZMod.val_mul, ZMod.val_one]
    exact h1
  have hv : validN (caseCode (t, a, b, m)) = true := by
    rw [validN, h1, h2]
    rfl
  simp only [okN, hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, nmod, ndiv,
    d0, d1, d2, d3] at hn
  obtain ⟨hi, hw⟩ := hn
  refine ⟨?_, ?_⟩
  · simp only [invB, Bool.and_eq_true, zQ_iff, dec_subI, dec_mulQ, sub_eq_zero] at hi
    obtain ⟨⟨⟨i1, i2⟩, i3⟩, i4⟩ := hi
    have eb := dec_basQ (t, a, b, m)
    have ebi := dec_basInvQ (t, a, b, m)
    have ep := dec_psiQ (t, a, b, m)
    have epi := dec_psiInvQ (t, a, b, m)
    simp only at eb ebi ep epi
    rw [eb, ebi] at i1 i2
    rw [ep, epi, ← blk_mul] at i3 i4
    have hb1 : blk (1 : M3) = 1 := by decide
    rw [← hb1] at i3 i4
    have blk_inj : ∀ M N : M3, blk M = blk N → M = N := by
      intro M N hMN
      ext i j
      have := congrFun (congrFun hMN i.succ) j.succ
      simpa [blk] using this
    exact ⟨i1, i2, blk_inj _ _ i3, blk_inj _ _ i4⟩
  · intro hx
    rcases hw with he | hw
    · obtain ⟨c', hc', hcc⟩ := mem_codesC _ _ (memN_sound _ _ he)
      rw [caseCode_inj hcc] at hc'
      exact absurd hc' hx
    · obtain ⟨e, he, hcc⟩ := mem_codesL _ _ (memN_sound _ _ hw)
      rw [← caseCode_inj hcc]
      exact List.mem_map_of_mem he

theorem dec_rowsQ (r : List (List (ZMod 7))) : dec (rowsQ r) = ofRows r := by
  rw [rowsQ, dec_mk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rowE, ofRows, val_cast]

theorem all6_sound (f : ℕ → Bool) (h : all6 f = true) (k : Fin 6) : f k.val = true := by
  simp only [all6, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩ := h
  fin_cases k <;> assumption

theorem monB_sound (L : List (Case × List (List (ZMod 7)) × List (List (ZMod 7))))
    (h : monB L = true) : ∀ e ∈ L, ofRows e.2.1 * ofRows e.2.2 = 1 ∧
      ∀ k : Fin 6, IsMonCube (ofRows e.2.1 * gens e.1 k * ofRows e.2.2) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    change (monE e && monB L) = true at h
    rw [Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · have h1 := h.1
      rw [monE, Bool.and_eq_true] at h1
      obtain ⟨hinv, hk⟩ := h1
      rw [zQ_iff, dec_subI, dec_mulQ, dec_rowsQ, dec_rowsQ, sub_eq_zero] at hinv
      refine ⟨hinv, fun k => ?_⟩
      have hk' := all6_sound _ hk k
      beta_reduce at hk'
      rw [dec_mulQ, dec_mulQ, dec_pick, dec_rowsQ, dec_rowsQ] at hk'
      exact hk'
    · exact ih h.2 e' he'

theorem a8Claim_of (hw : wordsB wordData = true)
    (hc : coverB (codesL wordData) (codesC excCases) = true) (hm : monB monData = true)
    (hl : allCases.length = 516) (hf : monData.map Prod.fst = excCases)
    (he : ∀ c ∈ excCases, c ∈ allCases) : A8Claim :=
  ⟨hl, fun c h => (coverB_sound hc c h).1, fun c h => (coverB_sound hc c h).2,
    wordsB_sound _ hw, hf, he, monB_sound _ hm⟩

end CFSG.KC.A8N476
