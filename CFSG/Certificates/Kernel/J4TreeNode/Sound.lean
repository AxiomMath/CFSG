module

public import Certificates.Data.Kernel.J4TreeNode
public import CFSG.Certificates.Kernel.J4Tree.CodeSound
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeFacts
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffHBase
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

theorem enumOK_spec {f : ℕ → ℕ → Bool} {l : List ℕ} {X u t : ℕ}
    (h : enumOK f l X u t = true) : ∀ m < 2 ^ l.length, f (prodFrom X l m) (u + 2 ^ t * m) = true := by
  induction l generalizing X u t with
  | nil =>
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    simpa [prodFrom, enumOK] using h
  | cons s l ih =>
    intro m hm
    unfold enumOK at h
    rw [Bool.and_eq_true] at h
    have hm2 : m / 2 < 2 ^ l.length := by
      rw [List.length_cons, pow_succ] at hm
      omega
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · have := ih h.1 (m / 2) hm2
      rw [prodFrom, if_neg (by omega)]
      have hm' : m = 2 * (m / 2) := by omega
      rwa [show u + 2 ^ t * m = u + 2 ^ (t + 1) * (m / 2) by
        rw [pow_succ]; nth_rewrite 1 [hm']; ring]
    · have := ih h.2 (m / 2) hm2
      rw [prodFrom, if_pos h1]
      have hm' : m = 2 * (m / 2) + 1 := by omega
      rwa [show u + 2 ^ t * m = u + 2 ^ t + 2 ^ (t + 1) * (m / 2) by
        rw [pow_succ]; nth_rewrite 1 [hm']; ring]

theorem enumZ_spec {f : ℕ → ℕ → ℕ → Bool} {l : List ℕ} {X u t : ℕ} {zs : List ℕ}
    (h : enumZ f l X u t zs = true) :
    ∀ m < 2 ^ l.length, ∃ z, f (prodFrom X l m) (u + 2 ^ t * m) z = true := by
  induction l generalizing X u t zs with
  | nil =>
    intro m hm
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    exact ⟨_, by simpa [prodFrom, enumZ] using h⟩
  | cons s l ih =>
    intro m hm
    unfold enumZ at h
    rw [Bool.and_eq_true] at h
    have hm2 : m / 2 < 2 ^ l.length := by
      rw [List.length_cons, pow_succ] at hm
      omega
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · obtain ⟨z, hz⟩ := ih h.1 (m / 2) hm2
      refine ⟨z, ?_⟩
      rw [prodFrom, if_neg (by omega)]
      have hm' : m = 2 * (m / 2) := by omega
      rwa [show u + 2 ^ t * m = u + 2 ^ (t + 1) * (m / 2) by
        rw [pow_succ]; nth_rewrite 1 [hm']; ring]
    · obtain ⟨z, hz⟩ := ih h.2 (m / 2) hm2
      refine ⟨z, ?_⟩
      rw [prodFrom, if_pos h1]
      have hm' : m = 2 * (m / 2) + 1 := by omega
      rwa [show u + 2 ^ t * m = u + 2 ^ t + 2 ^ (t + 1) * (m / 2) by
        rw [pow_succ]; nth_rewrite 1 [hm']; ring]

private theorem getD_reverse_map {β : Type*} (f : β → ℕ) (pre rest : List β) (d : β) {par : ℕ}
    (hp : par < pre.length) :
    ((pre.map f).reverse).getD (pre.length - 1 - par) 0 = f ((pre ++ rest).getD par d) := by
  have h1 : pre.length - 1 - par < (pre.map f).length := by rw [List.length_map]; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse h1,
    show (pre.map f).length - 1 - (pre.length - 1 - par) = par by rw [List.length_map]; omega,
    List.getElem?_map, List.getElem?_append_left hp, List.getElem?_eq_getElem hp]
  rfl

private theorem entsOK_gen {NA AI N NI kidU : List ℕ} (es : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    ∀ pre : List (ℕ × ℕ × ℕ × ℕ × ℕ),
    entsOK NA AI N NI kidU ((pre.map fun e => prodMask NA e.1).reverse) pre.length es = true →
    ∀ j < es.length,
      ((es.getD j default).2.1 ≠ 0 ∧ (es.getD j default).2.1 - 1 < kidU.length ∧
        kidU.getD ((es.getD j default).2.1 - 1) 0 = (es.getD j default).1) ∨
      ((es.getD j default).2.1 = 0 ∧ (es.getD j default).2.2.1 < pre.length + j ∧
        (es.getD j default).2.2.2.1 < N.length ∧
        M (M (N.getD (es.getD j default).2.2.2.1 0)
          (prodMask NA ((pre ++ es).getD (es.getD j default).2.2.1 default).1))
          (NI.getD (es.getD j default).2.2.2.1 0) =
          M (prodMask NA (es.getD j default).1) (prodMask AI (es.getD j default).2.2.2.2)) := by
  induction es with
  | nil => intro pre _ j hj; simp at hj
  | cons e es ih =>
    intro pre h j hj
    obtain ⟨u, kid, par, lab, v⟩ := e
    simp only [entsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      by_cases hk : kid = 0
      · right
        subst hk
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
          Nat.blt_eq, Nat.beq_eq] at h1
        obtain ⟨⟨hp, hl⟩, he⟩ := h1
        refine ⟨rfl, by omega, hl, ?_⟩
        rw [getD_reverse_map _ pre ((u, 0, par, lab, v) :: es) default hp] at he
        exact he
      · left
        have hk' : (kid != 0) = true := by simpa using hk
        rw [if_pos hk', Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h1
        exact ⟨hk, h1.2, h1.1⟩
    | succ j =>
      simp only [List.getD_cons_succ]
      have h2' : entsOK NA AI N NI kidU
          (((pre ++ [(u, kid, par, lab, v)]).map fun e => prodMask NA e.1).reverse)
          (pre ++ [(u, kid, par, lab, v)]).length es = true := by
        rw [List.map_append, List.reverse_append, List.length_append]
        exact h2
      have := ih _ h2' j (by simp only [List.length_cons] at hj; omega)
      rwa [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton,
        Nat.add_assoc, Nat.add_comm 1 j] at this

theorem entsOK_spec {NA AI N NI kidU : List ℕ} {es : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : entsOK NA AI N NI kidU [] 0 es = true) :
    ∀ j < es.length, let e := es.getD j default
      (e.2.1 ≠ 0 ∧ e.2.1 - 1 < kidU.length ∧ kidU.getD (e.2.1 - 1) 0 = e.1) ∨
      (e.2.1 = 0 ∧ e.2.2.1 < j ∧ e.2.2.2.1 < N.length ∧
        M (M (N.getD e.2.2.2.1 0) (prodMask NA (es.getD e.2.2.1 default).1)) (NI.getD e.2.2.2.1 0) =
          M (prodMask NA e.1) (prodMask AI e.2.2.2.2)) := by
  intro j hj
  have := entsOK_gen es [] h j hj
  rwa [List.nil_append, List.length_nil, Nat.zero_add] at this

private theorem incrFrom_spec : ∀ (lo : ℕ) (l : List ℕ), incrFrom lo l = true →
    l.Pairwise (· < ·) ∧ ∀ x ∈ l, lo ≤ x
  | _, [], _ => ⟨List.Pairwise.nil, by simp⟩
  | lo, x :: l, h => by
    simp only [incrFrom, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := incrFrom_spec (x + 1) l h2
    refine ⟨List.Pairwise.cons (fun y hy => by have := ih2 y hy; omega) ih1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1
    · have := ih2 y hy
      omega

private theorem testBit_foldl_lor {β : Type*} (g : β → ℕ) : ∀ (l : List β) (a u : ℕ),
    (l.foldl (fun acc x => acc ||| 2 ^ g x) a).testBit u = true →
      a.testBit u = true ∨ ∃ x ∈ l, g x = u
  | [], _, _, h => Or.inl h
  | x :: l, a, u, h => by
    rcases testBit_foldl_lor g l _ u h with h' | ⟨y, hy, hyu⟩
    · rw [Nat.testBit_or, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · rw [Nat.testBit_two_pow, decide_eq_true_eq] at h'
        exact Or.inr ⟨x, List.mem_cons_self .., h'⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hyu⟩

theorem orbOK_spec {S SI : List ℕ} {Y root : ℕ} {orb : List (ℕ × ℕ × ℕ × ℕ)}
    (h : orbOK S SI Y root orb = true) :
    root < orb.length ∧ (orb.map Prod.fst).Pairwise (· < ·) ∧ (∀ x ∈ orb, x.1 < 2 ^ 144) ∧
      ∀ i < orb.length, let p := orb.getD i default
        (i = root → p.1 = Y ∧ p.2.2.2 = 0) ∧
        (i ≠ root → p.2.1 < orb.length ∧ p.2.2.1 < S.length ∧
          p.2.2.2 = (orb.getD p.2.1 default).2.2.2 + 1 ∧
          p.1 = M (M (S.getD p.2.2.1 0) (orb.getD p.2.1 default).1) (SI.getD p.2.2.1 0)) := by
  unfold orbOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, (incrFrom_spec 0 _ h2).1, fun x hx => h3 x.1 (List.mem_map_of_mem hx), ?_⟩
  intro i hi
  have hmem : (orb.getD i default, i) ∈ orb.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have := h4 _ hmem
  by_cases hr : i = root
  · simp only [hr, if_true, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at this
    exact ⟨fun _ => ⟨by rw [hr]; exact this.1, by rw [hr]; exact this.2⟩, fun h => absurd hr h⟩
  · simp only [hr, if_false, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := this
    exact ⟨fun h => absurd h hr, fun _ => ⟨a1, a2, a3, a4⟩⟩

theorem coverBits_spec {ents : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {nonF : List (ℕ × List ℕ)} {u : ℕ}
    (h : (coverBits ents nonF).testBit u = true) :
    (∃ e ∈ ents, e.1 = u) ∨ ∃ c ∈ nonF, c.1 = u := by
  unfold coverBits at h
  rcases testBit_foldl_lor (fun u => u) (nonF.map Prod.fst) _ u h with h' | ⟨x, hx, rfl⟩
  · rcases testBit_foldl_lor (fun e => e.1) ents 0 u h' with h0 | h1
    · simp at h0
    · exact Or.inl h1
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact Or.inr ⟨c, hc, rfl⟩

theorem leadsOK_spec {L : List ℕ} (h : leadsOK L = true) :
    (∀ X ∈ L, utK (qconj X) = true ∧ leadOf (qconj X) < 66) ∧
      (L.map fun X => leadOf (qconj X)).Pairwise (· < ·) := by
  unfold leadsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun X hX => ⟨h1 X hX, h3 _ (List.mem_map_of_mem hX)⟩, (incrFrom_spec 0 _ h2).1⟩

@[expose] def idx (i j : ℕ) : ℕ := (j - i - 1) * 12 - (j - i - 1) * (j - i) / 2 + i

@[expose] def UT (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Prop :=
  ∀ i j : Fin 12, (j < i → A i j = 0) ∧ A i i = 1

private theorem codeMat_apply {a : Code} {Y : ℕ} (ha : RC a Y) (i j : Fin 12) :
    burnsideJ4NP_codeMat a i j = if Y.testBit (12 * i + j) then 1 else 0 := by
  rw [burnsideJ4NP_codeMat, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
    CFSG.Sporadic.SmallF2.toVecD_apply, rc_row ha i.isLt, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.add_comm (j : ℕ)]
  simp only [j.isLt, decide_true, Bool.true_and]

theorem utK_spec {Y : ℕ} {a : Code} (h : utK Y = true) (ha : RC a Y) :
    UT (burnsideJ4NP_codeMat a) := by
  unfold utK at h
  have hb : ∀ i j : ℕ, i < 12 → j ≤ i → Y.testBit (12 * i + j) = decide (i = j) := by
    intro i j hi hj
    have hu : Y / 2 ^ (12 * i) % 2 ^ (i + 1) = 2 ^ i :=
      beq_iff_eq.1 (List.all_eq_true.1 h i (List.mem_range.2 hi))
    have h1 := congrArg (fun x => Nat.testBit x j) hu
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow] at h1
    rw [Nat.add_comm, ← h1]
    simp [show j < i + 1 by omega]
  intro i j
  refine ⟨fun hji => ?_, ?_⟩
  · have hji' : (j : ℕ) < i := hji
    rw [codeMat_apply ha, hb i j i.isLt hji'.le, decide_eq_false (by omega : (i : ℕ) ≠ j)]
    simp
  · rw [codeMat_apply ha, hb i i i.isLt le_rfl]
    simp

private theorem find_zipIdx_some {α : Type*} (f : α → Bool) (d : α) :
    ∀ (l : List α) (k : ℕ) (x : α × ℕ), (l.zipIdx k).find? (fun p => f p.1) = some x →
      k ≤ x.2 ∧ x.2 < k + l.length ∧ f (l.getD (x.2 - k) d) = true ∧
        ∀ q, k ≤ q → q < x.2 → f (l.getD (q - k) d) = false
  | [], k, x, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    cases hfa : f a with
    | false =>
      rw [List.find?_cons_of_neg (by simp [hfa])] at h
      obtain ⟨h1, h2, h3, h4⟩ := find_zipIdx_some f d l (k + 1) x h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_, fun q hq1 hq2 => ?_⟩
      · rwa [show x.2 - k = x.2 - (k + 1) + 1 by omega, List.getD_cons_succ]
      · rcases Nat.eq_or_lt_of_le hq1 with rfl | hq
        · rwa [Nat.sub_self, List.getD_cons_zero]
        · rw [show q - k = q - (k + 1) + 1 by omega, List.getD_cons_succ]
          exact h4 q (by omega) hq2
    | true =>
      rw [List.find?_cons_of_pos (by simp [hfa])] at h
      cases h
      exact ⟨le_rfl, by simp, by simpa using hfa, fun q hq1 hq2 => by omega⟩

private theorem posL_get : ∀ q < 66, (posL.getD q (0, 0)).1 < (posL.getD q (0, 0)).2 ∧
    (posL.getD q (0, 0)).2 < 12 ∧ idx (posL.getD q (0, 0)).1 (posL.getD q (0, 0)).2 = q := by
  decide

private theorem posL_idx : ∀ i j : Fin 12, i < j →
    posL.getD (idx i j) (0, 0) = ((i : ℕ), (j : ℕ)) := by
  decide

theorem leadOf_spec {Y : ℕ} {a : Code} (h : leadOf Y < 66) (ha : RC a Y) :
    (∃ i j : Fin 12, i < j ∧ idx i j = leadOf Y ∧ burnsideJ4NP_codeMat a i j = 1) ∧
      ∀ i j : Fin 12, i < j → idx i j < leadOf Y → burnsideJ4NP_codeMat a i j = 0 := by
  unfold leadOf at h ⊢
  generalize hfd : (posL.zipIdx.find? fun p => Y.testBit (12 * p.1.1 + p.1.2)) = o at h ⊢
  cases o with
  | none => exact absurd h (by simp)
  | some x =>
    simp only [Option.elim] at h ⊢
    obtain ⟨-, -, hx3, hx4⟩ := find_zipIdx_some (fun p : ℕ × ℕ => Y.testBit (12 * p.1 + p.2))
      (0, 0) posL 0 x hfd
    simp only [Nat.sub_zero] at hx3 hx4
    obtain ⟨g1, g2, g3⟩ := posL_get x.2 h
    have g0 : (posL.getD x.2 (0, 0)).1 < 12 := by omega
    refine ⟨⟨⟨_, g0⟩, ⟨_, g2⟩, g1, g3, ?_⟩, fun i j hij hlt => ?_⟩
    · rw [codeMat_apply ha]
      simp only [hx3, if_true]
    · have := hx4 (idx i j) (Nat.zero_le _) hlt
      rw [posL_idx i j hij] at this
      rw [codeMat_apply ha]
      simp only [this]
      rfl

private theorem transl_eq {a : Code} {X : ℕ} (ha : RC a X) : a.transl = translK X := by
  unfold Code.transl translK
  rw [rc_row ha (by norm_num : 0 < 12), Nat.shiftRight_eq_div_pow]
  simp

private theorem translK_lt (X : ℕ) : translK X < 2048 := by
  unfold translK
  have : X % 2 ^ 12 < 2 ^ 12 := Nat.mod_lt _ (by positivity)
  omega

private theorem codeWF_of_rc {a : Code} {X : ℕ} (ha : RC a X) : burnsideJ4NP_CodeWF a := by
  obtain ⟨rows⟩ := a
  change rows = CFSG.KC.Co1F2.unpackR 12 X at ha
  subst ha
  apply burnsideJ4NP_codeWF_of_wf
  unfold Code.wf CFSG.KC.Co1F2.unpackR
  simp only [Array.size_ofFn, beq_self_eq_true, Bool.true_and, Array.toList_ofFn, List.all_eq_true,
    List.mem_ofFn, decide_eq_true_eq]
  rintro _ ⟨i, rfl⟩
  exact Nat.mod_lt _ (by norm_num)

private theorem fixK_eq {a : Code} {X : ℕ} (ha : RC a X) (v : ℕ) :
    fixK X v = burnsideJ4NP_fixesPt a v := by
  have hf : (List.range 12).foldl
      (fun acc i => if v.testBit i then acc ^^^ (X / 2 ^ (12 * i) % 2 ^ 12) else acc) 0 =
      (List.range 12).foldl (fun acc j => if v.testBit j then acc ^^^ (a.rows[j]?.getD 0) else acc)
        0 :=
    List.foldl_ext _ _ _ fun acc i hi => by rw [rc_row ha (List.mem_range.1 hi)]
  unfold fixK burnsideJ4NP_fixesPt CFSG.Sporadic.SmallF2.Native.vecMulN
  rw [hf]

private def spF (z : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if z.testBit n then spF z n ||| 2 ^ (12 * n) else spF z n

private theorem foldl_spF (z n : ℕ) :
    (List.range n).foldl (fun acc k => if z.testBit k then acc ||| 2 ^ (12 * k) else acc) 0 =
      spF z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

private theorem spF_lt (z : ℕ) : ∀ n, spF z n < 2 ^ (12 * n)
  | 0 => by simp [spF]
  | n + 1 => by
    have ih := spF_lt z n
    have h1 : 2 ^ (12 * n) < 2 ^ (12 * (n + 1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [show spF z (n + 1) = if z.testBit n then spF z n ||| 2 ^ (12 * n) else spF z n from rfl]
    split_ifs
    · exact Nat.or_lt_two_pow (ih.trans h1) h1
    · exact ih.trans h1

private theorem spF_mul (z : ℕ) : ∀ n, spF z n * 4095 < 2 ^ (12 * n) ∧
    ∀ m, (spF z n * 4095).testBit (12 * m) = (decide (m < n) && z.testBit m)
  | 0 => by simp [spF]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := spF_mul z n
    have hlt := spF_lt z n
    have e : spF z (n + 1) * 4095 =
        2 ^ (12 * n) * (if z.testBit n then 4095 else 0) + spF z n * 4095 := by
      rw [show spF z (n + 1) = if z.testBit n then spF z n ||| 2 ^ (12 * n) else spF z n from rfl]
      split_ifs with hz
      · have h2 := Nat.two_pow_add_eq_or_of_lt hlt 1
        rw [Nat.mul_one] at h2
        rw [Nat.lor_comm, ← h2]
        ring
      · simp
    rw [e]
    have hp : 2 ^ (12 * (n + 1)) = 2 ^ (12 * n) * 4096 := by
      rw [Nat.mul_succ, Nat.pow_add]
    constructor
    · rw [hp]
      have h4 : (if z.testBit n then 4095 else 0) ≤ 4095 := by split_ifs <;> omega
      have := Nat.mul_le_mul_left (2 ^ (12 * n)) h4
      omega
    · intro m
      rw [Nat.testBit_two_pow_mul_add _ ih1]
      by_cases hm : m < n
      · rw [if_pos (by omega), ih2, decide_eq_true hm, decide_eq_true (by omega : m < n + 1)]
      · rw [if_neg (by omega)]
        rcases Nat.eq_or_lt_of_not_lt hm with rfl | hm'
        · rw [Nat.sub_self, decide_eq_true (Nat.lt_succ_self m), Bool.true_and]
          cases z.testBit m <;> rfl
        · rw [decide_eq_false (by omega : ¬m < n + 1), Bool.false_and]
          split_ifs
          · apply Nat.testBit_lt_two_pow
            calc 4095 < 2 ^ 12 := by norm_num
              _ ≤ 2 ^ (12 * m - 12 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
          · exact Nat.zero_testBit _

private theorem spreadZ_testBit (z : ℕ) {k : ℕ} (hk : k < 12) :
    (spreadZ z).testBit (12 * k) = z.testBit k := by
  unfold spreadZ
  rw [foldl_spF, (spF_mul z 12).2 k, decide_eq_true hk, Bool.true_and]

private theorem foldl_or_pow_testBit (f : ℕ → Bool) (n j : ℕ) :
    ((List.range n).foldl (fun acc i => if f i then acc ||| 2 ^ i else acc) 0).testBit j =
      (decide (j < n) && f j) := by
  have := CFSG.Sporadic.SmallF2.foldl_or_testBit f n j
  simpa only [Nat.one_shiftLeft] using this

open Matrix in
private theorem colK_spec {a : Code} {X : ℕ} (ha : RC a X) (z : ℕ) :
    CFSG.Sporadic.SmallF2.toVecD 12 (colK X z) =
      burnsideJ4NP_codeMat a *ᵥ CFSG.Sporadic.SmallF2.toVecD 12 z := by
  let s : Code := ⟨CFSG.KC.Co1F2.unpackR 12 (spreadZ z)⟩
  have hs : RC s (spreadZ z) := rfl
  have hm : RC (a * s) (M X (spreadZ z)) := rc_mul ha hs
  have hcol : ∀ k : Fin 12, burnsideJ4NP_codeMat s k 0 = CFSG.Sporadic.SmallF2.toVecD 12 z k := by
    intro k
    rw [codeMat_apply hs, CFSG.Sporadic.SmallF2.toVecD_apply, Fin.val_zero, Nat.add_zero,
      spreadZ_testBit z k.isLt]
  funext j
  have e1 : CFSG.Sporadic.SmallF2.toVecD 12 (colK X z) j = burnsideJ4NP_codeMat (a * s) j 0 := by
    rw [CFSG.Sporadic.SmallF2.toVecD_apply, codeMat_apply hm, Fin.val_zero, Nat.add_zero]
    unfold colK
    rw [foldl_or_pow_testBit, decide_eq_true j.isLt, Bool.true_and]
  rw [e1, burnsideJ4NP_codeMat_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [hcol k]

open Matrix in
private theorem sepK_spec {a : Code} {X z : ℕ} (ha : RC a X) (h : sepK X z = true) :
    ¬ burnsideJ4NP_HasFix (burnsideJ4NP_codeMat a) := by
  rintro ⟨p, hp0, hp⟩
  unfold sepK at h
  have h1 : colK X z ^^^ z = 1 := Nat.eq_of_beq_eq_true h
  have h2 : CFSG.Sporadic.SmallF2.toVecD 12 1 =
      (burnsideJ4NP_codeMat a - 1) *ᵥ CFSG.Sporadic.SmallF2.toVecD 12 z := by
    rw [← h1, CFSG.Sporadic.SmallF2.toVecD_xor, colK_spec ha, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply]
    generalize (burnsideJ4NP_codeMat a *ᵥ CFSG.Sporadic.SmallF2.toVecD 12 z) j = x
    generalize CFSG.Sporadic.SmallF2.toVecD 12 z j = y
    revert x y
    decide
  have h3 : p ⬝ᵥ ((burnsideJ4NP_codeMat a - 1) *ᵥ CFSG.Sporadic.SmallF2.toVecD 12 z) = 0 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_sub, hp, Matrix.vecMul_one, sub_self,
      zero_dotProduct]
  rw [← h2, burnsideJ4NP_toVecD_one, dotProduct_single, hp0, mul_one] at h3
  exact one_ne_zero h3

theorem non2AK_spec {sx X z : ℕ} {a : Code} (h : non2AK sx X z = true) (ha : RC a X)
    (hsx : ∀ t < 2048, sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) :
    burnsideJ4NP_treeTest a = false := by
  unfold burnsideJ4NP_treeTest burnsideJ4NP_affine2AWith
  unfold non2AK at h
  rw [show a.inE = inEK X from inE_eq ha, transl_eq ha]
  split_ifs at h ⊢ with hE
  · rw [← hsx _ (translK_lt X)]
    simpa using h
  · rw [Bool.eq_false_iff]
    intro hf
    exact sepK_spec ha h ((burnsideJ4NP_hasFix_iff (codeWF_of_rc ha)).1 hf)

theorem is2AK_spec {sx X v : ℕ} {a : Code} (h : is2AK sx X v = true) (ha : RC a X)
    (hsx : ∀ t < 2048, sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) :
    burnsideJ4NP_treeTest a = true := by
  unfold burnsideJ4NP_treeTest burnsideJ4NP_affine2AWith
  unfold is2AK at h
  rw [show a.inE = inEK X from inE_eq ha, transl_eq ha]
  split_ifs at h ⊢ with hE
  · rw [← hsx _ (translK_lt X)]
    exact h
  · exact (burnsideJ4NP_hasFix_iff (codeWF_of_rc ha)).2
      (burnsideJ4NP_fixesPt_spec (by rw [← fixK_eq ha]; exact h))

theorem idx_lt : ∀ i k j : Fin 12, i < k → k < j → idx i k < idx i j ∧ idx k j < idx i j := by
  decide

theorem idx_inj : ∀ i j i' j' : Fin 12, i < j → i' < j' → idx i j = idx i' j' → i = i' ∧ j = j' := by
  decide

theorem ut_mul {A B : Matrix (Fin 12) (Fin 12) (ZMod 2)} (hA : UT A) (hB : UT B) : UT (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · rw [Matrix.mul_apply, Fintype.sum_eq_single i]
    · rw [(hA i i).2, (hB i i).2, mul_one]
    · intro k hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [(hA i k).1 hk, zero_mul]
      · rw [(hB k i).1 hk, mul_zero]

theorem ut_mul_apply {A B : Matrix (Fin 12) (Fin 12) (ZMod 2)} (hA : UT A) (hB : UT B) {p : ℕ}
    (hA0 : ∀ i j : Fin 12, i < j → idx i j < p → A i j = 0)
    (hB0 : ∀ i j : Fin 12, i < j → idx i j < p → B i j = 0) {i j : Fin 12} (hij : i < j)
    (hp : idx i j ≤ p) : (A * B) i j = A i j + B i j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add i j (ne_of_lt hij)]
  · rw [(hA i i).2, (hB j j).2, one_mul, mul_one, add_comm]
  · rintro k ⟨hki, hkj⟩
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [(hA i k).1 hk, zero_mul]
    rcases lt_or_gt_of_ne hkj with hk' | hk'
    · rw [hA0 i k hk (lt_of_lt_of_le (idx_lt i k j hk hk').1 hp), zero_mul]
    · rw [(hB k j).1 hk', mul_zero]

theorem ut_mul_zero {A B : Matrix (Fin 12) (Fin 12) (ZMod 2)} (hA : UT A) (hB : UT B) {p : ℕ}
    (hA0 : ∀ i j : Fin 12, i < j → idx i j < p → A i j = 0)
    (hB0 : ∀ i j : Fin 12, i < j → idx i j < p → B i j = 0) :
    ∀ i j : Fin 12, i < j → idx i j < p → (A * B) i j = 0 := by
  intro i j hij hp
  rw [ut_mul_apply hA hB hA0 hB0 hij hp.le, hA0 i j hij hp, hB0 i j hij hp, add_zero]

variable {G : Type*} [Group G]

@[expose] def nwFrom : G → List G → ℕ → G
  | acc, [], _ => acc
  | acc, x :: l, m => nwFrom (if m % 2 = 1 then acc * x else acc) l (m / 2)

theorem nwFrom_mul (acc : G) : ∀ (l : List G) (m : ℕ), nwFrom acc l m = acc * nwFrom 1 l m
  | [], _ => by simp [nwFrom]
  | x :: l, m => by
    unfold nwFrom
    rw [nwFrom_mul _ l, nwFrom_mul (if m % 2 = 1 then 1 * x else 1) l]
    split_ifs <;> group

theorem nwFrom_cons (x : G) (l : List G) (m : ℕ) :
    nwFrom 1 (x :: l) m = (if m % 2 = 1 then x else 1) * nwFrom 1 l (m / 2) := by
  conv_lhs => unfold nwFrom
  rw [nwFrom_mul]
  simp

theorem nwFrom_mem {K : Subgroup G} : ∀ {l : List G} (_ : ∀ x ∈ l, x ∈ K) {acc : G} (_ : acc ∈ K)
    (m : ℕ), nwFrom acc l m ∈ K
  | [], _, _, hacc, _ => hacc
  | x :: l, hl, acc, hacc, m => by
    unfold nwFrom
    refine nwFrom_mem (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_ _
    split_ifs
    · exact K.mul_mem hacc (hl x List.mem_cons_self)
    · exact hacc

@[expose] def Zb (q : ℕ) (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Prop :=
  ∀ i j : Fin 12, i < j → idx i j < q → A i j = 0

@[expose] def LeadAt (q : ℕ) (A : Matrix (Fin 12) (Fin 12) (ZMod 2)) : Prop :=
  (∃ i j : Fin 12, i < j ∧ idx i j = q ∧ A i j = 1) ∧ Zb q A

theorem ut_one : UT (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), Matrix.one_apply_eq i⟩

theorem zb_one (q : ℕ) : Zb q (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) := fun _ _ hij _ =>
  Matrix.one_apply_ne (ne_of_lt hij)

theorem zb_mono {q q' : ℕ} (h : q' ≤ q) {A : Matrix (Fin 12) (Fin 12) (ZMod 2)} (hA : Zb q A) :
    Zb q' A := fun i j hij hq => hA i j hij (lt_of_lt_of_le hq h)

theorem nw_ut {K : Subgroup G} (φ : G → Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hφ : ∀ x ∈ K, ∀ y ∈ K, φ (x * y) = φ x * φ y) (q : ℕ) :
    ∀ (l : List G) (acc : G) (m : ℕ), (∀ x ∈ l, x ∈ K ∧ UT (φ x) ∧ Zb q (φ x)) → acc ∈ K →
      UT (φ acc) → Zb q (φ acc) → UT (φ (nwFrom acc l m)) ∧ Zb q (φ (nwFrom acc l m))
  | [], _, _, _, _, hU, hZ => ⟨hU, hZ⟩
  | x :: l, acc, m, hl, hK, hU, hZ => by
    unfold nwFrom
    obtain ⟨hxK, hxU, hxZ⟩ := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, y ∈ K ∧ UT (φ y) ∧ Zb q (φ y) := fun y hy => hl y (List.mem_cons_of_mem _ hy)
    split_ifs
    · refine nw_ut φ hφ q l _ _ hl' (K.mul_mem hK hxK) ?_ ?_
      · rw [hφ _ hK _ hxK]
        exact ut_mul hU hxU
      · rw [hφ _ hK _ hxK]
        exact ut_mul_zero hU hxU hZ hxZ
    · exact nw_ut φ hφ q l _ _ hl' hK hU hZ

theorem nw_injective {K : Subgroup G} (φ : G → Matrix (Fin 12) (Fin 12) (ZMod 2))
    (hφ : ∀ x ∈ K, ∀ y ∈ K, φ (x * y) = φ x * φ y) (hφ1 : φ 1 = 1) :
    ∀ (l : List (G × ℕ)), (∀ x ∈ l, x.1 ∈ K ∧ UT (φ x.1) ∧ LeadAt x.2 (φ x.1)) →
      l.Pairwise (fun x y => x.2 < y.2) →
      ∀ m m', m < 2 ^ l.length → m' < 2 ^ l.length →
        nwFrom 1 (l.map Prod.fst) m = nwFrom 1 (l.map Prod.fst) m' → m = m'
  | [], _, _, m, m', hm, hm', _ => by
    simp only [List.length_nil, pow_zero, Nat.lt_one_iff] at hm hm'
    omega
  | x :: l, hl, hP, m, m', hm, hm', he => by
    obtain ⟨hxK, hxU, ⟨i, j, hij, hidx, hx1⟩, hxZ⟩ := hl x List.mem_cons_self
    have hl' : ∀ y ∈ l, y.1 ∈ K ∧ UT (φ y.1) ∧ LeadAt y.2 (φ y.1) :=
      fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hlt : ∀ y ∈ l, x.2 < y.2 := (List.pairwise_cons.mp hP).1
    have hl'' : ∀ y ∈ l.map Prod.fst, y ∈ K ∧ UT (φ y) ∧ Zb (x.2 + 1) (φ y) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact ⟨(hl' z hz).1, (hl' z hz).2.1, zb_mono (hlt z hz) (hl' z hz).2.2.2⟩
    have hw : ∀ m₀, nwFrom 1 (l.map Prod.fst) m₀ ∈ K ∧ UT (φ (nwFrom 1 (l.map Prod.fst) m₀)) ∧
        Zb (x.2 + 1) (φ (nwFrom 1 (l.map Prod.fst) m₀)) :=
      fun m₀ => ⟨nwFrom_mem (fun y hy => (hl'' y hy).1) K.one_mem m₀,
        nw_ut φ hφ (x.2 + 1) _ 1 m₀ hl'' K.one_mem (hφ1 ▸ ut_one) (hφ1 ▸ zb_one _)⟩
    have hlen : (x :: l).length = l.length + 1 := rfl
    rw [hlen, pow_succ] at hm hm'
    rw [List.map_cons, nwFrom_cons, nwFrom_cons] at he
    have key : ∀ m₁ m₂, x.1 * nwFrom 1 (l.map Prod.fst) m₁ ≠ nwFrom 1 (l.map Prod.fst) m₂ := by
      intro m₁ m₂ h
      obtain ⟨hK1, hU1, hZ1⟩ := hw m₁
      obtain ⟨-, -, hZ2⟩ := hw m₂
      have h1 : φ (x.1 * nwFrom 1 (l.map Prod.fst) m₁) i j =
          φ (nwFrom 1 (l.map Prod.fst) m₂) i j := by rw [h]
      rw [hφ _ hxK _ hK1, ut_mul_apply hxU hU1 hxZ (zb_mono (Nat.le_succ _) hZ1) hij hidx.le, hx1,
        hZ1 i j hij (by omega), hZ2 i j hij (by omega), add_zero] at h1
      exact one_ne_zero h1
    have hm2 : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
    have hm2' : m' % 2 = 0 ∨ m' % 2 = 1 := Nat.mod_two_eq_zero_or_one m'
    rcases hm2 with h0 | h0 <;> rcases hm2' with h0' | h0' <;>
      simp only [h0, h0', if_true, if_false, one_mul, Nat.zero_ne_one, Nat.one_ne_zero,
        mul_right_inj] at he
    · have := nw_injective φ hφ hφ1 l hl' (List.pairwise_cons.mp hP).2 _ _ (by omega)
        (by omega) he
      omega
    · exact absurd he.symm (key _ _)
    · exact absurd he (key _ _)
    · have := nw_injective φ hφ hφ1 l hl' (List.pairwise_cons.mp hP).2 _ _ (by omega)
        (by omega) he
      omega

theorem card_ge_of_nw [Finite G] {K : Subgroup G} {l : List G} (hl : ∀ x ∈ l, x ∈ K)
    (hinj : ∀ m m', m < 2 ^ l.length → m' < 2 ^ l.length → nwFrom 1 l m = nwFrom 1 l m' → m = m') :
    2 ^ l.length ≤ Nat.card K := by
  have hf : Function.Injective (fun m : Fin (2 ^ l.length) =>
      (⟨nwFrom 1 l m, nwFrom_mem hl K.one_mem _⟩ : K)) := by
    intro a b h
    exact Fin.ext (hinj a b a.2 b.2 (congrArg Subtype.val h))
  simpa using Nat.card_le_card_of_injective _ hf

theorem eq_nw_of_card [Finite G] {K : Subgroup G} {l : List G} (hl : ∀ x ∈ l, x ∈ K)
    (hinj : ∀ m m', m < 2 ^ l.length → m' < 2 ^ l.length → nwFrom 1 l m = nwFrom 1 l m' → m = m')
    (hc : Nat.card K ≤ 2 ^ l.length) : ∀ x ∈ K, ∃ m < 2 ^ l.length, x = nwFrom 1 l m := by
  have hf : Function.Injective (fun m : Fin (2 ^ l.length) =>
      (⟨nwFrom 1 l m, nwFrom_mem hl K.one_mem _⟩ : K)) := by
    intro a b h
    exact Fin.ext (hinj a b a.2 b.2 (congrArg Subtype.val h))
  have hb := hf.bijective_of_nat_card_le (by simpa using hc)
  intro x hx
  obtain ⟨m, hm⟩ := hb.2 ⟨x, hx⟩
  exact ⟨m, m.2, (congrArg Subtype.val hm).symm⟩

theorem filt_forall₂ {α β : Type*} {R : α → β → Prop} (b : Bool) :
    ∀ (fs : List Bool) {l : List α} {l' : List β}, List.Forall₂ R l l' →
      List.Forall₂ R (filt fs l b) (filt fs l' b)
  | [], _, _, _ => by simp [filt]
  | _ :: _, [], [], .nil => by simp [filt]
  | f :: fs, x :: l, y :: l', .cons hxy h => by
    unfold filt
    split_ifs
    · exact .cons hxy (filt_forall₂ b fs h)
    · exact filt_forall₂ b fs h

theorem filt_mem {α : Type*} {b : Bool} : ∀ {fs : List Bool} {l : List α} {x : α},
    x ∈ filt fs l b → x ∈ l
  | [], _, _, h => by simp [filt] at h
  | _ :: _, [], _, h => by simp [filt] at h
  | f :: fs, y :: l, x, h => by
    unfold filt at h
    split_ifs at h
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (filt_mem h)
    · exact List.mem_cons_of_mem _ (filt_mem h)

theorem filt_true_mem {α : Type*} : ∀ {fs : List Bool} {l : List α} {x : α},
    x ∈ filt fs l true → ∃ i, i < l.length ∧ fs.getD i false = true ∧ l[i]? = some x
  | [], _, _, h => by simp [filt] at h
  | _ :: _, [], _, h => by simp [filt] at h
  | f :: fs, y :: l, x, h => by
    unfold filt at h
    split_ifs at h with hf
    · rcases List.mem_cons.mp h with h | h
      · exact ⟨0, by simp, by simp [hf], by simp [h]⟩
      · obtain ⟨i, hi, hfi, hli⟩ := filt_true_mem h
        exact ⟨i + 1, by simp [hi], by simpa using hfi, by simpa using hli⟩
    · obtain ⟨i, hi, hfi, hli⟩ := filt_true_mem h
      exact ⟨i + 1, by simp [hi], by simpa using hfi, by simpa using hli⟩

theorem nw_split {K : Subgroup G} : ∀ (fs : List Bool) (l : List G), fs.length = l.length →
    (∀ x ∈ l, x ∈ K) → (∀ x ∈ filt fs l true, ∀ y ∈ K, x * y = y * x) →
    ∀ m < 2 ^ l.length, ∃ u < 2 ^ (filt fs l false).length, ∃ v < 2 ^ (filt fs l true).length,
      nwFrom 1 l m = nwFrom 1 (filt fs l false) u * nwFrom 1 (filt fs l true) v
  | [], [], _, _, _, m, hm => ⟨0, by simp [filt], 0, by simp [filt], by
      simp only [List.length_nil, pow_zero, Nat.lt_one_iff] at hm
      simp [nwFrom, filt]⟩
  | f :: fs, x :: l, hlen, hK, hc, m, hm => by
    have hlen' : fs.length = l.length := by simpa using hlen
    have hK' : ∀ y ∈ l, y ∈ K := fun y hy => hK y (List.mem_cons_of_mem _ hy)
    have hm' : m / 2 < 2 ^ l.length := by
      rw [List.length_cons, pow_succ] at hm
      omega
    have hc' : ∀ x ∈ filt fs l true, ∀ y ∈ K, x * y = y * x := by
      intro z hz y hy
      refine hc z ?_ y hy
      unfold filt
      split_ifs
      · exact List.mem_cons_of_mem _ hz
      · exact hz
    obtain ⟨u, hu, v, hv, he⟩ := nw_split fs l hlen' hK' hc' (m / 2) hm'
    have hxK := hK x List.mem_cons_self
    have hb : m % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [nwFrom_cons, he]
    by_cases hf : f = true
    · subst hf
      have hxc : ∀ y ∈ K, x * y = y * x := hc x (by simp [filt])
      refine ⟨u, by simpa [filt] using hu, m % 2 + 2 * v, ?_, ?_⟩
      · simp only [filt, if_true, List.length_cons, pow_succ]
        omega
      · simp only [filt, if_true, if_false, Bool.true_eq_false]
        rw [nwFrom_cons]
        have e1 : (m % 2 + 2 * v) % 2 = m % 2 := by omega
        have e2 : (m % 2 + 2 * v) / 2 = v := by omega
        rw [e1, e2]
        have hR : nwFrom 1 (filt fs l false) u ∈ K :=
          nwFrom_mem (fun y hy => hK' y (filt_mem hy)) K.one_mem u
        split_ifs
        · rw [← mul_assoc, ← mul_assoc, hxc _ hR]
        · simp
    · have hf' : f = false := by simpa using hf
      subst hf'
      refine ⟨m % 2 + 2 * u, ?_, v, by simpa [filt] using hv, ?_⟩
      · simp only [filt, if_true, List.length_cons, pow_succ]
        omega
      · simp only [filt, if_true, if_false, Bool.false_eq_true]
        rw [nwFrom_cons]
        have e1 : (m % 2 + 2 * u) % 2 = m % 2 := by omega
        have e2 : (m % 2 + 2 * u) / 2 = u := by omega
        rw [e1, e2, mul_assoc]

theorem nw_mul_xor : ∀ (l : List G), (∀ x ∈ l, ∀ y ∈ l, x * y = y * x) → (∀ x ∈ l, x * x = 1) →
    ∀ v v', nwFrom 1 l v * nwFrom 1 l v' = nwFrom 1 l (v ^^^ v')
  | [], _, _, v, v' => by simp [nwFrom]
  | x :: l, hc, hs, v, v' => by
    have hc' : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a :=
      fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have hs' : ∀ a ∈ l, a * a = 1 := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    have hxw : ∀ w, x * nwFrom 1 l w = nwFrom 1 l w * x := by
      intro w
      have hmem : nwFrom 1 l w ∈ Subgroup.centralizer {x} :=
        nwFrom_mem (K := Subgroup.centralizer {x}) (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (hc y (List.mem_cons_of_mem _ hy) x List.mem_cons_self)) (Subgroup.one_mem _) w
      exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
    have hxx := hs x List.mem_cons_self
    have e1 : (v ^^^ v') / 2 = v / 2 ^^^ v' / 2 :=
      Nat.eq_of_testBit_eq fun i => by simp only [← Nat.testBit_succ, Nat.testBit_xor]
    have e2 : (v ^^^ v') % 2 = (v % 2 + v' % 2) % 2 := by
      have h := Nat.testBit_xor v v' 0
      simp only [Nat.testBit_zero] at h
      rcases Nat.mod_two_eq_zero_or_one v with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one v' with h2 | h2 <;>
        rcases Nat.mod_two_eq_zero_or_one (v ^^^ v') with h3 | h3 <;> simp_all
    rw [nwFrom_cons, nwFrom_cons, nwFrom_cons, e1, ← nw_mul_xor l hc' hs' (v / 2) (v' / 2), e2]
    rcases Nat.mod_two_eq_zero_or_one v with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one v' with h2 | h2 <;>
      simp only [h1, h2, Nat.reduceAdd, Nat.reduceMod, Nat.zero_ne_one, if_true, if_false,
        one_mul, mul_one]
    · rw [← mul_assoc, ← hxw, mul_assoc]
    · rw [mul_assoc]
    · rw [← mul_assoc, mul_assoc x (nwFrom 1 l (v / 2)) x, ← hxw, ← mul_assoc, hxx, one_mul]

theorem nwFrom_zero : ∀ l : List G, nwFrom 1 l 0 = 1
  | [] => rfl
  | x :: l => by rw [nwFrom_cons, nwFrom_zero l]; simp

theorem nwFrom_mod : ∀ (l : List G) (v : ℕ), nwFrom 1 l v = nwFrom 1 l (v % 2 ^ l.length)
  | [], v => by simp [nwFrom]
  | x :: l, v => by
    rw [nwFrom_cons, nwFrom_cons, nwFrom_mod l (v / 2), List.length_cons, pow_succ',
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd v (Dvd.intro _ rfl)]

theorem nwFrom_two_pow : ∀ (l : List G) (i : ℕ) (hi : i < l.length), nwFrom 1 l (2 ^ i) = l[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: l, 0, _ => by rw [nwFrom_cons]; simp [nwFrom_zero]
  | x :: l, i + 1, hi => by
    rw [nwFrom_cons, pow_succ, Nat.mul_mod_left, Nat.mul_div_cancel _ (by norm_num),
      nwFrom_two_pow l i (by simpa using hi)]
    simp

theorem mem_closure_nw {l : List G} (hc' : ∀ a ∈ {x | x ∈ l}, ∀ b ∈ {x | x ∈ l}, a * b = b * a)
    (hs' : ∀ a ∈ {x | x ∈ l}, a * a = 1) {g : G} (hg : g ∈ Subgroup.closure {x | x ∈ l}) :
    ∃ v < 2 ^ l.length, g = nwFrom 1 l v := by
  have hc : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x := fun x hx y hy => hc' x hx y hy
  have hs : ∀ x ∈ l, x * x = 1 := fun x hx => hs' x hx
  have hred : ∀ v, ∃ v' < 2 ^ l.length, nwFrom 1 l v = nwFrom 1 l v' :=
    fun v => ⟨v % 2 ^ l.length, Nat.mod_lt _ (by positivity), nwFrom_mod l v⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨2 ^ i, Nat.pow_lt_pow_right (by norm_num) hi, (nwFrom_two_pow l i hi).symm⟩
  | one => exact ⟨0, by positivity, (nwFrom_zero l).symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, -, rfl⟩ := ha
    obtain ⟨v', -, rfl⟩ := hb
    rw [nw_mul_xor l hc hs]
    exact hred _
  | inv a _ ha =>
    obtain ⟨v, hv, rfl⟩ := ha
    refine ⟨v, hv, ?_⟩
    have := nw_mul_xor l hc hs v v
    rw [Nat.xor_self, nwFrom_zero] at this
    exact inv_eq_of_mul_eq_one_right this

theorem card_conj_le [Finite G] (K : Subgroup G) (y : G) (S : Finset G)
    (hS : ∀ z ∈ S, ∃ p ∈ K, z = p * y * p⁻¹) :
    S.card * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) ≤ Nat.card K := by
  classical
  set St := (K ⊓ Subgroup.centralizer {y}).subgroupOf K
  have hSt : Nat.card St = Nat.card ↥(K ⊓ Subgroup.centralizer {y}) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  choose! p hpK hp using hS
  let f : S → K ⧸ St := fun z => (⟨p z.1, hpK z.1 z.2⟩ : K)
  have hf : Function.Injective f := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [f, QuotientGroup.eq] at hab
    have hmem : (p a)⁻¹ * p b ∈ Subgroup.centralizer {y} := by
      have := (Subgroup.mem_subgroupOf.mp hab)
      exact (Subgroup.mem_inf.mp (by simpa using this)).2
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hmem
    refine Subtype.ext ?_
    change a = b
    rw [hp a ha, hp b hb]
    have hk : (p a)⁻¹ * p b * y * ((p a)⁻¹ * p b)⁻¹ = y := by
      rw [hc]
      group
    calc p a * y * (p a)⁻¹ = p a * ((p a)⁻¹ * p b * y * ((p a)⁻¹ * p b)⁻¹) * (p a)⁻¹ := by
          rw [hk]
      _ = p b * y * (p b)⁻¹ := by group
  have h1 : S.card ≤ St.index := by
    rw [Subgroup.index]
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have h2 := Subgroup.card_mul_index St
  rw [hSt] at h2
  calc S.card * Nat.card ↥(K ⊓ Subgroup.centralizer {y})
      ≤ St.index * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) := Nat.mul_le_mul_right _ h1
    _ = Nat.card K := by rw [Nat.mul_comm, h2]

theorem packL_ofFn : ∀ (n X : ℕ), X < 2 ^ (12 * n) →
    packL (List.ofFn fun i : Fin n => X / 2 ^ (12 * i.val) % 2 ^ 12) = X
  | 0, X, h => by
    have : X = 0 := by simpa using h
    simp [packL, this]
  | n + 1, X, h => by
    have h2 : ∀ i : Fin n,
        X / 2 ^ (12 * (i.val + 1)) % 2 ^ 12 = X / 4096 / 2 ^ (12 * i.val) % 2 ^ 12 := by
      intro i
      rw [Nat.div_div_eq_div_mul, Nat.mul_add, Nat.pow_add, Nat.mul_comm (2 ^ (12 * i.val))]
    have hX : X / 4096 < 2 ^ (12 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc X < 2 ^ (12 * (n + 1)) := h
        _ = 2 ^ (12 * n) * 4096 := by rw [Nat.mul_succ, Nat.pow_add]
    rw [List.ofFn_succ]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Fin.val_succ, h2]
    change X % 2 ^ 12 + 4096 *
      packL (List.ofFn fun i : Fin n => X / 4096 / 2 ^ (12 * i.val) % 2 ^ 12) = X
    rw [packL_ofFn n _ hX]
    omega

theorem pkC_of_rc {a : Code} {X : ℕ} (h : RC a X) (hX : X < 2 ^ 144) : pkC a = X := by
  unfold pkC
  rw [h]
  unfold CFSG.KC.Co1F2.unpackR
  rw [Array.toList_ofFn]
  exact packL_ofFn 12 X hX

theorem wf_unpack (X : ℕ) : (⟨CFSG.KC.Co1F2.unpackR 12 X⟩ : Code).wf = true := by
  unfold Code.wf CFSG.KC.Co1F2.unpackR
  simp only [Array.size_ofFn, beq_self_eq_true, Bool.true_and, Array.toList_ofFn, List.all_eq_true,
    List.mem_ofFn, decide_eq_true_eq]
  rintro _ ⟨i, rfl⟩
  exact Nat.mod_lt _ (by norm_num)

theorem M_lt (X Y : ℕ) : M X Y < 2 ^ 144 := by
  unfold M
  rw [CFSG.KC.F2W.mulW_eq]
  unfold CFSG.KC.M1F2.mulF
  rw [CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.strictN_eq]
  exact CFSG.KC.F2W.orN_fields_lt (d := 12) (n := 12) fun i _ => CFSG.KC.F2W.vmF_lt 12 _ _

theorem oneK_lt : oneK < 2 ^ 144 := by decide

theorem u_wf : uCode.toList.all Code.wf = true := by decide
theorem k_wf : kCode.toList.all Code.wf = true := by decide
theorem x_wf : xCode.toList.all Code.wf = true := by decide
theorem xi_wf : xiCode.toList.all Code.wf = true := by decide

theorem rc_kel (e : ℕ) : RC (kelCode e) (kelCK e) :=
  rc_foldl _ _ (fun _ _ i h => rc_mul h (rc_get k_wf i)) _ 1 oneK rc_one

theorem ltr_mem (d : ℕ) : ltr d ∈ letters := by
  unfold ltr
  split_ifs <;> decide

theorem digitsL_letters : ∀ (f v : ℕ), ∀ ℓ ∈ digitsL f v, ℓ ∈ letters
  | 0, _, ℓ, h => by simp [digitsL] at h
  | f + 1, v, ℓ, h => by
    unfold digitsL at h
    split_ifs at h
    · simp at h
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ ltr_mem _
      · exact digitsL_letters f _ ℓ h

theorem wordC_letters : ∀ (f w : ℕ), ∀ ℓ ∈ wordC f w, ℓ ∈ letters
  | 0, _, ℓ, h => by simp [wordC] at h
  | f + 1, w, ℓ, h => by
    unfold wordC at h
    split_ifs at h
    · simp at h
    · rcases List.mem_append.mp h with h | h
      · exact digitsL_letters _ _ ℓ h
      · exact wordC_letters f _ ℓ h

theorem wordProd_append {G : Type*} [Group G] (gs : ℕ → G) (l₁ l₂ : List ℤ) :
    wordProd gs (l₁ ++ l₂) = wordProd gs l₁ * wordProd gs l₂ := by
  unfold wordProd
  rw [List.map_append, List.prod_append]

theorem transl_etaCode (c : ℕ) : (etaCode c).transl = etaCK UK c % 2 ^ 12 / 2 := by
  unfold Code.transl
  rw [rc_row (rc_etaCode u_wf c) (by norm_num : 0 < 12), Nat.shiftRight_eq_div_pow]
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.pow_one]
  rfl

theorem sxOf_testBit (zm : List ℕ) :
    ∀ t < 2048, (sxOf zm).testBit t = (burnsideJ4NP_sextArrOf zm)[t]?.getD false := by
  have key : ∀ (l : List ℕ) (acc : ℕ) (A : Array Bool), A.size = 2048 →
      (∀ t < 2048, acc.testBit t = A[t]?.getD false) →
      ∀ t < 2048, (l.foldl (fun acc c => acc ||| 2 ^ ((etaCK UK c) % 2 ^ 12 / 2)) acc).testBit t =
        (l.foldl (fun A c => A.set! (etaCode c).transl true) A)[t]?.getD false := by
    intro l
    induction l with
    | nil => intro acc A _ h; simpa using h
    | cons c l ih =>
      intro acc A hA h
      simp only [List.foldl_cons]
      refine ih _ _ (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hA]) ?_
      intro t ht
      rw [Nat.testBit_or, Nat.testBit_two_pow, h t ht, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds, transl_etaCode]
      by_cases he : etaCK UK c % 2 ^ 12 / 2 = t
      · rw [if_pos he, if_pos (by rw [hA, he]; exact ht), decide_eq_true he]
        simp
      · rw [if_neg he, decide_eq_false he, Bool.or_false]
  intro t ht
  refine key zm 0 _ (by simp) (fun t ht => ?_) t ht
  simp [Array.getElem?_replicate, ht]

section PK


@[expose] def PK (x : J) (X : ℕ) : Prop := x ∈ Hj ∧ RC (burnsideJ4NP_encJ x) X

theorem pk_mul {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) : PK (x * y) (M X Y) :=
  ⟨Hj.mul_mem hx.1 hy.1, by rw [burnsideJ4NP_encJ_mul hx.1 hy.1]; exact rc_mul hx.2 hy.2⟩

theorem pk_one : PK 1 oneK := ⟨Hj.one_mem, by rw [burnsideJ4NP_encJ_one]; exact rc_one⟩

theorem pk_eq {x y : J} {X : ℕ} (hx : PK x X) (hy : PK y X) : x = y :=
  burnsideJ4NP_encJ_inj hx.1 hy.1 (rc_eq hx.2 hy.2)

theorem pk_beq {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) (h : Nat.beq X Y = true) : x = y :=
  pk_eq hx (Nat.eq_of_beq_eq_true h ▸ hy)

theorem pk_canon {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) (hX : X < 2 ^ 144)
    (hY : Y < 2 ^ 144) (h : x = y) : X = Y := by
  subst h
  rw [← pkC_of_rc hx.2 hX, ← pkC_of_rc hy.2 hY]

theorem pk_comm {x y : J} {X Y : ℕ} (hx : PK x X) (hy : PK y Y) :
    x * y = y * x ↔ commK X Y = true := by
  constructor
  · intro h
    unfold commK
    rw [pk_canon (pk_mul hx hy) (pk_mul hy hx) (M_lt _ _) (M_lt _ _) h]
    exact Nat.beq_refl _
  · intro h
    exact pk_beq (pk_mul hx hy) (pk_mul hy hx) h

theorem pk_sq {x : J} {X : ℕ} (hx : PK x X) : x * x = 1 ↔ sqOneK X = true := by
  constructor
  · intro h
    unfold sqOneK
    rw [pk_canon (pk_mul hx hx) pk_one (M_lt _ _) oneK_lt h]
    exact Nat.beq_refl _
  · intro h
    exact pk_beq (pk_mul hx hx) pk_one h

theorem pk_inv {x : J} {X XI : ℕ} (hx : PK x X) (h : invK X XI = true) : PK x⁻¹ XI := by
  unfold invK at h
  rw [Bool.and_eq_true] at h
  have hm : M X XI = oneK := Nat.eq_of_beq_eq_true h.1
  have h1 : RC 1 (M X XI) := by rw [hm]; exact rc_one
  have ha : burnsideJ4NP_encJ x * ⟨CFSG.KC.Co1F2.unpackR 12 XI⟩ = 1 :=
    rc_eq (rc_mul hx.2 (rfl : RC ⟨CFSG.KC.Co1F2.unpackR 12 XI⟩ XI)) h1
  exact ⟨Hj.inv_mem hx.1, by rw [burnsideJ4NP_encJ_inv hx.1 ha (wf_unpack XI)]; rfl⟩

theorem pk_cc {T : Tabs} (hT : tabsOK T = true) {ce : ℕ × ℕ} (hce : coordOK ce = true) :
    PK (burnsideJ4NP_treeElt ce) (ccT T ce) := by
  unfold coordOK at hce
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hce
  unfold tabsOK at hT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
  have he : T.eta ce.1 = etaCK UK ce.1 := Nat.eq_of_beq_eq_true (hT.1.1 _ hce.1)
  have hk : T.kel ce.2 = kelCK ce.2 := Nat.eq_of_beq_eq_true (hT.1.2 _ hce.2)
  refine ⟨burnsideJ4NP_treeElt_mem hce.2, ?_⟩
  rw [burnsideJ4NP_encJ_treeElt hce.2]
  unfold ccT
  rw [he, hk]
  exact rc_mul (rc_etaCode u_wf ce.1) (rc_kel ce.2)

theorem pk_word {T : Tabs} (hT : tabsOK T = true) :
    ∀ (f w : ℕ), PK (wordProd xJ (wordC f w)) (wordT T f w)
  | 0, w => by simpa [wordC, wordT, wordProd] using pk_one
  | f + 1, w => by
    unfold wordC wordT
    split_ifs with hw
    · simpa [wordProd] using pk_one
    · rw [wordProd_append]
      refine pk_mul ?_ (pk_word hT f _)
      unfold tabsOK at hT
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
      have h4 : T.w4 (w % 4096) = wordCK XK XiK (digitsL 4 (w % 4096)) :=
        Nat.eq_of_beq_eq_true (hT.2 _ (Nat.mod_lt _ (by norm_num)))
      have hl := digitsL_letters 4 (w % 4096)
      refine ⟨wordProd_mem_Hj hl, ?_⟩
      rw [burnsideJ4NP_encJ_of_mem (wordProd_mem_Hj hl), burnsideJ4NP_enc_wordProd hl, h4]
      exact rc_codeOfWord x_wf xi_wf _

theorem word_mem (f w : ℕ) : wordProd xJ (wordC f w) ∈ Hj := wordProd_mem_Hj (wordC_letters f w)

theorem pk_prodFrom : ∀ {xs : List J} {Xs : List ℕ}, List.Forall₂ PK xs Xs →
    ∀ {acc : J} {ACC : ℕ}, PK acc ACC → ∀ m, PK (nwFrom acc xs m) (prodFrom ACC Xs m)
  | [], [], .nil, _, _, h, _ => h
  | x :: xs, X :: Xs, .cons hx hxs, acc, ACC, h, m => by
    unfold nwFrom prodFrom
    split_ifs
    · exact pk_prodFrom hxs (pk_mul h hx) _
    · exact pk_prodFrom hxs h _

end PK

end CFSG.KC.J4TreeN
