module

public import CFSG.Certificates.Kernel.Co2Span.Sound

public section

set_option exponentiation.threshold 600

namespace CFSG.KC.Co2Span

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.Co2Syl CFSG.KC.TabMatGrp Matrix
open CFSG.Sporadic.SmallF2 (ofBits_testBit ofBits_lt)

@[expose] noncomputable def linP (e : Nat) (D : Matrix (Fin 22) (Fin 22) (ZMod 2)) : ZMod 2 :=
  ∑ pq : Fin 22 × Fin 22, if e.testBit (22 * pq.1.val + pq.2.val) then D pq.1 pq.2 else 0

private theorem z2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem linP_xor (e f : Nat) (D : Matrix (Fin 22) (Fin 22) (ZMod 2)) :
    linP (e ^^^ f) D = linP e D + linP f D := by
  unfold linP
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [Nat.testBit_xor]
  cases e.testBit (22 * pq.1.val + pq.2.val) <;>
    cases f.testBit (22 * pq.1.val + pq.2.val) <;> simp [z2_add_self]

theorem linP_zero (D : Matrix (Fin 22) (Fin 22) (ZMod 2)) : linP 0 D = 0 := by
  simp [linP]

theorem linP_eqMaskP (Y Z : Nat) (i j : Fin 22) (D : Matrix (Fin 22) (Fin 22) (ZMod 2)) :
    linP (eqMaskP Y Z i.val j.val) D = (D * MatP 22 Y + MatP 22 Z * D) i j := by
  have hs : ∀ p q : Fin 22, linP (1 <<< (22 * p.val + q.val)) D = D p q := by
    intro p q
    unfold linP
    rw [Finset.sum_eq_single (p, q)]
    · simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_true, ↓reduceIte]
    · intro pq _ hne
      have : ¬ (22 * p.val + q.val = 22 * pq.1.val + pq.2.val) := by
        intro h
        apply hne
        have h1 : pq.1.val = p.val := by omega
        have h2 : pq.2.val = q.val := by omega
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      simp [Nat.one_shiftLeft, this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hite : ∀ (c : Bool) (e : Nat), linP (if c then e else 0) D = if c then linP e D else 0 := by
    intro c e
    cases c
    · simp [linP_zero]
    · rfl
  set g : Nat → ZMod 2 := fun q =>
    linP (if Y.testBit (22 * q + j.val) then 1 <<< (22 * i.val + q) else 0) D +
      linP (if Z.testBit (22 * i.val + q) then 1 <<< (22 * q + j.val) else 0) D with hg
  have key : ∀ (m init : Nat), linP ((List.range m).foldl (fun acc q =>
      acc ^^^ (if Y.testBit (22 * q + j.val) then 1 <<< (22 * i.val + q) else 0) ^^^
        (if Z.testBit (22 * i.val + q) then 1 <<< (22 * q + j.val) else 0)) init) D =
      linP init D + ∑ q ∈ Finset.range m, g q := by
    intro m
    induction m with
    | zero => intro init; simp
    | succ m ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, linP_xor, linP_xor, ih, hg]
      ring
  unfold eqMaskP
  rw [key, linP_zero, zero_add, ← Fin.sum_univ_eq_sum_range g, Matrix.add_apply, Matrix.mul_apply,
    Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hg]
  simp only []
  rw [hite, hite, MatP_apply22, MatP_apply22, hs i q, hs q j]
  split_ifs <;> simp

private theorem linP_foldl {Ys Zs : List Nat} {D : Matrix (Fin 22) (Fin 22) (ZMod 2)}
    (hD : ∀ r < 1452, linP (eqAtP Ys Zs r) D = 0) :
    ∀ (rs : List Nat) (init : Nat), (∀ r ∈ rs, r < 1452) →
      linP (rs.foldl (fun acc r => acc ^^^ eqAtP Ys Zs r) init) D = linP init D := by
  intro rs
  induction rs with
  | nil => intro init _; rfl
  | cons r rs ih =>
    intro init h
    rw [List.foldl_cons, ih _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')), linP_xor,
      hD r (h r List.mem_cons_self), add_zero]

private theorem fullP_testBit {n : Nat} (hn : n < 484) : fullP.testBit n = true := by
  rw [fullP, Nat.testBit_two_pow_sub_one]
  simp [hn]

theorem peel_sound {Ys Zs : List Nat} (D : Matrix (Fin 22) (Fin 22) (ZMod 2))
    (hD : ∀ r < 1452, linP (eqAtP Ys Zs r) D = 0) :
    ∀ (L : List (Nat × List Nat)) (K : Nat), peelK Ys Zs K L = true →
      (∀ p q : Fin 22, K.testBit (22 * p.val + q.val) = true → D p q = 0) →
        ∀ p q : Fin 22, D p q = 0 := by
  intro L
  induction L with
  | nil =>
    intro K h hK p q
    rw [peelK, beq_iff_eq] at h
    exact hK p q (by rw [h]; exact fullP_testBit (by omega))
  | cons st L ih =>
    obtain ⟨a, rs⟩ := st
    intro K h hK
    rw [peelK] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨ha, hrs⟩, he⟩, hrest⟩ := h
    have hbit : ∀ n, n < 484 → (xorEqs Ys Zs rs).testBit n = true → K.testBit n = false →
        n = a := by
      intro n hn h1 h2
      have := congrArg (fun m => m.testBit n) he
      simp only [Nat.testBit_and, Nat.testBit_xor, fullP_testBit hn, h1, h2, Nat.one_shiftLeft,
        Nat.testBit_two_pow] at this
      exact (by simpa using this : a = n).symm
    have haK : K.testBit a = false := by
      have := congrArg (fun m => m.testBit a) he
      simp only [Nat.testBit_and, Nat.testBit_xor, fullP_testBit ha, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_true] at this
      cases hk : K.testBit a <;> simp_all
    have hea : (xorEqs Ys Zs rs).testBit a = true := by
      have := congrArg (fun m => m.testBit a) he
      simp only [Nat.testBit_and, Nat.testBit_xor, fullP_testBit ha, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_true] at this
      cases hx : (xorEqs Ys Zs rs).testBit a <;> simp_all
    refine ih _ hrest ?_
    intro p q hb
    rw [Nat.testBit_or] at hb
    rcases Bool.or_eq_true_iff.1 hb with hb | hb
    · exact hK p q hb
    · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hb
      have hpa : a = 22 * p.val + q.val := of_decide_eq_true hb
      have h0 : linP (xorEqs Ys Zs rs) D = 0 := by
        rw [xorEqs, linP_foldl hD rs 0 hrs, linP_zero]
      have h1 : linP (xorEqs Ys Zs rs) D = D p q := by
        unfold linP
        rw [Finset.sum_eq_single (p, q)]
        · simp only []
          rw [← hpa, hea, if_pos rfl]
        · intro pq _ hne
          have hlt : 22 * pq.1.val + pq.2.val < 484 := by omega
          by_cases hk : K.testBit (22 * pq.1.val + pq.2.val) = true
          · split_ifs
            · exact hK _ _ hk
            · rfl
          · have hne' : 22 * pq.1.val + pq.2.val ≠ a := by
              intro e
              apply hne
              have e1 : pq.1.val = p.val := by omega
              have e2 : pq.2.val = q.val := by omega
              exact Prod.ext (Fin.ext e1) (Fin.ext e2)
            have : (xorEqs Ys Zs rs).testBit (22 * pq.1.val + pq.2.val) = false := by
              cases hx : (xorEqs Ys Zs rs).testBit (22 * pq.1.val + pq.2.val)
              · rfl
              · exact absurd (hbit _ hlt hx (by simpa using hk)) hne'
            rw [this]
            rfl
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [← h1, h0]

private noncomputable def ent (M : Matrix (Fin 22) (Fin 22) (ZMod 2)) (a : Nat) : ZMod 2 :=
  if h : a < 484 then M ⟨a / 22, by omega⟩ ⟨a % 22, by omega⟩ else 0

private theorem ent_add (A B : Matrix (Fin 22) (Fin 22) (ZMod 2)) (a : Nat) :
    ent (A + B) a = ent A a + ent B a := by
  unfold ent
  split_ifs
  · rfl
  · simp

private theorem ent_sum (s : Finset (Fin 11)) (A : Fin 11 → Matrix (Fin 22) (Fin 22) (ZMod 2))
    (a : Nat) : ent (∑ i ∈ s, A i) a = ∑ i ∈ s, ent (A i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold ent
    split_ifs <;> rfl
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ent_add, ih]

private theorem ent_smul (c : ZMod 2) (A : Matrix (Fin 22) (Fin 22) (ZMod 2)) (a : Nat) :
    ent (c • A) a = c * ent A a := by
  unfold ent
  split_ifs
  · rfl
  · simp

private theorem ent_pair (Q : Matrix (Fin 22) (Fin 22) (ZMod 2)) (p q : Fin 22) :
    ent Q (22 * p.val + q.val) = Q p q := by
  have hlt : 22 * p.val + q.val < 484 := by omega
  have hd : (22 * p.val + q.val) / 22 = p.val := by omega
  have hm : (22 * p.val + q.val) % 22 = q.val := by omega
  unfold ent
  simp only [hlt, ↓reduceDIte]
  congr 1 <;> exact Fin.ext (by simp [hd, hm])

private theorem ent_MatP (X a : Nat) (ha : a < 484) :
    ent (MatP 22 X) a = if X.testBit a then 1 else 0 := by
  unfold ent
  rw [dif_pos ha, MatP_apply22]
  simp only []
  rw [show 22 * (a / 22) + a % 22 = a by omega]

private theorem maskOf_testBit {l : List Nat} {a : Nat} (h : (maskOf l).testBit a = true) :
    a ∈ l := by
  have key : ∀ (l : List Nat) (m : Nat),
      (l.foldl (fun m f => m ||| (1 <<< f)) m).testBit a = true → m.testBit a = true ∨ a ∈ l := by
    intro l
    induction l with
    | nil => intro m h; exact Or.inl h
    | cons f l ih =>
      intro m hm
      simp only [List.foldl_cons] at hm
      rcases ih _ hm with h1 | h1
      · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow] at h1
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons.2 (Or.inl h1.symm))
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  unfold maskOf at h
  rcases key l 0 h with h1 | h1
  · simp at h1
  · exact h1

theorem span_of_peel {Ys Zs Bs free : List Nat} {L : List (Nat × List Nat)}
    (hfr : free.length = 11) (hf : ∀ f ∈ free, f < 484)
    (hpeel : peelK Ys Zs (maskOf free) L = true)
    (hsol : ∀ i < 11, ∀ k < 3, MatP 22 (Bs.getD i 0) * MatP 22 (Ys.getD k 0) =
      MatP 22 (Zs.getD k 0) * MatP 22 (Bs.getD i 0))
    (hfree : ∀ i < 11, ∀ j < 11, (Bs.getD i 0).testBit (free.getD j 0) = (i == j))
    (M : Matrix (Fin 22) (Fin 22) (ZMod 2))
    (hM : ∀ k < 3, M * MatP 22 (Ys.getD k 0) = MatP 22 (Zs.getD k 0) * M) :
    ∃ c : Fin 11 → ZMod 2, M = ∑ i : Fin 11, c i • MatP 22 (Bs.getD i.val 0) := by
  refine ⟨fun i => ent M (free.getD i.val 0), ?_⟩
  set S := ∑ i : Fin 11, ent M (free.getD i.val 0) • MatP 22 (Bs.getD i.val 0) with hS
  have hSsol : ∀ k < 3, S * MatP 22 (Ys.getD k 0) = MatP 22 (Zs.getD k 0) * S := by
    intro k hk
    rw [hS, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hsol i.val i.isLt k hk]
  have hDsol : ∀ k < 3,
      (M + S) * MatP 22 (Ys.getD k 0) = MatP 22 (Zs.getD k 0) * (M + S) := by
    intro k hk
    rw [add_mul, mul_add, hM k hk, hSsol k hk]
  have hD : ∀ r < 1452, linP (eqAtP Ys Zs r) (M + S) = 0 := by
    intro r hr
    have hi : r % 484 / 22 < 22 := by omega
    have hj : r % 22 < 22 := by omega
    have h := linP_eqMaskP (Ys.getD (r / 484) 0) (Zs.getD (r / 484) 0) ⟨_, hi⟩ ⟨_, hj⟩ (M + S)
    unfold eqAtP
    rw [h, hDsol (r / 484) (by omega), Matrix.add_apply]
    exact z2_add_self _
  have hK : ∀ p q : Fin 22, (maskOf free).testBit (22 * p.val + q.val) = true →
      (M + S) p q = 0 := by
    intro p q hb
    have hmem := maskOf_testBit hb
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
    have hj11 : j < 11 := hfr ▸ hj
    have hget : free.getD j 0 = 22 * p.val + q.val := by
      rw [List.getD_eq_getElem _ _ hj, hjv]
    have hlt : 22 * p.val + q.val < 484 := by omega
    have key : ∀ i : Fin 11, ent (MatP 22 (Bs.getD i.val 0)) (free.getD j 0) =
        if i = ⟨j, hj11⟩ then 1 else 0 := by
      intro i
      rw [hget, ent_MatP _ _ hlt, ← hget, hfree i.val i.isLt j hj11]
      by_cases h : i = ⟨j, hj11⟩
      · subst h
        simp
      · have : (i.val == j) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun e => h (Fin.ext e)
        simp [h, this]
    have hSa : ent S (free.getD j 0) = ent M (free.getD j 0) := by
      rw [hS, ent_sum]
      simp only [ent_smul, key, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]
    rw [← ent_pair (M + S) p q, ← hget, ent_add, hSa]
    exact z2_add_self _
  have h0 := peel_sound (M + S) hD L _ hpeel hK
  ext i j
  have h4 := h0 i j
  rw [Matrix.add_apply] at h4
  exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ h4

theorem MatP_comboP (Bs : List Nat) (cc : Nat) :
    MatP 22 (comboP Bs cc) =
      ∑ i : Fin 11, (if cc.testBit i.val then (1 : ZMod 2) else 0) • MatP 22 (Bs.getD i.val 0) := by
  have key : ∀ (m init : Nat), MatP 22 ((List.range m).foldl
      (fun acc i => if cc.testBit i then acc ^^^ Bs.getD i 0 else acc) init) =
        MatP 22 init + ∑ i ∈ Finset.range m,
          (if cc.testBit i then (1 : ZMod 2) else 0) • MatP 22 (Bs.getD i 0) := by
    intro m
    induction m with
    | zero => intro init; simp
    | succ m ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ← add_assoc]
      split_ifs with h
      · rw [MatP_xor, ih]
        simp
      · rw [ih]
        simp
  unfold comboP
  rw [key, MatP_zero, zero_add, ← Fin.sum_univ_eq_sum_range
    (fun i => (if cc.testBit i then (1 : ZMod 2) else 0) • MatP 22 (Bs.getD i 0))]

theorem MatP_wordP (X1 X2 : Nat) (w : List (Nat × Nat)) :
    MatP 22 (wordP X1 X2 w) =
      (w.map fun q => (if q.1 % 2 == 0 then MatP 22 X1 else MatP 22 X2) ^ q.2).prod := by
  have key : ∀ (w : List (Nat × Nat)) (init : Nat), MatP 22 (w.foldl
      (fun acc q => mulV acc (powK (if q.1 % 2 == 0 then X1 else X2) q.2)) init) =
        MatP 22 init *
          (w.map fun q => (if q.1 % 2 == 0 then MatP 22 X1 else MatP 22 X2) ^ q.2).prod := by
    intro w
    induction w with
    | nil => intro init; simp
    | cons q w ih =>
      intro init
      rw [List.foldl_cons, ih, MatP_mulV, MatP_powK, List.map_cons, List.prod_cons, mul_assoc]
      congr 3
      split_ifs <;> rfl
  unfold wordP
  rw [key, MatP_IDP, one_mul]

theorem enum_sound {Bs X1s X2s : List Nat} {tw : List (List (Nat × Nat))} {kk Qs : List Nat}
    {X01 X02 M0 : Nat} (h : enumP Bs X1s X2s tw kk Qs X01 X02 M0 = true)
    (htw : tw.head? = some [(0, 1)]) (hlen : tw.length ≤ kk.length)
    {cc c₁ c₂ : Nat} (hcc : cc < 2048) (hc₁ : c₁ < 16) (hc₂ : c₂ < 16)
    (h3 : MatP 22 (comboP Bs cc) ^ 3 = 1)
    (hrel : ∀ j < tw.length, (MatP 22 (wordP (X1s.getD c₁ 0) (X2s.getD c₂ 0) (tw.getD j [])) *
      MatP 22 (comboP Bs cc)) ^ kk.getD j 0 = 1) :
    ∃ Q ∈ Qs, MatP 22 Q * MatP 22 (X1s.getD c₁ 0) = MatP 22 X01 * MatP 22 Q ∧
      MatP 22 Q * MatP 22 (X2s.getD c₂ 0) = MatP 22 X02 * MatP 22 Q ∧
      MatP 22 Q * MatP 22 (comboP Bs cc) = MatP 22 M0 * MatP 22 Q := by
  unfold enumP at h
  have hO := allN_iff.1 h cc hcc
  rw [letB_eq] at hO
  have e3 : eqK (powK (comboP Bs cc) 3) IDP = true := by
    rw [eqK_iff, MatP_powK, MatP_IDP, h3]
  rw [e3, Bool.not_true, Bool.false_or] at hO
  have hC := allN_iff.1 hO c₁ hc₁
  rw [letB_eq] at hC
  have htl : 0 < tw.length := by
    cases tw with
    | nil => simp at htw
    | cons _ _ => simp
  have e1 : eqK (powK (mulV (X1s.getD c₁ 0) (comboP Bs cc)) (kk.getD 0 0)) IDP = true := by
    rw [eqK_iff, MatP_powK, MatP_IDP, MatP_mulV]
    have h0 := hrel 0 htl
    have hw : tw.getD 0 [] = [(0, 1)] := by
      cases tw with
      | nil => simp at htw
      | cons a _ =>
        simp only [List.head?_cons, Option.some.injEq] at htw
        simp [htw]
    rw [hw, MatP_wordP] at h0
    simpa using h0
  rw [e1, Bool.not_true, Bool.false_or] at hC
  have hD := allN_iff.1 hC c₂ hc₂
  rw [letB_eq] at hD
  have er : relsP (X1s.getD c₁ 0) (X2s.getD c₂ 0) (comboP Bs cc) tw kk = true := by
    unfold relsP
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hp
    have hn2 : n < min tw.length kk.length := by rwa [List.length_zip] at hn
    have hn' : n < tw.length := by omega
    have hn3 : n < kk.length := by omega
    rw [List.getElem_zip, eqK_iff, MatP_powK, MatP_IDP, MatP_mulV]
    have := hrel n hn'
    rwa [List.getD_eq_getElem tw [] hn', List.getD_eq_getElem kk 0 hn3] at this
  rw [er, Bool.not_true, Bool.false_or] at hD
  unfold conjP at hD
  obtain ⟨Q, hQ, hQc⟩ := List.any_eq_true.1 hD
  simp only [Bool.and_eq_true] at hQc
  obtain ⟨⟨hA, hB⟩, hC'⟩ := hQc
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · simpa only [MatP_mulV] using eqK_iff.1 hA
  · simpa only [MatP_mulV] using eqK_iff.1 hB
  · simpa only [MatP_mulV] using eqK_iff.1 hC'

end CFSG.KC.Co2Span
