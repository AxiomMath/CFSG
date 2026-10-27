module

public import CFSG.Certificates.Kernel.M3BSyl.Packed

public section

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 4096

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BS

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.KC.M3BF (enc dig3 vz GoodRow GoodMat Ins slpNodes slpWT bit)
open Timmesfeld.M3B (WT LM matOf sigW tMats)

theorem forall2_getD {α β : Type*} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : List.Forall₂ R as bs) (da : α) (db : β) : ∀ i < as.length, R (as.getD i da) (bs.getD i db) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i (by simpa using hi)

theorem nodesChk_spec (ns : List MatK) : ∀ (gi : List ℕ) (gs : List MatK), nodesChk ns gi gs = true →
    ∀ A ∈ gs, ∃ i < ns.length, ns.getD i idK = A ∧ GoodMat A
  | [], [], _ => by simp
  | [], A :: gs, h => by
    change (A :: gs).isEmpty = true at h
    simp at h
  | i :: gi, [], _ => by simp
  | i :: gi, A :: gs, h => by
    change (Nat.blt i ns.length && goodK A && ns.getD i idK == A && nodesChk ns gi gs) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact ⟨i, h1, h3, goodMat_of_goodK h2⟩
    · exact nodesChk_spec ns gi gs h4 B hB

theorem genChk_spec (hl : letChk = true) {gp : List Ins} {gi : List ℕ} {gs : List MatK}
    (h : genChk gp gi gs = true) : gs.length = 7 ∧ ∀ A ∈ gs, ∃ w : WT, Rep A w := by
  unfold genChk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun A hA => ?_⟩
  obtain ⟨i, hi, rfl, -⟩ := nodesChk_spec _ gi gs h.2 A hA
  exact ⟨_, node_rep (rep_letter hl) gp hi⟩

theorem tMats_get {j : ℕ} (hj : j < 3) :
    (tMats ())[j]! = matOf (LM ()) (sigW.toList.getD j (.gen 0)) := by
  have hs : sigW.size = 3 := rfl
  have hj' : j < (tMats ()).size := by simp [tMats, hs, hj]
  unfold tMats at hj' ⊢
  rw [getElem!_pos _ j hj', Array.getElem_map,
    List.getD_eq_getElem _ _ (by simp [hs, hj]), Array.getElem_toList]

theorem tChk_spec (hl : letChk = true) {tp : List (List Ins)} {tk : List MatK}
    (h : tChk tp tk = true) (htw : tp.map slpWT = sigW.toList) :
    ∀ j < 3, GoodMat (tk.getD j idK) ∧ toMatK (tk.getD j idK) = toMatrix (tMats ())[j]! := by
  unfold tChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, id] at h
  obtain ⟨⟨hp, hk⟩, hall⟩ := h
  intro j hj
  have hz : j < (List.zipWith (fun P A => goodK A && matSLP letK P == A) tp tk).length := by
    simp [hp, hk, hj]
  have hm := hall _ (List.getElem_mem hz)
  rw [List.getElem_zipWith] at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  have e1 : tk.getD j idK = tk[j]'(by omega) := List.getD_eq_getElem _ _ _
  have hr := matSLP_rep (rep_letter hl) tp[j]
  rw [hm.2] at hr
  rw [e1, tMats_get hj, ← htw, M3BF.getD_map_lt (d := []) (by omega),
    List.getD_eq_getElem _ _ (by omega)]
  exact hr

theorem mem_pcPairs {i j : ℕ} (hij : i ≤ j) (hj : j < 7) : (i, j) ∈ pcPairs := by
  unfold pcPairs
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨i, by omega, j - i, by simp only [Nat.sub_eq]; omega, rfl, by simp only [Nat.add_eq]; omega⟩

theorem pcChk_spec {gs : List MatK} {pc : List (ℕ × ℕ × List ℕ)} (h : pcChk gs pc = true)
    {i j : ℕ} (hij : i ≤ j) (hj : j < 7) :
    ∃ es : List ℕ, es.length = 7 ∧ (∀ e ∈ es.take (i + 1), e = 0) ∧
      (j = i → mmK (mmK (gs.getD i idK) (gs.getD i idK)) (gs.getD i idK) = nfK gs es) ∧
      (j ≠ i → mmK (gs.getD j idK) (gs.getD i idK) = mmK (gs.getD i idK) (nfK gs es)) := by
  unfold pcChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hm, hall⟩ := h
  have hmem := mem_pcPairs hij hj
  rw [← hm, List.mem_map] at hmem
  obtain ⟨⟨a, b, es⟩, hr, hab⟩ := hmem
  simp only [Prod.mk.injEq] at hab
  obtain ⟨rfl, rfl⟩ := hab
  have h1 := hall _ hr
  unfold pcOne at h1
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  obtain ⟨⟨hl, hz⟩, he⟩ := h1
  refine ⟨es, hl, hz, fun hji => ?_, fun hji => ?_⟩
  · subst hji
    simpa using he
  · simpa [hji] using he

theorem uChk_spec {v : ℕ} {us : List ℕ} {gs : List MatK} (h : uChk v us gs = true) :
    GoodRow v ∧ us = (gs.take 3).map (vmK v) := by
  unfold uChk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem walksChk_spec {gs : List MatK} {us : List ℕ} {wu : List (List (List ℕ))}
    (h : walksChk gs us wu = true) :
    us.length = 3 ∧ wu.length = 3 ∧ ∀ k < 3, walkChk gs (us.getD k 0) (wu.getD k []) = true := by
  unfold walksChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, id] at h
  obtain ⟨⟨hu, hw⟩, hall⟩ := h
  refine ⟨hu, hw, fun k hk => ?_⟩
  have hz : k < (List.zipWith (walkChk gs) us wu).length := by simp [hu, hw, hk]
  have := hall _ (List.getElem_mem hz)
  rw [List.getElem_zipWith] at this
  rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem nfL_replicate {G : Type*} [Monoid G] : ∀ (Us : List G) (m : ℕ), nfL Us (List.replicate m 0) = 1
  | [], _ => by simp [nfL]
  | _ :: _, 0 => by simp [nfL]
  | u :: Us, m + 1 => by
    have := nfL_replicate Us m
    simp only [nfL, List.replicate_succ, List.zipWith_cons_cons, pow_zero, List.prod_cons,
      one_mul] at this ⊢
    exact this

theorem nfL_zero {G : Type*} [Monoid G] : ∀ (Us : List G) (es : List ℕ),
    (∀ t, es.getD t 0 = 0) → nfL Us es = 1
  | [], _, _ => by simp [nfL]
  | _ :: _, [], _ => by simp [nfL]
  | u :: Us, e :: es, h => by
    have h0 : e = 0 := h 0
    have ih := nfL_zero Us es fun t => h (t + 1)
    simp only [nfL] at ih ⊢
    rw [List.zipWith_cons_cons, List.prod_cons, ih, h0, pow_zero, one_mul]

theorem nfL_step {G : Type*} [Monoid G] : ∀ (Us : List G) (es : List ℕ) (p : ℕ), p < Us.length →
    p < es.length → 1 ≤ es.getD p 0 → (∀ t, p < t → es.getD t 0 = 0) →
    nfL Us (es.set p (es.getD p 0 - 1)) * Us.getD p 1 = nfL Us es
  | u :: Us, e :: es, 0, _, _, h1, hz => by
    have hr := nfL_zero Us es fun t => hz (t + 1) (by omega)
    have h1' : 1 ≤ e := h1
    simp only [nfL] at hr ⊢
    simp only [List.getD_cons_zero, List.set_cons_zero, List.zipWith_cons_cons, List.prod_cons, hr,
      mul_one]
    rw [← pow_succ, Nat.sub_add_cancel h1']
  | u :: Us, e :: es, p + 1, hU, he, h1, hz => by
    have ih := nfL_step Us es p (by simpa using hU) (by simpa using he) h1
      fun t ht => hz (t + 1) (by omega)
    simp only [nfL] at ih ⊢
    simp only [List.getD_cons_succ, List.set_cons_succ, List.zipWith_cons_cons, List.prod_cons]
    rw [mul_assoc, ih]

@[expose] noncomputable def digStep (n : ℕ) : Bool :=
  (fun k => Nat.ble k 6 && Nat.ble (3 ^ k) n &&
    digs (n - 3 ^ k) == (digs n).set (6 - k) ((digs n).getD (6 - k) 0 - 1) &&
    Nat.ble 1 ((digs n).getD (6 - k) 0) &&
    (List.range 7).all (fun t => Nat.ble t (6 - k) || (digs n).getD t 0 == 0)) (low3 n)

theorem digStep_all : (List.range 2186).all (fun i => digStep (i + 1)) = true := by decide +kernel

theorem digs_length (n : ℕ) : (digs n).length = 7 := by simp [digs]

theorem digs_zero : digs 0 = List.replicate 7 0 := by decide +kernel

theorem walk_spec {gs : List MatK} {Us : List (GL (Fin 12) (ZMod 3))} (hU : List.Forall₂ RepU gs Us)
    (hl : Us.length = 7) {u : ℕ} {W : List (List ℕ)} (hu : GoodRow u) (h : walkChk gs u W = true) :
    ∀ n < 2187, GoodRow (getW W n) ∧ vz (getW W n) = Matrix.vecMul (vz u)
      ((nfL Us (digs n) : GL (Fin 12) (ZMod 3)) : Matrix (Fin 12) (Fin 12) (ZMod 3)) := by
  unfold walkChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, h0⟩, hstep⟩ := h
  have hgl : gs.length = 7 := by rw [hU.length_eq, hl]
  have hds := digStep_all
  simp only [List.all_eq_true, List.mem_range] at hds
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | i
    · rw [h0, digs_zero, nfL_replicate, Units.val_one, Matrix.vecMul_one]
      exact ⟨hu, rfl⟩
    · have hi : i < 2186 := by omega
      have hs := hstep i hi
      have hd := hds i hi
      unfold digStep at hd
      simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true] at hd
      obtain ⟨⟨⟨⟨hk6, hkn⟩, hset⟩, h1⟩, hz⟩ := hd
      set k := low3 (i + 1) with hkdef
      have hpos : 0 < 3 ^ k := pow_pos (by norm_num) k
      obtain ⟨g1, g2⟩ := ih (i + 1 - 3 ^ k) (by omega) (by omega)
      have hr := forall2_getD hU idK 1 (6 - k) (by omega)
      change getW W (i + 1) = vmK (getW W (i + 1 - 3 ^ k)) (gs.getD (6 - k) idK) at hs
      rw [hs]
      refine ⟨goodRow_vmK _ _, ?_⟩
      have hz' : ∀ t, 6 - k < t → (digs (i + 1)).getD t 0 = 0 := by
        intro t ht
        by_cases ht7 : t < 7
        · rcases hz t ht7 with h | h
          · omega
          · exact h
        · exact List.getD_eq_default _ _ (by rw [digs_length]; omega)
      rw [vz_vmK hr.1, g2, hr.2, Matrix.vecMul_vecMul, ← Units.val_mul, hset,
        nfL_step Us (digs (i + 1)) (6 - k) (by omega) (by rw [digs_length]; omega) h1 hz']

theorem ordRun_spec (W : List (List ℕ)) : ∀ (ko : List ℕ) (b m M : ℕ), ordRun W ko b m = some M →
    (∀ x ∈ ko, b ≤ getW W x) ∧ ko.Pairwise (fun x y => getW W x < getW W y) ∧
      ∀ i, M.testBit i = true → m.testBit i = true ∨ i ∈ ko
  | [], b, m, M, h => by
    change some m = some M at h
    cases h
    exact ⟨by simp, List.Pairwise.nil, fun i hi => Or.inl hi⟩
  | x :: ko, b, m, M, h => by
    unfold ordRun at h
    dsimp only at h
    rw [cond_eq_if] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
    obtain ⟨h1, h2, h3⟩ := ordRun_spec W ko _ _ M h
    refine ⟨fun y hy => ?_, List.Pairwise.cons (fun y hy => ?_) h2, fun i hi => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hc.2
      · have := h1 y hy
        omega
    · have := h1 y hy
      omega
    · rcases h3 i hi with hi | hi
      · rcases (M3BF.f13S_testBit_lor_pow _ _ _).1 hi with hi | rfl
        · exact Or.inl hi
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ hi)

theorem ordChk_spec {W : List (List ℕ)} {ko : List ℕ} (h : ordChk W ko = true) {a b : ℕ}
    (ha : a < 2187) (hb : b < 2187) (he : getW W a = getW W b) : a = b := by
  unfold ordChk at h
  rw [beq_iff_eq] at h
  obtain ⟨-, h2, h3⟩ := ordRun_spec W ko 0 0 _ h
  have hin : ∀ i < 2187, i ∈ ko := by
    intro i hi
    rcases h3 i (by
      change (2 ^ 2187 - 1).testBit i = true
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hi) with h | h
    · simp at h
    · exact h
  have key : ∀ l : List ℕ, l.Pairwise (fun x y => getW W x < getW W y) →
      ∀ x ∈ l, ∀ y ∈ l, getW W x = getW W y → x = y := by
    intro l hl
    induction hl with
    | nil => simp
    | @cons z l hxl _ ih =>
      intro x hx y hy hxy
      rcases List.mem_cons.1 hx with hx | hx <;> rcases List.mem_cons.1 hy with hy | hy
      · rw [hx, hy]
      · rw [hx] at hxy
        exact absurd hxy (ne_of_lt (hxl y hy))
      · rw [hy] at hxy
        exact absurd hxy.symm (ne_of_lt (hxl x hx))
      · exact ih x hx y hy hxy
  exact key ko h2 a (hin a ha) b (hin b hb) he

theorem maskOf_spec : ∀ (rs : List ℕ) (i : ℕ), (maskOf rs).testBit i = true → i ∈ rs
  | [], i, h => by
    change (0 : ℕ).testBit i = true at h
    simp at h
  | r :: rs, i, h => by
    change (Nat.lor (maskOf rs) (Nat.pow 2 r)).testBit i = true at h
    rcases (M3BF.f13S_testBit_lor_pow _ _ _).1 h with h | rfl
    · exact List.mem_cons_of_mem _ (maskOf_spec rs i h)
    · exact List.mem_cons_self

theorem rowsW_spec {gs : List MatK} {wv : List (List ℕ)} {wu : List (List (List ℕ))} {P : ℕ → Prop}
    (hstep : ∀ n p k, n < 2187 → k < 3 → vmK (getW wv n) (gs.getD k idK) = getW (wu.getD k []) p →
      P p → P n) :
    ∀ (rows : List (ℕ × ℕ × ℕ)) (m M : ℕ), (∀ i, m.testBit i = true → P i) →
      rowsW gs wv wu rows m = some M → ∀ i, M.testBit i = true → P i
  | [], m, M, hm, h => by
    change some m = some M at h
    cases h
    exact hm
  | r :: rows, m, M, hm, h => by
    unfold rowsW at h
    dsimp only at h
    rw [cond_eq_if] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, M3BF.f13S_bit] at hc
    obtain ⟨⟨⟨hn, hb⟩, hk⟩, he⟩ := hc
    have hr : P r.1 := hstep _ _ _ hn hk he (hm _ hb)
    refine rowsW_spec hstep rows (Nat.lor m (Nat.pow 2 r.1)) M ?_ h
    intro i hi
    rcases (M3BF.f13S_testBit_lor_pow _ _ _).1 hi with hi | rfl
    · exact hm i hi
    · exact hr

theorem testBit_mask (i : ℕ) (h0 : 0 < i) (h : i < 2187) : (2 ^ 2187 - 2).testBit i = true := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.testBit_succ, (by decide +kernel : (2 ^ 2187 - 2) / 2 = 2 ^ 2186 - 1),
    Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  omega

theorem forestW_spec {gs : List MatK} {wv : List (List ℕ)} {wu : List (List (List ℕ))}
    {rs : List ℕ} {rows : List (ℕ × ℕ × ℕ)} (h : forestW gs wv wu rs rows = true) (P : ℕ → Prop)
    (hroot : ∀ r ∈ rs, P r)
    (hstep : ∀ n p k, n < 2187 → k < 3 → vmK (getW wv n) (gs.getD k idK) = getW (wu.getD k []) p →
      P p → P n) :
    ∀ n, 0 < n → n < 2187 → P n := by
  unfold forestW at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  intro n h0 hn
  refine rowsW_spec hstep rows _ _ (fun i hi => hroot i (maskOf_spec rs i hi)) h.2 n ?_
  exact testBit_mask n h0 hn

theorem r3Chk_spec {gs tk : List MatK} {cp : List Ins} {r3 : List (ℕ × ℕ × ℕ)}
    (h : r3Chk gs tk cp r3 = true) : ∀ r ∈ r3, r.1 < 2187 ∧ r.2.1 < 3 ∧
      r.2.2 < (nodesK letK cp).length ∧
      mmK (nfK gs (digs r.1)) ((nodesK letK cp).getD r.2.2 idK) =
        mmK ((nodesK letK cp).getD r.2.2 idK) (tk.getD r.2.1 idK) := by
  unfold r3Chk at h
  simp only [List.all_eq_true, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  intro r hr
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h r hr
  exact ⟨h1, h2, h3, h4⟩

theorem r9Chk_spec {gs : List MatK} {v : ℕ} {r9 : List ℕ} (h : r9Chk gs v r9 = true) :
    ∀ n ∈ r9, n < 2187 ∧ nfV gs (digs n) (nfV gs (digs n) (nfV gs (digs n) v)) ≠ v := by
  unfold r9Chk at h
  simp only [List.all_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    at h
  exact h

end CFSG.KC.M3BS

end
