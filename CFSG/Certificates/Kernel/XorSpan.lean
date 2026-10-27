module

public import Certificates.Data.Kernel.XorSel
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.KC.XorSel

open CFSG.KLie.CT

theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem selK_cons (e : ℕ) (L : List ℕ) (c : ℕ) :
    selK (e :: L) c = (if c.testBit 0 then e else 0) ^^^ selK L (c >>> 1) := by
  change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 e (bit c 0)) (selK L (Nat.shiftRight c 1)) = _
  rw [bit_eq]
  cases c.testBit 0 <;> rfl

theorem selK_zero : ∀ L : List ℕ, selK L 0 = 0
  | [] => rfl
  | e :: L => by
    rw [selK_cons, Nat.zero_shiftRight, selK_zero L]
    simp

theorem xor_xor_cancel (e x y : ℕ) : (e ^^^ x) ^^^ (e ^^^ y) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases e.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl

theorem xor_xor_left (e x y : ℕ) : e ^^^ (x ^^^ y) = (e ^^^ x) ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases e.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl

theorem xor_xor_right (e x y : ℕ) : e ^^^ (x ^^^ y) = x ^^^ (e ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases e.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl

theorem selK_xor : ∀ (L : List ℕ) (a b : ℕ), selK L (a ^^^ b) = selK L a ^^^ selK L b
  | [], _, _ => by
    change (0 : ℕ) = 0 ^^^ 0
    simp
  | e :: L, a, b => by
    rw [selK_cons, selK_cons, selK_cons, Nat.shiftRight_xor_distrib, selK_xor L, Nat.testBit_xor]
    cases a.testBit 0 <;> cases b.testBit 0
    · simp
    · simp only [Bool.false_xor, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      exact xor_xor_right e _ _
    · simp only [Bool.xor_false, ↓reduceIte, Bool.false_eq_true, Nat.zero_xor]
      exact xor_xor_left e _ _
    · simp only [Bool.xor_self, Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
      exact (xor_xor_cancel e _ _).symm

theorem selK_two_pow : ∀ (L : List ℕ) (i : ℕ), i < L.length → selK L (2 ^ i) = L.getD i 0
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | e :: L, 0, _ => by
    rw [selK_cons]
    simp [selK_zero]
  | e :: L, i + 1, h => by
    rw [selK_cons]
    have h1 : (2 ^ (i + 1)).testBit 0 = false := by
      rw [Nat.testBit_two_pow]
      simp
    have h2 : 2 ^ (i + 1) >>> 1 = 2 ^ i := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.pow_one, Nat.mul_div_cancel _ (by norm_num)]
    rw [h1, h2, selK_two_pow L i (by simpa using h)]
    simp

theorem selAll_spec {E : List ℕ} : ∀ {V M : List ℕ}, selAllK E V M = true →
    V.length = M.length ∧ ∀ i < V.length, V.getD i 0 = selK E (M.getD i 0)
  | [], [], _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | v :: V, m :: M, h => by
    have h' : andB (Nat.beq v (selK E m)) (selAllK E V M) = true := h
    obtain ⟨h1, h2⟩ := andB_iff.1 h'
    obtain ⟨hl, hs⟩ := selAll_spec h2
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ i => exact hs i (by simpa using hi)

theorem pw2_eq' (w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem pivGo_spec {N : ℕ} : ∀ {P pv : List ℕ} {lo : ℕ}, pivGo N P pv lo = true →
    pv.length = P.length ∧ ∀ k < P.length, lo ≤ pv.getD k 0 ∧ pv.getD k 0 < N ∧
      (P.getD k 0).testBit (pv.getD k 0) = true ∧
      (∀ q < pv.getD k 0, (P.getD k 0).testBit q = false) ∧
      ∀ j < k, pv.getD j 0 < pv.getD k 0
  | [], [], _, _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], _, h => (Bool.false_ne_true h).elim
  | x :: P, p :: pv, lo, h => by
    have h' : andB (Nat.ble lo p) (andB (Nat.blt p N) (andB (bit x p)
        (andB (Nat.beq (Nat.land x (Nat.sub (pw2 p) 1)) 0) (pivGo N P pv (Nat.succ p))))) = true := h
    obtain ⟨h1, h'⟩ := andB_iff.1 h'
    obtain ⟨h2, h'⟩ := andB_iff.1 h'
    obtain ⟨h3, h'⟩ := andB_iff.1 h'
    obtain ⟨h4, h5⟩ := andB_iff.1 h'
    obtain ⟨hl, hs⟩ := pivGo_spec h5
    have hlo : lo ≤ p := by simpa using h1
    have hpN : p < N := by simpa using h2
    have hx : x.testBit p = true := by rw [← bit_eq]; exact h3
    have hm : x % 2 ^ p = 0 := by
      have e := Nat.eq_of_beq_eq_true h4
      rw [pw2_eq'] at e
      have e' : x &&& 2 ^ p - 1 = 0 := e
      rwa [Nat.and_two_pow_sub_one_eq_mod] at e'
    have hq : ∀ q < p, x.testBit q = false := by
      intro q hq
      have := Nat.testBit_mod_two_pow x p q
      rw [hm, Nat.zero_testBit] at this
      simp only [hq, decide_true, Bool.true_and] at this
      exact this.symm
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨hlo, hpN, hx, hq, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k =>
      obtain ⟨a1, a2, a3, a4, a5⟩ := hs k (by simpa using hk)
      refine ⟨by simp only [List.getD_cons_succ]; omega, by simpa using a2, by simpa using a3,
        by simpa using a4, fun j hj => ?_⟩
      cases j with
      | zero => simp only [List.getD_cons_succ, List.getD_cons_zero]; omega
      | succ j => simpa using a5 j (by omega)

theorem piv_spec {N : ℕ} {P pv : List ℕ} (h : pivOK N P pv = true) :
    pv.length = P.length ∧ ∀ k < P.length, pv.getD k 0 < N ∧
      (P.getD k 0).testBit (pv.getD k 0) = true ∧
      (∀ q < pv.getD k 0, (P.getD k 0).testBit q = false) ∧
      ∀ j < k, pv.getD j 0 < pv.getD k 0 := by
  obtain ⟨hl, hs⟩ := pivGo_spec h
  exact ⟨hl, fun k hk => (hs k hk).2⟩

@[expose] def tv (N m : ℕ) : Fin N → ZMod 2 := fun i => if m.testBit i then 1 else 0

theorem tv_xor (N a b : ℕ) : tv N (a ^^^ b) = tv N a + tv N b := by
  funext i
  simp only [tv, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem tv_zero (N : ℕ) : tv N 0 = 0 := by
  funext i
  simp [tv]

@[expose] noncomputable def spanL (N : ℕ) (L : List ℕ) : Submodule (ZMod 2) (Fin N → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ e ∈ L, tv N e = v}

theorem tv_selK_mem (N : ℕ) : ∀ (L : List ℕ) (c : ℕ), tv N (selK L c) ∈ spanL N L
  | [], c => by
    change tv N 0 ∈ _
    rw [tv_zero]
    exact Submodule.zero_mem _
  | e :: L, c => by
    rw [selK_cons, tv_xor]
    refine Submodule.add_mem _ ?_ ?_
    · split_ifs
      · exact Submodule.subset_span ⟨e, List.mem_cons_self, rfl⟩
      · rw [tv_zero]
        exact Submodule.zero_mem _
    · refine Submodule.span_mono ?_ (tv_selK_mem N L _)
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, List.mem_cons_of_mem _ hx, rfl⟩

theorem finrank_spanL_le (N : ℕ) (L : List ℕ) : Module.finrank (ZMod 2) (spanL N L) ≤ L.length := by
  classical
  have e : {v | ∃ e ∈ L, tv N e = v} = ((L.map (tv N)).toFinset : Set (Fin N → ZMod 2)) := by
    ext v
    simp [eq_comm]
  have h := finrank_span_finset_le_card (R := ZMod 2) (L.map (tv N)).toFinset
  rw [← e] at h
  exact h.trans ((List.toFinset_card_le _).trans (by simp))

theorem spanL_append (N : ℕ) (E F : List ℕ) : spanL N (E ++ F) = spanL N E ⊔ spanL N F := by
  unfold spanL
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [List.mem_append, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

theorem indep_of_piv {N : ℕ} {P pv : List ℕ} (h : pivOK N P pv = true) :
    LinearIndependent (ZMod 2) (fun k : Fin P.length => tv N (P.getD k 0)) := by
  classical
  obtain ⟨-, hs⟩ := piv_spec h
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hne
  set s' := s.filter (fun j => c j ≠ 0) with hs'
  have hne' : s'.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  set i0 := s'.min' hne' with hi0
  have hi0m : i0 ∈ s' := Finset.min'_mem s' hne'
  obtain ⟨hi0s, hci0⟩ := Finset.mem_filter.1 hi0m
  obtain ⟨hpN, hp1, -, -⟩ := hs i0 i0.isLt
  set p : Fin N := ⟨pv.getD i0 0, hpN⟩ with hp
  have hev := congrFun hsum p
  rw [Finset.sum_apply, Pi.zero_apply, Finset.sum_eq_single i0] at hev
  · simp only [Pi.smul_apply, smul_eq_mul, tv, hp, hp1, ↓reduceIte, mul_one] at hev
    exact hci0 hev
  · intro j hj hji
    by_cases hcj : c j = 0
    · simp [hcj]
    · have hjm : j ∈ s' := Finset.mem_filter.2 ⟨hj, hcj⟩
      have hle : i0 ≤ j := Finset.min'_le s' j hjm
      have hlt : i0.val < j.val := lt_of_le_of_ne hle (fun e => hji (Fin.ext e).symm)
      have hpl := (hs j j.isLt).2.2.2 i0 hlt
      have hb := (hs j j.isLt).2.2.1 _ hpl
      simp only [Pi.smul_apply, smul_eq_mul, tv, hp, hb, Bool.false_eq_true, ↓reduceIte, mul_zero]
  · intro h'
    exact absurd hi0s h'

theorem finrank_span_piv {N : ℕ} {P pv : List ℕ} (h : pivOK N P pv = true) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range fun k : Fin P.length => tv N (P.getD k 0))) = P.length := by
  rw [finrank_span_eq_card (indep_of_piv h), Fintype.card_fin]

@[expose] def selSub (N : ℕ) (L : List ℕ) : Submodule (ZMod 2) (Fin N → ZMod 2) where
  carrier := {w | ∃ t < 2 ^ L.length, w = tv N (selK L t)}
  add_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t ^^^ t', Nat.xor_lt_two_pow ht ht', by rw [selK_xor, tv_xor]⟩
  zero_mem' := ⟨0, Nat.two_pow_pos _, by rw [selK_zero, tv_zero]⟩
  smul_mem' := by
    rintro c _ ⟨t, ht, rfl⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact ⟨0, Nat.two_pow_pos _, by rw [zero_smul, selK_zero, tv_zero]⟩
    · exact ⟨t, ht, by rw [one_smul]⟩

theorem inter_sel {N : ℕ} {E E₂ L P pvL pvP CL CL₂ CP : List ℕ}
    (h1 : selAllK E L CL = true) (h2 : selAllK E₂ L CL₂ = true)
    (h3 : selAllK (E ++ E₂) P CP = true) (hL : pivOK N L pvL = true)
    (hP : pivOK N P pvP = true) (hd : E.length + E₂.length ≤ P.length + L.length) {a b : ℕ}
    (h : tv N (selK E a) = tv N (selK E₂ b)) :
    ∃ t < 2 ^ L.length, tv N (selK E a) = tv N (selK L t) := by
  set A := spanL N E
  set B := spanL N E₂
  have hvA : tv N (selK E a) ∈ A := tv_selK_mem N E a
  have hvB : tv N (selK E a) ∈ B := by rw [h]; exact tv_selK_mem N E₂ b
  obtain ⟨hl3, hs3⟩ := selAll_spec h3
  have hPle : Submodule.span (ZMod 2) (Set.range fun k : Fin P.length => tv N (P.getD k 0)) ≤
      A ⊔ B := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change tv N (P.getD k 0) ∈ A ⊔ B
    rw [hs3 k k.isLt, ← spanL_append]
    exact tv_selK_mem N _ _
  have hsup : P.length ≤ Module.finrank (ZMod 2) ↥(A ⊔ B) := by
    rw [← finrank_span_piv hP]
    exact Submodule.finrank_mono hPle
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hA : Module.finrank (ZMod 2) A ≤ E.length := finrank_spanL_le N E
  have hB : Module.finrank (ZMod 2) B ≤ E₂.length := finrank_spanL_le N E₂
  have hinf : Module.finrank (ZMod 2) ↥(A ⊓ B) ≤ L.length := by omega
  obtain ⟨-, hs1⟩ := selAll_spec h1
  obtain ⟨-, hs2⟩ := selAll_spec h2
  set C := Submodule.span (ZMod 2) (Set.range fun k : Fin L.length => tv N (L.getD k 0))
  have hCle : C ≤ A ⊓ B := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · change tv N (L.getD k 0) ∈ A
      rw [hs1 k k.isLt]
      exact tv_selK_mem N E _
    · change tv N (L.getD k 0) ∈ B
      rw [hs2 k k.isLt]
      exact tv_selK_mem N E₂ _
  have hCeq : C = A ⊓ B :=
    Submodule.eq_of_le_of_finrank_le hCle (by rw [finrank_span_piv hL]; exact hinf)
  have hvC : tv N (selK E a) ∈ C := by rw [hCeq]; exact ⟨hvA, hvB⟩
  have hCX : C ≤ selSub N L := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨2 ^ k.val, Nat.pow_lt_pow_right (by norm_num) k.isLt,
      by rw [selK_two_pow L k k.isLt]⟩
  exact hCX hvC

end CFSG.KC.XorSel

end
