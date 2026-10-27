module

public import CFSG.Certificates.Kernel.Misc.Ree2Pack

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop CFSG.Walter.Ree.Bombieri Polynomial

variable {K : Type*} [Field K]

noncomputable def phi (q1 : ℕ) (γ : K) (e : ℕ) : K := if e < q1 then γ ^ e else 0

structure LogEnv (q1 hf ZT : ℕ) (γ : K) : Prop where
  pos : 0 < q1
  hf_lt : hf < q1
  pow_q1 : γ ^ q1 = 1
  pow_hf : γ ^ hf = -1
  zech_le : ∀ d < q1, zech ZT d ≤ q1
  zech_eq : ∀ d < q1, 1 + γ ^ d = phi q1 γ (zech ZT d)

variable {q1 hf ZT : ℕ} {γ : K}

theorem phi_lt {e : ℕ} (h : e < q1) : phi q1 γ e = γ ^ e := by simp [phi, h]

theorem phi_ge {e : ℕ} (h : q1 ≤ e) : phi q1 γ e = 0 := by
  have he : ¬ e < q1 := by omega
  simp [phi, he]

theorem phi_q1 : phi q1 γ q1 = 0 := phi_ge le_rfl

theorem mulL_eq (a b : ℕ) :
    mulL q1 a b = if a = q1 then q1 else if b = q1 then q1 else (a + b) % q1 := by
  unfold mulL
  simp only [nIf_eq, nbeq, decide_eq_true_eq]
  rfl

theorem addL_eq (a b : ℕ) : addL q1 ZT a b = if a = q1 then b else if b = q1 then a else
    if zech ZT ((b + q1 - a) % q1) = q1 then q1 else (a + zech ZT ((b + q1 - a) % q1)) % q1 := by
  unfold addL
  simp only [nIf_eq, nbeq, sN, decide_eq_true_eq]
  rfl

theorem negL_eq (a : ℕ) : negL q1 hf a = if a = q1 then q1 else (a + hf) % q1 := by
  unfold negL
  simp only [nIf_eq, nbeq, decide_eq_true_eq]
  rfl

theorem invL_eq (a : ℕ) : invL q1 a = (q1 - a) % q1 := rfl

theorem powL_eq (a n : ℕ) :
    powL q1 a n = if n = 0 then 0 else if a = q1 then q1 else a * n % q1 := by
  unfold powL
  simp only [nIf_eq, nbeq, decide_eq_true_eq]
  rfl

theorem resL_eq (v : ℕ) :
    resL q1 hf v = if v % 3 = 0 then q1 else if v % 3 = 1 then 0 else hf := by
  unfold resL
  simp only [nIf_eq, nbeq, sN, decide_eq_true_eq]
  rfl

namespace LogEnv

variable (E : LogEnv q1 hf ZT γ)
include E

theorem pow_mod (e : ℕ) : γ ^ (e % q1) = γ ^ e := by
  conv_rhs => rw [← Nat.mod_add_div e q1, pow_add, pow_mul, E.pow_q1, one_pow, mul_one]

theorem phi_mod (e : ℕ) : phi q1 γ (e % q1) = γ ^ e := by
  rw [phi_lt (Nat.mod_lt _ E.pos), E.pow_mod]

theorem ne_zero : γ ≠ 0 := by
  intro h
  have := E.pow_q1
  rw [h, zero_pow E.pos.ne'] at this
  exact zero_ne_one this

theorem phi_ne_zero {a : ℕ} (ha : a ≤ q1) (h : a ≠ q1) : phi q1 γ a ≠ 0 := by
  rw [phi_lt (by omega)]
  exact pow_ne_zero _ E.ne_zero

theorem phi_eq_zero_iff {a : ℕ} (ha : a ≤ q1) : phi q1 γ a = 0 ↔ a = q1 :=
  ⟨fun h => by_contra fun h' => E.phi_ne_zero ha h' h, fun h => h ▸ phi_q1⟩

theorem phi_zero : phi q1 γ 0 = 1 := by rw [phi_lt E.pos, pow_zero]

theorem mulL_spec {a b : ℕ} (ha : a ≤ q1) (hb : b ≤ q1) :
    mulL q1 a b ≤ q1 ∧ phi q1 γ (mulL q1 a b) = phi q1 γ a * phi q1 γ b := by
  rw [mulL_eq]
  split_ifs with h1 h2
  · subst h1; simp [phi_q1]
  · subst h2; simp [phi_q1]
  · refine ⟨(Nat.mod_lt _ E.pos).le, ?_⟩
    rw [E.phi_mod, phi_lt (by omega), phi_lt (by omega), pow_add]

theorem addL_spec {a b : ℕ} (ha : a ≤ q1) (hb : b ≤ q1) :
    addL q1 ZT a b ≤ q1 ∧ phi q1 γ (addL q1 ZT a b) = phi q1 γ a + phi q1 γ b := by
  rw [addL_eq]
  have hd : (b + q1 - a) % q1 < q1 := Nat.mod_lt _ E.pos
  have hz := E.zech_eq _ hd
  have hzl := E.zech_le _ hd
  split_ifs with h1 h2 h3
  · subst h1; simp [phi_q1, hb]
  · subst h2; simp [phi_q1, ha]
  · refine ⟨le_rfl, ?_⟩
    rw [h3, phi_q1] at hz
    rw [phi_q1, phi_lt (by omega : a < q1), phi_lt (by omega : b < q1)]
    have e : γ ^ b = γ ^ a * γ ^ ((b + q1 - a) % q1) := by
      rw [E.pow_mod, ← pow_add, (by omega : a + (b + q1 - a) = b + q1), pow_add, E.pow_q1,
        mul_one]
    rw [e]
    linear_combination (-γ ^ a) * hz
  · refine ⟨(Nat.mod_lt _ E.pos).le, ?_⟩
    rw [E.phi_mod, pow_add, ← phi_lt (by omega : zech ZT ((b + q1 - a) % q1) < q1), ← hz,
      phi_lt (by omega : a < q1), phi_lt (by omega : b < q1)]
    have e : γ ^ b = γ ^ a * γ ^ ((b + q1 - a) % q1) := by
      rw [E.pow_mod, ← pow_add, (by omega : a + (b + q1 - a) = b + q1), pow_add, E.pow_q1,
        mul_one]
    rw [e]
    ring

theorem negL_spec {a : ℕ} (ha : a ≤ q1) :
    negL q1 hf a ≤ q1 ∧ phi q1 γ (negL q1 hf a) = -phi q1 γ a := by
  rw [negL_eq]
  split_ifs with h1
  · subst h1; simp [phi_q1]
  · refine ⟨(Nat.mod_lt _ E.pos).le, ?_⟩
    rw [E.phi_mod, pow_add, E.pow_hf, phi_lt (by omega)]
    ring

theorem subL_spec {a b : ℕ} (ha : a ≤ q1) (hb : b ≤ q1) :
    subL q1 hf ZT a b ≤ q1 ∧ phi q1 γ (subL q1 hf ZT a b) = phi q1 γ a - phi q1 γ b := by
  obtain ⟨h1, h2⟩ := E.negL_spec hb
  obtain ⟨h3, h4⟩ := E.addL_spec ha h1
  exact ⟨h3, by rw [subL, h4, h2, sub_eq_add_neg]⟩

theorem invL_le (a : ℕ) : invL q1 a ≤ q1 := by
  rw [invL_eq]; exact (Nat.mod_lt _ E.pos).le

theorem invL_spec {a : ℕ} (ha : a < q1) : phi q1 γ (invL q1 a) = (phi q1 γ a)⁻¹ := by
  rw [invL_eq, E.phi_mod, phi_lt ha]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, Nat.sub_add_cancel ha.le, E.pow_q1]

theorem powL_spec {a : ℕ} (ha : a ≤ q1) (n : ℕ) :
    powL q1 a n ≤ q1 ∧ phi q1 γ (powL q1 a n) = phi q1 γ a ^ n := by
  rw [powL_eq]
  split_ifs with h1 h2
  · subst h1; simp [E.phi_zero, E.pos.le]
  · subst h2; simp [phi_q1, h1]
  · refine ⟨(Nat.mod_lt _ E.pos).le, ?_⟩
    rw [E.phi_mod, phi_lt (by omega), pow_mul]

theorem resL_spec [CharP K 3] (v : ℕ) :
    resL q1 hf v ≤ q1 ∧ phi q1 γ (resL q1 hf v) = (v : K) := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hv : (v : K) = ((v % 3 : ℕ) : K) := by
    conv_lhs => rw [← Nat.mod_add_div v 3]
    push_cast
    rw [h3, zero_mul, add_zero]
  rw [resL_eq, hv]
  split_ifs with h1 h2
  · rw [h1]; simp [phi_q1]
  · rw [h2]; simp [E.phi_zero, E.pos.le]
  · have h2' : v % 3 = 2 := by omega
    refine ⟨E.hf_lt.le, ?_⟩
    rw [h2', phi_lt E.hf_lt, E.pow_hf]
    push_cast
    linear_combination -h3

theorem constL_spec [CharP K 3] (c : ℤ) :
    constL q1 hf c ≤ q1 ∧ phi q1 γ (constL q1 hf c) = (c : K) := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  cases c with
  | ofNat n =>
    obtain ⟨h1, h2⟩ := E.resL_spec n
    refine ⟨h1, ?_⟩
    change phi q1 γ (resL q1 hf n) = _
    rw [h2]
    simp
  | negSucc n =>
    obtain ⟨h1, h2⟩ := E.resL_spec (2 * (n + 1))
    refine ⟨h1, ?_⟩
    change phi q1 γ (resL q1 hf (2 * (n + 1))) = _
    rw [h2, Int.cast_negSucc]
    push_cast
    linear_combination (n + 1 : K) * h3

end LogEnv

section evalL

variable {q1 hf ZT : ℕ} {ρ α : ℕ → ℕ}

theorem evalL_var (i : ℕ) : evalL q1 hf ZT ρ α (PE.var i) = ρ i := rfl

theorem evalL_atom (k : ℕ) : evalL q1 hf ZT ρ α (PE.atom k) = α k := rfl

theorem evalL_const (c : ℤ) : evalL q1 hf ZT ρ α (PE.const c) = constL q1 hf c := rfl

theorem evalL_add (a b : PE) : evalL q1 hf ZT ρ α (PE.add a b) =
    addL q1 ZT (evalL q1 hf ZT ρ α a) (evalL q1 hf ZT ρ α b) := by
  change strictN (evalL q1 hf ZT ρ α a)
    (fun x => strictN (evalL q1 hf ZT ρ α b) (fun y => addL q1 ZT x y)) = _
  rw [sN, sN]

theorem evalL_sub (a b : PE) : evalL q1 hf ZT ρ α (PE.sub a b) =
    subL q1 hf ZT (evalL q1 hf ZT ρ α a) (evalL q1 hf ZT ρ α b) := by
  change strictN (evalL q1 hf ZT ρ α a)
    (fun x => strictN (evalL q1 hf ZT ρ α b) (fun y => subL q1 hf ZT x y)) = _
  rw [sN, sN]

theorem evalL_mul (a b : PE) : evalL q1 hf ZT ρ α (PE.mul a b) =
    mulL q1 (evalL q1 hf ZT ρ α a) (evalL q1 hf ZT ρ α b) := by
  change strictN (evalL q1 hf ZT ρ α a)
    (fun x => strictN (evalL q1 hf ZT ρ α b) (fun y => mulL q1 x y)) = _
  rw [sN, sN]

theorem evalL_pow (a : PE) (n : ℕ) : evalL q1 hf ZT ρ α (PE.pow a n) =
    powL q1 (evalL q1 hf ZT ρ α a) n := by
  change strictN (evalL q1 hf ZT ρ α a) (fun x => powL q1 x n) = _
  rw [sN]

theorem evalL_neg (a : PE) : evalL q1 hf ZT ρ α (PE.neg a) =
    negL q1 hf (evalL q1 hf ZT ρ α a) := by
  change strictN (evalL q1 hf ZT ρ α a) (fun x => negL q1 hf x) = _
  rw [sN]

theorem LogEnv.evalL_spec [CharP K 3] {γ : K} (E : LogEnv q1 hf ZT γ) (hρ : ∀ i, ρ i ≤ q1)
    (hα : ∀ k, α k ≤ q1) : ∀ e : PE, evalL q1 hf ZT ρ α e ≤ q1 ∧
      phi q1 γ (evalL q1 hf ZT ρ α e) = PE.eval (phi q1 γ ∘ ρ) (phi q1 γ ∘ α) e
  | PE.var i => ⟨hρ i, rfl⟩
  | PE.atom k => ⟨hα k, rfl⟩
  | PE.const c => by
    rw [evalL_const]
    exact E.constL_spec c
  | PE.add a b => by
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ hα a
    obtain ⟨h3, h4⟩ := E.evalL_spec hρ hα b
    obtain ⟨h5, h6⟩ := E.addL_spec h1 h3
    rw [evalL_add]
    exact ⟨h5, by rw [h6, h2, h4]; rfl⟩
  | PE.sub a b => by
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ hα a
    obtain ⟨h3, h4⟩ := E.evalL_spec hρ hα b
    obtain ⟨h5, h6⟩ := E.subL_spec h1 h3
    rw [evalL_sub]
    exact ⟨h5, by rw [h6, h2, h4]; rfl⟩
  | PE.mul a b => by
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ hα a
    obtain ⟨h3, h4⟩ := E.evalL_spec hρ hα b
    obtain ⟨h5, h6⟩ := E.mulL_spec h1 h3
    rw [evalL_mul]
    exact ⟨h5, by rw [h6, h2, h4]; rfl⟩
  | PE.pow a n => by
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ hα a
    obtain ⟨h5, h6⟩ := E.powL_spec h1 n
    rw [evalL_pow]
    exact ⟨h5, by rw [h6, h2]; rfl⟩
  | PE.neg a => by
    obtain ⟨h1, h2⟩ := E.evalL_spec hρ hα a
    obtain ⟨h5, h6⟩ := E.negL_spec h1
    rw [evalL_neg]
    exact ⟨h5, by rw [h6, h2]; rfl⟩

end evalL

noncomputable def polyL (q1 : ℕ) (γ : K) : List ℕ → K[X]
  | [] => 0
  | a :: l => C (phi q1 γ a) + X * polyL q1 γ l

theorem polyL_nil : polyL q1 γ [] = 0 := by rw [polyL]

theorem polyL_cons (a : ℕ) (l : List ℕ) :
    polyL q1 γ (a :: l) = C (phi q1 γ a) + X * polyL q1 γ l := by
  rw [polyL]

theorem coeff_polyL : ∀ (l : List ℕ) (i : ℕ), (polyL q1 γ l).coeff i = phi q1 γ (l.getD i q1)
  | [], i => by simp [polyL_nil, phi_q1]
  | a :: l, 0 => by simp [polyL_cons]
  | a :: l, i + 1 => by
    rw [polyL_cons, coeff_add, coeff_C_succ, zero_add, coeff_X_mul, coeff_polyL l i]
    simp

theorem natDegree_polyL_le (l : List ℕ) : (polyL q1 γ l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_polyL, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  exact phi_q1

theorem hornerL_nil (x : ℕ) : hornerL q1 ZT [] x = q1 := rfl

theorem hornerL_cons (a : ℕ) (l : List ℕ) (x : ℕ) :
    hornerL q1 ZT (a :: l) x = addL q1 ZT a (mulL q1 x (hornerL q1 ZT l x)) := by
  change strictN (hornerL q1 ZT l x) (fun h => addL q1 ZT a (mulL q1 x h)) = _
  rw [sN]

theorem LogEnv.hornerL_spec (E : LogEnv q1 hf ZT γ) {x : ℕ} (hx : x ≤ q1) :
    ∀ {l : List ℕ}, (∀ a ∈ l, a ≤ q1) →
      hornerL q1 ZT l x ≤ q1 ∧ phi q1 γ (hornerL q1 ZT l x) = (polyL q1 γ l).eval (phi q1 γ x)
  | [], _ => ⟨le_rfl, by simp [hornerL_nil, polyL_nil, phi_q1]⟩
  | a :: l, hl => by
    obtain ⟨h1, h2⟩ := E.hornerL_spec hx (l := l) (fun b hb => hl b (by simp [hb]))
    obtain ⟨h3, h4⟩ := E.mulL_spec hx h1
    obtain ⟨h5, h6⟩ := E.addL_spec (hl a (by simp)) h3
    rw [hornerL_cons]
    refine ⟨h5, ?_⟩
    rw [h6, h4, h2, polyL_cons, eval_add, eval_C, eval_mul, eval_X]

theorem LogEnv.loopN_addL (E : LogEnv q1 hf ZT γ) {u : ℕ → ℕ} :
    ∀ (n b a : ℕ), (∀ i, b ≤ i → i < b + n → u i ≤ q1) → a ≤ q1 →
      loopN n b (fun i acc => addL q1 ZT acc (u i)) a ≤ q1 ∧
      phi q1 γ (loopN n b (fun i acc => addL q1 ZT acc (u i)) a) =
        phi q1 γ a + ∑ i ∈ Finset.range n, phi q1 γ (u (b + i))
  | 0, b, a, _, ha => ⟨ha, by simp [loopN_zero]⟩
  | n + 1, b, a, hu, ha => by
    obtain ⟨h1, h2⟩ := E.addL_spec ha (hu b le_rfl (by omega))
    obtain ⟨h3, h4⟩ := E.loopN_addL n (b + 1) _ (fun i h1 h2 => hu i (by omega) (by omega)) h1
    rw [loopN_succ]
    refine ⟨h3, ?_⟩
    rw [h4, h2, Finset.sum_range_succ', add_zero, add_assoc, add_comm (phi q1 γ (u b))]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    omega

theorem LogEnv.loopN_mulL (E : LogEnv q1 hf ZT γ) {u : ℕ → ℕ} :
    ∀ (n b a : ℕ), (∀ i, b ≤ i → i < b + n → u i ≤ q1) → a ≤ q1 →
      loopN n b (fun i d => mulL q1 d (u i)) a ≤ q1 ∧
      phi q1 γ (loopN n b (fun i d => mulL q1 d (u i)) a) =
        phi q1 γ a * ∏ i ∈ Finset.range n, phi q1 γ (u (b + i))
  | 0, b, a, _, ha => ⟨ha, by simp [loopN_zero]⟩
  | n + 1, b, a, hu, ha => by
    obtain ⟨h1, h2⟩ := E.mulL_spec ha (hu b le_rfl (by omega))
    obtain ⟨h3, h4⟩ := E.loopN_mulL n (b + 1) _ (fun i h1 h2 => hu i (by omega) (by omega)) h1
    rw [loopN_succ]
    refine ⟨h3, ?_⟩
    rw [h4, h2, Finset.prod_range_succ', add_zero, mul_assoc, mul_comm (phi q1 γ (u b))]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2
    omega

end CFSG.KC.Misc.Ree2

end
