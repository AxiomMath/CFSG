module

public import CFSG.Certificates.Kernel.Misc.Ree2Log

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop

@[expose] noncomputable def entM (M i j : ℕ) : ℕ := getP M (12 * i + j)

@[expose] def BdM (q1 M : ℕ) : Prop := ∀ i j, i < 12 → j < 12 → entM M i j ≤ q1

theorem entM_setP {M i b v : ℕ} (hv : v < 2 ^ 16) (hb : b < 12) {i' j' : ℕ} (hj' : j' < 12) :
    entM (setP M (12 * i + b) v) i' j' = if i' = i ∧ j' = b then v else entM M i' j' := by
  unfold entM
  rw [getP_setP hv]
  by_cases h : i' = i ∧ j' = b
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

@[expose] noncomputable def upd (q1 hf ZT lp a akj : ℕ) : ℕ :=
  if akj = q1 then a else subL q1 hf ZT a (mulL q1 lp akj)

@[expose] noncomputable def nv (q1 hf ZT ip l a akj : ℕ) : ℕ :=
  if l = q1 then a else upd q1 hf ZT (mulL q1 l ip) a akj

@[expose] noncomputable def innerF (q1 hf ZT k i lp j M : ℕ) : ℕ :=
  strictN (getP M (Nat.add (Nat.mul (nat_lit 12) k) j)) (fun akj =>
    nIf(Nat.beq akj q1, M,
      strictN (Nat.add (Nat.mul (nat_lit 12) i) j) (fun p =>
        setP M p (subL q1 hf ZT (getP M p) (mulL q1 lp akj)))))

@[expose] noncomputable def outerF (q1 hf ZT k ip i M : ℕ) : ℕ :=
  strictN (getP M (Nat.add (Nat.mul (nat_lit 12) i) k)) (fun l =>
    nIf(Nat.beq l q1, M,
      strictN (mulL q1 l ip) (fun lp =>
        loopN (Nat.sub (nat_lit 11) k) (Nat.succ k) (innerF q1 hf ZT k i lp) M)))

theorem elimStep_eq (q1 hf ZT k M : ℕ) : elimStep q1 hf ZT k M =
    loopN (11 - k) (k + 1) (outerF q1 hf ZT k (invL q1 (entM M k k))) M := by
  unfold elimStep
  rw [sN]
  have : getP M (Nat.mul 13 k) = entM M k k := by
    unfold entM
    congr 1
    change 13 * k = _
    omega
  rw [this]
  rfl

theorem innerF_eq (q1 hf ZT k i lp j M : ℕ) : innerF q1 hf ZT k i lp j M =
    if entM M k j = q1 then M else
      setP M (12 * i + j) (subL q1 hf ZT (entM M i j) (mulL q1 lp (entM M k j))) := by
  unfold innerF
  rw [sN, nIf_eq, sN, nbeq]
  simp only [decide_eq_true_eq]
  rfl

theorem outerF_eq (q1 hf ZT k ip i M : ℕ) : outerF q1 hf ZT k ip i M =
    if entM M i k = q1 then M else
      loopN (11 - k) (k + 1) (innerF q1 hf ZT k i (mulL q1 (entM M i k) ip)) M := by
  unfold outerF
  rw [sN, nIf_eq, sN, nbeq]
  simp only [decide_eq_true_eq]
  rfl

section

variable {K : Type*} [Field K] {q1 hf ZT : ℕ} {γ : K}

theorem LogEnv.upd_le (E : LogEnv q1 hf ZT γ) {lp a akj : ℕ} (hlp : lp ≤ q1) (ha : a ≤ q1)
    (hakj : akj ≤ q1) : upd q1 hf ZT lp a akj ≤ q1 := by
  unfold upd
  split_ifs
  · exact ha
  · exact (E.subL_spec ha (E.mulL_spec hlp hakj).1).1

theorem LogEnv.nv_le (E : LogEnv q1 hf ZT γ) {ip l a akj : ℕ} (hip : ip ≤ q1) (hl : l ≤ q1)
    (ha : a ≤ q1) (hakj : akj ≤ q1) : nv q1 hf ZT ip l a akj ≤ q1 := by
  unfold nv
  split_ifs
  · exact ha
  · exact E.upd_le (E.mulL_spec hl hip).1 ha hakj

theorem LogEnv.phi_nv (E : LogEnv q1 hf ZT γ) {ip l a akj : ℕ} (hip : ip ≤ q1) (hl : l ≤ q1)
    (ha : a ≤ q1) (hakj : akj ≤ q1) : phi q1 γ (nv q1 hf ZT ip l a akj) =
      phi q1 γ a - phi q1 γ l * phi q1 γ ip * phi q1 γ akj := by
  unfold nv upd
  split_ifs with h1 h2
  · rw [h1, phi_q1]; ring
  · rw [h2, phi_q1]; ring
  · obtain ⟨h3, h4⟩ := E.mulL_spec hl hip
    obtain ⟨h5, h6⟩ := E.mulL_spec h3 hakj
    rw [(E.subL_spec ha h5).2, h6, h4]

theorem LogEnv.inner_spec (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {k i lp : ℕ} (hk : k < 12)
    (hi : i < 12) (hik : i ≠ k) (hlp : lp ≤ q1) :
    ∀ (n b M : ℕ), b + n ≤ 12 → BdM q1 M →
      BdM q1 (loopN n b (innerF q1 hf ZT k i lp) M) ∧ ∀ i' j', i' < 12 → j' < 12 →
        entM (loopN n b (innerF q1 hf ZT k i lp) M) i' j' =
          if i' = i ∧ b ≤ j' ∧ j' < b + n then upd q1 hf ZT lp (entM M i j') (entM M k j')
          else entM M i' j'
  | 0, b, M, _, hM => ⟨hM, fun i' j' _ _ => by rw [loopN_zero, ite_eq_right (by omega)]⟩
  | n + 1, b, M, hb, hM => by
    rw [loopN_succ]
    set M1 := innerF q1 hf ZT k i lp b M with hM1
    have h1 : ∀ i' j', i' < 12 → j' < 12 → entM M1 i' j' =
        if i' = i ∧ j' = b then upd q1 hf ZT lp (entM M i b) (entM M k b) else entM M i' j' := by
      intro i' j' hi' hj'
      rw [hM1, innerF_eq]
      unfold upd
      by_cases hz : entM M k b = q1
      · rw [ite_eq_left hz]
        by_cases h : i' = i ∧ j' = b
        · rw [ite_eq_left h, ite_eq_left hz, h.1, h.2]
        · rw [ite_eq_right h]
      · rw [ite_eq_right hz, ite_eq_right hz, entM_setP _ (by omega) hj']
        exact (E.subL_spec (hM i b hi (by omega))
          (E.mulL_spec hlp (hM k b hk (by omega))).1).1.trans_lt (by omega)
    have hB1 : BdM q1 M1 := by
      intro i' j' hi' hj'
      rw [h1 i' j' hi' hj']
      split_ifs
      · exact E.upd_le hlp (hM i b hi (by omega)) (hM k b hk (by omega))
      · exact hM i' j' hi' hj'
    obtain ⟨h2, h3⟩ := E.inner_spec hq hk hi hik hlp n (b + 1) M1 (by omega) hB1
    refine ⟨h2, fun i' j' hi' hj' => ?_⟩
    rw [h3 i' j' hi' hj']
    by_cases c1 : i' = i ∧ b + 1 ≤ j' ∧ j' < b + 1 + n
    · rw [ite_eq_left c1, ite_eq_left (by omega), h1 i j' hi hj', h1 k j' hk hj',
        ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right c1, h1 i' j' hi' hj']
      by_cases c2 : i' = i ∧ j' = b
      · rw [ite_eq_left c2, ite_eq_left (by omega), c2.2]
      · rw [ite_eq_right c2, ite_eq_right (by omega)]

theorem LogEnv.outer_spec (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {k ip : ℕ} (hk : k < 12)
    (hip : ip ≤ q1) :
    ∀ (n b M : ℕ), k < b → b + n ≤ 12 → BdM q1 M →
      BdM q1 (loopN n b (outerF q1 hf ZT k ip) M) ∧ ∀ i' j', i' < 12 → j' < 12 →
        entM (loopN n b (outerF q1 hf ZT k ip) M) i' j' =
          if b ≤ i' ∧ i' < b + n ∧ k < j' then
            nv q1 hf ZT ip (entM M i' k) (entM M i' j') (entM M k j')
          else entM M i' j'
  | 0, b, M, _, _, hM => ⟨hM, fun i' j' _ _ => by rw [loopN_zero, ite_eq_right (by omega)]⟩
  | n + 1, b, M, hkb, hb, hM => by
    rw [loopN_succ]
    set M1 := outerF q1 hf ZT k ip b M with hM1
    have h1 : BdM q1 M1 ∧ ∀ i' j', i' < 12 → j' < 12 → entM M1 i' j' =
        if i' = b ∧ k < j' then nv q1 hf ZT ip (entM M b k) (entM M b j') (entM M k j')
        else entM M i' j' := by
      rw [hM1, outerF_eq]
      by_cases hz : entM M b k = q1
      · rw [ite_eq_left hz]
        refine ⟨hM, fun i' j' _ _ => ?_⟩
        unfold nv
        by_cases h : i' = b ∧ k < j'
        · rw [ite_eq_left h, ite_eq_left hz, h.1]
        · rw [ite_eq_right h]
      · rw [ite_eq_right hz]
        have hlp := (E.mulL_spec (hM b k (by omega) hk) hip).1
        obtain ⟨h2, h3⟩ := E.inner_spec (i := b) hq hk (by omega) (by omega) hlp (11 - k) (k + 1) M
          (by omega) hM
        refine ⟨h2, fun i' j' hi' hj' => ?_⟩
        rw [h3 i' j' hi' hj']
        unfold nv
        rw [ite_eq_right hz]
        by_cases h : i' = b ∧ k < j'
        · rw [ite_eq_left (by omega), ite_eq_left h]
        · rw [ite_eq_right (by omega), ite_eq_right h]
    obtain ⟨hB1, h1⟩ := h1
    obtain ⟨h2, h3⟩ := E.outer_spec hq hk hip n (b + 1) M1 (by omega) (by omega) hB1
    refine ⟨h2, fun i' j' hi' hj' => ?_⟩
    rw [h3 i' j' hi' hj']
    by_cases c1 : b + 1 ≤ i' ∧ i' < b + 1 + n ∧ k < j'
    · rw [ite_eq_left c1, ite_eq_left (by omega), h1 i' k hi' hk, h1 i' j' hi' hj',
        h1 k j' hk hj', ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right c1, h1 i' j' hi' hj']
      by_cases c2 : i' = b ∧ k < j'
      · rw [ite_eq_left c2, ite_eq_left (by omega), c2.1]
      · rw [ite_eq_right c2, ite_eq_right (by omega)]

theorem LogEnv.elimStep_spec (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {k M : ℕ} (hk : k < 12)
    (hM : BdM q1 M) :
    BdM q1 (elimStep q1 hf ZT k M) ∧ ∀ i j, i < 12 → j < 12 →
      entM (elimStep q1 hf ZT k M) i j = if k < i ∧ k < j then
        nv q1 hf ZT (invL q1 (entM M k k)) (entM M i k) (entM M i j) (entM M k j)
      else entM M i j := by
  rw [elimStep_eq]
  obtain ⟨h1, h2⟩ := E.outer_spec hq hk (E.invL_le _) (11 - k) (k + 1) M (by omega) (by omega) hM
  refine ⟨h1, fun i j hi hj => ?_⟩
  rw [h2 i j hi hj]
  by_cases h : k < i ∧ k < j
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

end

section

variable {K : Type*} [Field K]

@[expose] noncomputable def lowZ (k : ℕ) (A : Matrix (Fin 12) (Fin 12) K) :
    Matrix (Fin 12) (Fin 12) K :=
  Matrix.of fun i j => if (j : ℕ) < k ∧ (j : ℕ) < i then 0 else A i j

theorem lowZ_zero (A : Matrix (Fin 12) (Fin 12) K) : lowZ 0 A = A := by
  ext i j
  simp [lowZ]

theorem det_lowZ_twelve (A : Matrix (Fin 12) (Fin 12) K) : (lowZ 12 A).det = ∏ i, A i i := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [lowZ]
  · intro i j hij
    simp only [lowZ, Matrix.of_apply]
    rw [ite_eq_left ⟨j.2, hij⟩]

theorem det_lowZ_step {A B : Matrix (Fin 12) (Fin 12) K} {k : ℕ} (hk : k < 12)
    (hp : A ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0)
    (hB : ∀ i j : Fin 12, B i j = if k < (i : ℕ) ∧ k < (j : ℕ) then
      A i j - A i ⟨k, hk⟩ * (A ⟨k, hk⟩ ⟨k, hk⟩)⁻¹ * A ⟨k, hk⟩ j else A i j) :
    (lowZ (k + 1) B).det = (lowZ k A).det := by
  set kk : Fin 12 := ⟨k, hk⟩
  set C : Matrix (Fin 12) (Fin 12) K :=
    Matrix.of fun i l => if l = kk then (if k < (i : ℕ) then A i kk * (A kk kk)⁻¹ else 0) else 0
  have hL : (1 - C).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp only [C, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply]
      split_ifs with h1 h2
      · subst h1; exact absurd h2 (lt_irrefl _)
      · ring
      · ring
    · intro i j hij
      have hij' : i < j := hij
      simp only [C, Matrix.sub_apply, Matrix.of_apply]
      rw [Matrix.one_apply_ne (ne_of_lt hij')]
      split_ifs with h1 h2
      · subst h1
        have : (i : ℕ) < k := hij'
        omega
      · ring
      · ring
  have hE : lowZ (k + 1) B = (1 - C) * lowZ k A := by
    ext i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
    simp only [C, Matrix.of_apply, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ kk, ite_eq_left (Finset.mem_univ _)]
    simp only [lowZ, Matrix.of_apply, hB]
    have hkk : (kk : ℕ) = k := rfl
    by_cases hj : j = kk
    · subst hj
      rw [hkk]
      split_ifs <;> first | omega | (field_simp; ring) | ring
    · have hj' : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
      split_ifs <;> first | omega | ring
  rw [hE, Matrix.det_mul, hL, one_mul]

end

section

variable {K : Type*} [Field K] {q1 hf ZT : ℕ} {γ : K}

@[expose] noncomputable def matV (q1 : ℕ) (γ : K) (M : ℕ) : Matrix (Fin 12) (Fin 12) K :=
  Matrix.of fun i j => phi q1 γ (entM M i j)

@[expose] noncomputable def elimN (q1 hf ZT M k : ℕ) : ℕ :=
  loopN k (nat_lit 0) (fun k M => elimStep q1 hf ZT k M) M

theorem elimN_succ (q1 hf ZT M k : ℕ) :
    elimN q1 hf ZT M (k + 1) = elimStep q1 hf ZT k (elimN q1 hf ZT M k) := by
  unfold elimN
  rw [loopN_succ']
  exact congrArg (fun t => elimStep q1 hf ZT t _) (Nat.zero_add k)

theorem LogEnv.bd_elimN (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {M : ℕ} (hM : BdM q1 M) :
    ∀ k, k ≤ 12 → BdM q1 (elimN q1 hf ZT M k)
  | 0, _ => hM
  | k + 1, hk => by
    rw [elimN_succ]
    exact (E.elimStep_spec hq (by omega) (E.bd_elimN hq hM k (by omega))).1

theorem LogEnv.diag_elimN (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {M : ℕ} (hM : BdM q1 M)
    {k : ℕ} (hk : k < 12) : ∀ k', k ≤ k' → k' ≤ 12 →
      entM (elimN q1 hf ZT M k') k k = entM (elimN q1 hf ZT M k) k k
  | 0, h, _ => by rw [(by omega : k = 0)]
  | k' + 1, h, h' => by
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · rw [elimN_succ, (E.elimStep_spec hq (by omega) (E.bd_elimN hq hM k' (by omega))).2 k k hk hk,
        ite_eq_right (by omega), E.diag_elimN hq hM hk k' (by omega) (by omega)]

theorem LogEnv.det_elimN (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {M : ℕ} (hM : BdM q1 M)
    (hpiv : ∀ k, k < 12 → entM (elimN q1 hf ZT M k) k k ≠ q1) :
    ∀ k, k ≤ 12 → (lowZ k (matV q1 γ (elimN q1 hf ZT M k))).det = (matV q1 γ M).det
  | 0, _ => by rw [lowZ_zero]; rfl
  | k + 1, hk => by
    rw [← E.det_elimN hq hM hpiv k (by omega)]
    have hB := E.bd_elimN hq hM k (by omega)
    obtain ⟨-, h2⟩ := E.elimStep_spec hq (by omega : k < 12) hB
    have hp := hpiv k (by omega)
    refine det_lowZ_step (by omega) ?_ fun i j => ?_
    · exact E.phi_ne_zero (hB k k (by omega) (by omega)) hp
    · simp only [matV, Matrix.of_apply]
      rw [elimN_succ, h2 i j i.2 j.2]
      split_ifs
      · rw [E.phi_nv (E.invL_le _) (hB _ _ i.2 (by omega)) (hB _ _ i.2 j.2) (hB _ _ (by omega) j.2),
          E.invL_spec (lt_of_le_of_ne (hB k k (by omega) (by omega)) hp)]
      · rfl

theorem LogEnv.detM_spec (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {M : ℕ} (hM : BdM q1 M)
    (h : detM q1 hf ZT M ≠ q1 + 1) :
    detM q1 hf ZT M ≤ q1 ∧ phi q1 γ (detM q1 hf ZT M) = (matV q1 γ M).det := by
  have hU : loopN (nat_lit 12) (nat_lit 0) (fun k M => elimStep q1 hf ZT k M) M =
      elimN q1 hf ZT M 12 := rfl
  have hd : ∀ U k, getP U (Nat.mul (nat_lit 13) k) = entM U k k := by
    intro U k
    unfold entM
    congr 1
    change 13 * k = _
    omega
  unfold detM at h ⊢
  rw [sN, hU, nIf_eq] at h ⊢
  split_ifs at h ⊢ with hall
  · rw [allFrom_iff] at hall
    have hpiv : ∀ k, k < 12 → entM (elimN q1 hf ZT M k) k k ≠ q1 := by
      intro k hk
      have := hall k (Nat.zero_le _) (by omega)
      rw [bNot, hd] at this
      rw [← E.diag_elimN hq hM hk 12 (by omega) le_rfl]
      exact Nat.ne_of_beq_eq_false this
    have hB := E.bd_elimN hq hM 12 le_rfl
    obtain ⟨h1, h2⟩ := E.loopN_mulL (u := fun k => getP (elimN q1 hf ZT M 12) (Nat.mul 13 k)) 12 0
      0 (fun i _ hi => by rw [hd]; exact hB i i hi hi) E.pos.le
    refine ⟨h1, ?_⟩
    rw [h2, E.phi_zero, one_mul, ← E.det_elimN hq hM hpiv 12 le_rfl, det_lowZ_twelve,
      ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hd, Nat.zero_add]
    rfl
  · exact absurd rfl h

end

end CFSG.KC.Misc.Ree2

end
