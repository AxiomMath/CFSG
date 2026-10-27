module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

namespace RD

section Fast

@[expose] def add3 (F u1 u2 v1 v2 : ℕ) : ℕ × ℕ :=
  ((((F ^^^ (u1 ||| u2)) &&& v1) ||| (u1 &&& (F ^^^ (v1 ||| v2)))) ||| (u2 &&& v2),
    (((F ^^^ (u1 ||| u2)) &&& v2) ||| (u2 &&& (F ^^^ (v1 ||| v2)))) ||| (u1 &&& v1))

structure IsSt (N : ℕ) (ρ : ℕ → ℤ) (a1 a2 : ℕ) : Prop where
  bit1 : ∀ l, a1.testBit l = decide (l < N ∧ ρ l = 1)
  bit2 : ∀ l, a2.testBit l = decide (l < N ∧ ρ l = 2)

theorem IsSt.congr {N : ℕ} {ρ ρ' : ℕ → ℤ} {a1 a2 : ℕ} (h : ∀ l, ρ l = ρ' l)
    (hs : IsSt N ρ a1 a2) : IsSt N ρ' a1 a2 :=
  ⟨fun l => by rw [hs.bit1, h], fun l => by rw [hs.bit2, h]⟩

theorem add3_spec {N : ℕ} {ρ σ : ℕ → ℤ} {u1 u2 v1 v2 : ℕ} (hρ : ∀ l, 0 ≤ ρ l ∧ ρ l < 3)
    (hσ : ∀ l, 0 ≤ σ l ∧ σ l < 3) (hu : IsSt N ρ u1 u2) (hv : IsSt N σ v1 v2) :
    IsSt N (fun l => (ρ l + σ l) % 3) (add3 (2 ^ N - 1) u1 u2 v1 v2).1
      (add3 (2 ^ N - 1) u1 u2 v1 v2).2 := by
  constructor <;> intro l <;>
  · simp only [add3, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      hu.bit1, hu.bit2, hv.bit1, hv.bit2]
    have h1 := hρ l
    have h2 := hσ l
    by_cases hl : l < N
    · obtain h | h | h : ρ l = 0 ∨ ρ l = 1 ∨ ρ l = 2 := by omega
      all_goals obtain h' | h' | h' : σ l = 0 ∨ σ l = 1 ∨ σ l = 2 := by omega
      all_goals simp [hl, h, h']
    · simp [hl]

@[expose] def addDig (F p1 p2 d : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  match d with
  | 0 => st
  | 1 => add3 F st.1 st.2 p1 p2
  | _ => add3 F st.1 st.2 p2 p1

theorem addDig_spec {N : ℕ} {ρ σ : ℕ → ℤ} {st : ℕ × ℕ} {p1 p2 : ℕ} (d : ℕ) (hd : d < 3)
    (hρ : ∀ l, 0 ≤ ρ l ∧ ρ l < 3) (hσ : ∀ l, 0 ≤ σ l ∧ σ l < 3) (hu : IsSt N ρ st.1 st.2)
    (hv : IsSt N σ p1 p2) :
    IsSt N (fun l => (ρ l + (d : ℤ) * σ l) % 3) (addDig (2 ^ N - 1) p1 p2 d st).1
      (addDig (2 ^ N - 1) p1 p2 d st).2 := by
  interval_cases d
  · refine IsSt.congr (fun l => ?_) hu
    have := hρ l
    simp only [Nat.cast_zero, zero_mul, add_zero]
    omega
  · refine IsSt.congr (fun l => ?_) (add3_spec hρ hσ hu hv)
    simp
  · have hv' : IsSt N (fun l => (2 * σ l) % 3) p2 p1 := by
      constructor <;> intro l
      · rw [hv.bit2]
        have := hσ l
        simp only [decide_eq_decide]
        omega
      · rw [hv.bit1]
        have := hσ l
        simp only [decide_eq_decide]
        omega
    have hσ' : ∀ l, 0 ≤ (2 * σ l) % 3 ∧ (2 * σ l) % 3 < 3 := fun l => by omega
    refine IsSt.congr (fun l => ?_) (add3_spec hρ hσ' hu hv')
    push_cast
    omega

@[expose] def colsOf : ℕ → List (List ℤ) → List (ℕ × ℕ)
  | 0, _ => []
  | m + 1, R =>
    (maskOf (R.map fun r => r.headD 0 % 3 == 1), maskOf (R.map fun r => r.headD 0 % 3 == 2)) ::
      colsOf m (R.map List.tail)

@[expose] def accum (F : ℕ) : List (ℕ × ℕ) → List ℕ → ℕ × ℕ → ℕ × ℕ
  | (p1, p2) :: cs, d :: ds, st => accum F cs ds (addDig F p1 p2 d st)
  | _, _, st => st

theorem accum_spec : ∀ (m : ℕ) (R : List (List ℤ)) (ds : List ℕ) (ρ : ℕ → ℤ) (st : ℕ × ℕ),
    (∀ r ∈ R, r.length ≤ m) → (∀ d ∈ ds, d < 3) → (∀ l, 0 ≤ ρ l ∧ ρ l < 3) →
    IsSt R.length ρ st.1 st.2 →
    IsSt R.length (fun l => (ρ l + dotR (R.getD l []) (ds.map Int.ofNat)) % 3)
      (accum (2 ^ R.length - 1) (colsOf m R) ds st).1
      (accum (2 ^ R.length - 1) (colsOf m R) ds st).2
  | 0, R, ds, ρ, st, hR, hds, hρ, hst => by
    refine IsSt.congr (fun l => ?_) hst
    have hRl : R.getD l [] = [] := by
      by_cases hl : l < R.length
      · rw [List.getD_eq_getElem _ _ hl]
        exact List.length_eq_zero_iff.1 (Nat.le_zero.1 (hR _ (List.getElem_mem hl)))
      · exact List.getD_eq_default _ _ (by omega)
    have := hρ l
    simp only [hRl, dotR]
    omega
  | m + 1, R, ds, ρ, st, hR, hds, hρ, hst => by
    cases ds with
    | nil =>
      refine IsSt.congr (fun l => ?_) (by simpa [colsOf, accum] using hst)
      have := hρ l
      simp [dotR]
      omega
    | cons d ds' =>
      have hd : d < 3 := hds d (List.mem_cons_self ..)
      have hσ : ∀ l, 0 ≤ ((R.getD l []).headD 0) % 3 ∧ ((R.getD l []).headD 0) % 3 < 3 :=
        fun l => by omega
      have hv : IsSt R.length (fun l => ((R.getD l []).headD 0) % 3)
          (maskOf (R.map fun r => r.headD 0 % 3 == 1))
          (maskOf (R.map fun r => r.headD 0 % 3 == 2)) := by
        constructor <;> intro l <;> rw [testBit_maskOf]
        · by_cases hl : l < R.length
          · rw [getD_map_lt _ R hl [] false]; simp [hl, beq_eq_decide]
          · rw [List.getD_eq_default _ _ (by simpa using hl)]; simp [hl]
        · by_cases hl : l < R.length
          · rw [getD_map_lt _ R hl [] false]; simp [hl, beq_eq_decide]
          · rw [List.getD_eq_default _ _ (by simpa using hl)]; simp [hl]
      have hstep := addDig_spec (N := R.length) d hd hρ hσ hst hv
      have hlen : (R.map List.tail).length = R.length := by simp
      have hρ' : ∀ l, 0 ≤ (ρ l + (d : ℤ) * (((R.getD l []).headD 0) % 3)) % 3 ∧
          (ρ l + (d : ℤ) * (((R.getD l []).headD 0) % 3)) % 3 < 3 := fun l => by omega
      have hR' : ∀ r ∈ R.map List.tail, r.length ≤ m := by
        intro r hr
        obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
        have := hR r' hr'
        simp only [List.length_tail]
        omega
      have ih := accum_spec m (R.map List.tail) ds' _ _ hR' (fun x hx => hds x (List.mem_cons_of_mem _ hx))
        hρ' (by rw [hlen]; exact hstep)
      rw [hlen] at ih
      simp only [colsOf, accum]
      refine IsSt.congr (fun l => ?_) ih
      by_cases hl : l < R.length
      · have hl' : l < (R.map List.tail).length := by simpa using hl
        rw [getD_map_lt List.tail R hl []]
        generalize R.getD l [] = r
        have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by omega
        cases r with
        | nil => simp [dotR]
        | cons x xs =>
          simp only [List.headD_cons, List.tail_cons, List.map_cons, dotR]
          rcases hd3 with rfl | rfl | rfl <;> simp <;> omega
      · have h1 : R.getD l [] = [] := List.getD_eq_default _ _ (by simpa using hl)
        have h2 : (R.map List.tail).getD l [] = [] := List.getD_eq_default _ _ (by simpa using hl)
        rw [h1, h2]
        have := hρ l
        simp only [dotR, List.headD_nil, List.map_cons]
        omega

end Fast

section FastKernel

variable {τ : Tag}

@[expose] def kerMaskFast (τ : Tag) (d : List ℕ) : ℕ :=
  (2 ^ τ.artifactRoots.length - 1) ^^^
    ((accum (2 ^ τ.artifactRoots.length - 1) (colsOf τ.rank τ.artifactRoots) d (0, 0)).1 |||
      (accum (2 ^ τ.artifactRoots.length - 1) (colsOf τ.rank τ.artifactRoots) d (0, 0)).2)

theorem kerMaskFast_testBit (d : List ℕ) (hd : ∀ x ∈ d, x < 3)
    (l : ℕ) :
    (kerMaskFast τ d).testBit l = decide (l < τ.artifactRoots.length ∧
      dotR (τ.artifactRoots.getD l []) (d.map Int.ofNat) % 3 = 0) := by
  have hR : ∀ r ∈ τ.artifactRoots, r.length ≤ τ.rank := fun r hr =>
    (length_of_mem_artifactRoots hr).le
  have hst := accum_spec τ.rank τ.artifactRoots d (fun _ => 0) (0, 0) hR hd
    (fun _ => ⟨le_rfl, by norm_num⟩)
    ⟨fun l => by simp, fun l => by simp⟩
  simp only [kerMaskFast, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  rw [hst.bit1 l, hst.bit2 l]
  generalize dotR (τ.artifactRoots.getD l []) (d.map Int.ofNat) = x
  by_cases hl : l < τ.artifactRoots.length
  · obtain h | h | h : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    all_goals simp [hl, h]
  · simp [hl]

theorem kerMaskFast_eq (d : List ℕ) (hd : ∀ x ∈ d, x < 3) :
    kerMaskFast τ d = kerMask τ d := by
  refine Nat.eq_of_testBit_eq fun l => ?_
  rw [kerMaskFast_testBit d hd l, kerMask, testBit_maskOf]
  by_cases hl : l < τ.artifactRoots.length
  · rw [getD_map_lt _ τ.artifactRoots hl [] false]
    simp only [hl, true_and, digDot, beq_eq_decide]
  · rw [List.getD_eq_default _ _ (by simpa using hl)]
    simp [hl]

end FastKernel

section FastRows

variable {τ : Tag}

theorem noG2_E6 : NoG2 .E6 := fun i => Or.inl (by simp [Tag.symmetrizer])

theorem noG2_E7 : NoG2 .E7 := fun i => Or.inl (by simp [Tag.symmetrizer])

theorem three_dvd_aux {p q s : ℤ} (hp : p = 2 ∨ p = 4) (hq : q = 2 ∨ q = 4)
    (hsq : s ^ 2 < p * q) (hps : p ∣ 2 * s) (hqs : q ∣ 2 * s) (h3 : (3 : ℤ) ∣ s) : s = 0 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
  · have h : s ≤ 3 ∧ -3 ≤ s := by constructor <;> nlinarith
    obtain ⟨h1, h2⟩ := h
    interval_cases s <;> omega

theorem three_dvd_iform_iff (hτ : NoG2 τ) {a b : Fin τ.rank → ℤ} (ha : IsRoot τ a)
    (hb : IsRoot τ b) : (3 : ℤ) ∣ iform a b ↔ iform a b = 0 := by
  refine ⟨fun h3 => ?_, fun h => by rw [h]; exact dvd_zero _⟩
  have hpa := iform_self_cases hτ ha
  have hpb := iform_self_cases hτ hb
  by_cases hab : a = b
  · subst hab; omega
  · by_cases hab' : a = -b
    · subst hab'
      have : iform (-b) b = -iform b b := iform_neg_left' b b
      omega
    · exact three_dvd_aux hpa hpb (iform_sq_lt ha hb hab hab') (iform_dvd_of_isRoot ha b)
        (by rw [iform_comm a b]; exact iform_dvd_of_isRoot hb a) h3

@[expose] def digs3 (w : List ℤ) : List ℕ := w.map fun x => (x % 3).toNat

theorem digs3_lt (w : List ℤ) : ∀ x ∈ digs3 w, x < 3 := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  omega

theorem dotR_map_mod3 : ∀ (u w : List ℤ), dotR u (w.map fun x => x % 3) % 3 = dotR u w % 3
  | [], w => by simp [dotR]
  | a :: as, [] => by simp [dotR]
  | a :: as, b :: bs => by
    simp only [List.map_cons, dotR]
    have ih := dotR_map_mod3 as bs
    have h1 : (a * (b % 3)) % 3 = (a * b) % 3 := by
      rw [Int.mul_emod a (b % 3) 3, Int.mul_emod a b 3, Int.emod_emod_of_dvd b (dvd_refl 3)]
    omega

theorem map_ofNat_digs3 (w : List ℤ) : (digs3 w).map Int.ofNat = w.map fun x => x % 3 := by
  simp only [digs3, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))

@[expose] def rowsFast (τ : Tag) : List ℕ :=
  (bRoots τ).map fun w => (2 ^ τ.artifactRoots.length - 1) ^^^ kerMaskFast τ (digs3 w)

theorem rowsFast_bit (hτ : NoG2 τ) {k : ℕ} (hk : k < τ.artifactRoots.length) (l : ℕ) :
    (((2 ^ τ.artifactRoots.length - 1) ^^^ kerMaskFast τ (digs3 ((bRoots τ).getD k []))).testBit l) =
      decide (l < τ.artifactRoots.length ∧ iform (rt τ k) (rt τ l) ≠ 0) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, kerMaskFast_testBit _ (digs3_lt _),
    map_ofNat_digs3, bRoots_getD hk]
  by_cases hl : l < τ.artifactRoots.length
  · have h1 : dotR (τ.artifactRoots.getD l []) (mulVecR (gramList τ) (rl τ k) |>.map fun x => x % 3) % 3 =
        iform (rt τ l) (rt τ k) % 3 := by
      rw [dotR_map_mod3, iform_rt_rt hl hk]
      rfl
    rw [h1]
    have h2 : iform (rt τ l) (rt τ k) % 3 = 0 ↔ iform (rt τ k) (rt τ l) = 0 := by
      rw [iform_comm]
      constructor
      · intro h
        exact (three_dvd_iform_iff hτ (isRoot_rt hk) (isRoot_rt hl)).1 (Int.dvd_of_emod_eq_zero h)
      · intro h; rw [h]; rfl
    simp only [hl, true_and, decide_true]
    by_cases h : iform (rt τ k) (rt τ l) = 0
    · simp [h, h2.2 h]
    · have : ¬ iform (rt τ l) (rt τ k) % 3 = 0 := fun h' => h (h2.1 h')
      simp [h, this]
  · simp [hl]

theorem rowsFast_getD (hτ : NoG2 τ) (k : ℕ) : (rowsFast τ).getD k 0 = rowOf τ k := by
  by_cases hk : k < τ.artifactRoots.length
  · have hk' : k < (bRoots τ).length := by simpa [bRoots] using hk
    rw [rowsFast, getD_map_lt _ (bRoots τ) hk' [] 0]
    refine Nat.eq_of_testBit_eq fun l => ?_
    rw [rowsFast_bit hτ hk l]
    have := rowOf_spec (τ := τ) k l
    by_cases h : (rowOf τ k).testBit l = true
    · rw [h]
      have := this.1 h
      simp [this]
    · have h' : (rowOf τ k).testBit l = false := by simpa using h
      rw [h']
      simp only [decide_eq_false_iff_not]
      intro hh
      exact h (this.2 ⟨hk, hh.1, hh.2⟩)
  · rw [List.getD_eq_default _ _ (by simpa [rowsFast, bRoots] using hk), rowOf,
      List.getD_eq_default _ _ (by simpa [rowsList] using hk)]

end FastRows

section Table

variable {τ : Tag}

@[expose] def tblOf (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + B * tblOf B rs

@[expose] def fetchT (T B k : ℕ) : ℕ := T / B ^ k % B

theorem fetchT_tblOf {B : ℕ} (hB : 0 < B) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < B) → ∀ k, fetchT (tblOf B rows) B k = rows.getD k 0
  | [], _, k => by simp [tblOf, fetchT]
  | r :: rs, h, 0 => by
    have hr : r < B := h r (List.mem_cons_self ..)
    simp only [fetchT, tblOf, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  | r :: rs, h, k + 1 => by
    have hr : r < B := h r (List.mem_cons_self ..)
    have ih := fetchT_tblOf hB rs (fun x hx => h x (List.mem_cons_of_mem _ hx)) k
    simp only [fetchT, tblOf, List.getD_cons_succ] at ih ⊢
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hr,
      zero_add]
    exact ih

@[expose] def rowFast (τ : Tag) (k : ℕ) : ℕ :=
  fetchT (tblOf (2 ^ τ.artifactRoots.length) (rowsFast τ)) (2 ^ τ.artifactRoots.length) k

theorem rowsFast_lt (hτ : NoG2 τ) : ∀ r ∈ rowsFast τ, r < 2 ^ τ.artifactRoots.length := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, kerMaskFast_testBit _ (digs3_lt _)]
  have : ¬ i < τ.artifactRoots.length := by omega
  simp [this]

theorem rowFast_eq (hτ : NoG2 τ) : rowFast τ = rowOf τ := by
  funext k
  rw [rowFast, fetchT_tblOf (by positivity) (rowsFast τ) (rowsFast_lt hτ) k, rowsFast_getD hτ k]

end Table

section Lowbit

@[expose] def lowbit (m : ℕ) : ℕ := Nat.land m (Nat.xor m (m - 1))

theorem testBit_lowbit (m i : ℕ) :
    (lowbit m).testBit i = (m.testBit i && (m.testBit i != (m - 1).testBit i)) := by
  unfold lowbit
  rw [show Nat.land m (Nat.xor m (m - 1)) = m &&& (m ^^^ (m - 1)) from rfl, Nat.testBit_and,
    Nat.testBit_xor]

theorem lowbit_two_mul_add_one (q : ℕ) : lowbit (2 * q + 1) = 1 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_lowbit]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · have h1 : (2 * q + 1) / 2 = q := by omega
    have h2 : (2 * q + 1 - 1) / 2 = q := by omega
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, h1, h2]
    simp

theorem lowbit_two_mul {q : ℕ} (hq : q ≠ 0) : lowbit (2 * q) = 2 * lowbit q := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases i with _ | i
  · rw [testBit_lowbit]
    simp [Nat.testBit_zero]
  · have h1 : (2 * q) / 2 = q := by omega
    have h2 : (2 * q - 1) / 2 = q - 1 := by omega
    have h3 : (2 * lowbit q) / 2 = lowbit q := by omega
    rw [testBit_lowbit, Nat.testBit_succ (2 * lowbit q), h3, testBit_lowbit,
      Nat.testBit_succ (2 * q), Nat.testBit_succ (2 * q - 1), h1, h2]

theorem lowbit_spec : ∀ m : ℕ, m ≠ 0 → ∃ x, lowbit m = 2 ^ x ∧ m.testBit x = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
    · have hq : q ≠ 0 := by omega
      obtain ⟨x, hx1, hx2⟩ := ih q (by omega) hq
      refine ⟨x + 1, ?_, ?_⟩
      · rw [lowbit_two_mul hq, hx1]; ring
      · rw [Nat.testBit_succ]
        simpa using hx2
    · refine ⟨0, ?_, ?_⟩
      · rw [lowbit_two_mul_add_one]; rfl
      · simp [Nat.testBit_zero]

end Lowbit

section Bfs2

@[expose] def newNbR (nb K vis : ℕ) : ℕ := Nat.xor (Nat.land nb K) (Nat.land (Nat.land nb K) vis)

theorem BInv.step' {row : ℕ → ℕ} {K b vis fr x : ℕ} (h : BInv row K b vis fr)
    (hx : fr.testBit x = true) :
    BInv row K b (vis ||| newNb (row x) K vis) ((fr ^^^ 2 ^ x) ||| newNb (row x) K vis) := by
  have hxv := h.fr_sub _ hx
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy hy' z hz hyz => ?_⟩
  · simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Bool.or_eq_true] at hy ⊢
    rcases hy with hy | hy
    · left
      have : fr.testBit y = true := by
        cases h1 : fr.testBit y
        · simp [h1] at hy
          subst hy
          simp_all
        · rfl
      exact h.fr_sub y this
    · exact Or.inr hy
  · simp only [Nat.testBit_or, Bool.or_eq_true] at hy
    rcases hy with hy | hy
    · exact h.reach y hy
    · rw [testBit_newNb] at hy
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy
      obtain ⟨⟨hrow, hK⟩, -⟩ := hy
      exact ⟨hK, Relation.ReflTransGen.tail (h.reach _ hxv).2 ⟨hK, hrow⟩⟩
  · simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Bool.or_eq_true,
      Bool.or_eq_false_iff] at hy hy' ⊢
    obtain ⟨hy1, hy2⟩ := hy'
    rcases hy with hy | hy
    · by_cases hfy : fr.testBit y = true
      · have hxy : x = y := by
          by_contra hne
          simp [hfy, hne] at hy1
        subst hxy
        by_cases hzv : vis.testBit z = true
        · exact Or.inl hzv
        · right
          rw [testBit_newNb]
          simp [hz, hyz, hzv]
      · have hfy' : fr.testBit y = false := by simpa using hfy
        exact Or.inl (h.expanded y hy hfy' z hz hyz)
    · rw [hy] at hy2
      exact absurd hy2 (by simp)

@[expose] def bfs2 (rowM : ℕ → ℕ) (K : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | f + 1, vis, fr =>
    bif Nat.beq fr 0 || Nat.beq vis K then some vis
    else bfs2 rowM K f (Nat.lor vis (newNbR (rowM (lowbit fr)) K vis))
      (Nat.lor (Nat.xor fr (lowbit fr)) (newNbR (rowM (lowbit fr)) K vis))

theorem bfs2_sound {rowM row : ℕ → ℕ} (hrow : ∀ x, rowM (2 ^ x) = row x) (K b : ℕ) :
    ∀ (f vis fr V : ℕ), BInv row K b vis fr → bfs2 rowM K f vis fr = some V →
      (∀ x, vis.testBit x = true → V.testBit x = true) ∧
      (∀ x, V.testBit x = true → K.testBit x = true ∧ Reach row K b x) ∧
      (∀ y z, V.testBit y = true → K.testBit z = true → (row y).testBit z = true →
        V.testBit z = true)
  | 0, vis, fr, V, h, hb => by simp [bfs2] at hb
  | f + 1, vis, fr, V, h, hb => by
    unfold bfs2 at hb
    by_cases hc : (Nat.beq fr 0 || Nat.beq vis K) = true
    · rw [hc] at hb
      simp only [cond_true] at hb
      obtain rfl := Option.some.inj hb
      have hexit : fr = 0 ∨ vis = K := by
        simpa [Bool.or_eq_true, Nat.beq_eq_true_eq] using hc
      exact ⟨fun _ hx => hx, h.reach, h.closed_of_exit hexit⟩
    · have hc' : (Nat.beq fr 0 || Nat.beq vis K) = false := Bool.eq_false_iff.mpr hc
      rw [hc'] at hb
      simp only [cond_false] at hb
      have hfr : fr ≠ 0 := by
        intro h0
        apply hc
        simp [h0]
      obtain ⟨x, hx1, hx2⟩ := lowbit_spec fr hfr
      rw [hx1, hrow x] at hb
      have hxor : Nat.xor fr (2 ^ x) = fr ^^^ 2 ^ x := rfl
      rw [hxor] at hb
      have hstep := h.step' hx2
      obtain ⟨h1, h2, h3⟩ := bfs2_sound hrow K b f _ _ V hstep hb
      refine ⟨fun y hy => h1 y ?_, h2, h3⟩
      simp [Nat.testBit_or, hy]

theorem isComp_of_bfs2 {rowM row : ℕ → ℕ} (hrow : ∀ x, rowM (2 ^ x) = row x) {K b f V : ℕ}
    (hb : K.testBit b = true) (h : bfs2 rowM K f (2 ^ b) (2 ^ b) = some V) : IsComp row K V b := by
  obtain ⟨h1, h2, h3⟩ := bfs2_sound hrow K b f _ _ V (BInv.init hb) h
  exact ⟨hb, h1 b Nat.testBit_two_pow_self, h2, h3⟩

end Bfs2

section Loop2

theorem beq0_false {n : ℕ} (h : n ≠ 0) : Nat.beq n 0 = false := by
  cases hb : Nat.beq n 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

@[expose] def compLoop2 (rowM : ℕ → ℕ) (K bf : ℕ) (okC : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, rem => Nat.beq rem 0
  | f + 1, rem =>
    bif Nat.beq rem 0 then true
    else
      match bfs2 rowM K bf (lowbit rem) (lowbit rem) with
      | none => false
      | some V => okC V && compLoop2 rowM K bf okC f (Nat.xor rem (Nat.land rem V))

theorem compLoop2_sound {rowM row : ℕ → ℕ} (hrow : ∀ x, rowM (2 ^ x) = row x) (K bf : ℕ)
    (okC : ℕ → Bool) :
    ∀ (f rem : ℕ), compLoop2 rowM K bf okC f rem = true →
      (∀ x, rem.testBit x = true → K.testBit x = true) →
      ∀ x, rem.testBit x = true → ∃ V b, V.testBit x = true ∧ IsComp row K V b ∧ okC V = true
  | 0, rem, h, hK, x, hx => by
    simp only [compLoop2] at h
    have h0 := Nat.eq_of_beq_eq_true h
    subst h0
    simp at hx
  | f + 1, rem, h, hK, x, hx => by
    unfold compLoop2 at h
    have hrem : rem ≠ 0 := by
      rintro rfl
      simp at hx
    have hb0 : Nat.beq rem 0 = false := beq0_false hrem
    rw [hb0] at h
    simp only [cond_false] at h
    obtain ⟨b, hb1, hb2⟩ := lowbit_spec rem hrem
    cases hbfs : bfs2 rowM K bf (lowbit rem) (lowbit rem) with
    | none => simp [hbfs] at h
    | some V =>
      rw [hbfs] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hok, hrest⟩ := h
      rw [hb1] at hbfs
      have hcomp := isComp_of_bfs2 hrow (hK _ hb2) hbfs
      by_cases hxV : V.testBit x = true
      · exact ⟨V, _, hxV, hcomp, hok⟩
      · have hxV' : V.testBit x = false := by simpa using hxV
        refine compLoop2_sound hrow K bf okC f _ hrest (fun y hy => ?_) x ?_
        · have hy' : (rem ^^^ (rem &&& V)).testBit y = true := hy
          simp only [Nat.testBit_xor, Nat.testBit_and] at hy'
          apply hK
          cases h1 : rem.testBit y <;> simp_all
        · have : (rem ^^^ (rem &&& V)).testBit x = true := by
            simp [Nat.testBit_xor, Nat.testBit_and, hx, hxV']
          exact this

@[expose] def cnt2 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, V => bif Nat.beq V 0 then 0 else cnt2 f (Nat.xor V (lowbit V)) + 1

theorem bitsSet_clear' {V x : ℕ} (hx : V.testBit x = true) :
    bitsSet (V ^^^ 2 ^ x) = bitsSet V \ {x} := by
  ext y
  simp only [bitsSet, Set.mem_setOf_eq, Nat.testBit_xor, Nat.testBit_two_pow, Set.mem_diff,
    Set.mem_singleton_iff]
  by_cases hxe : x = y
  · subst hxe
    simp [hx]
  · cases h : V.testBit y <;> simp [hxe, h, Ne.symm hxe]

theorem ncard_bitsSet_clear' {V x : ℕ} (hx : V.testBit x = true) :
    (bitsSet V).ncard = (bitsSet (V ^^^ 2 ^ x)).ncard + 1 := by
  rw [bitsSet_clear' hx]
  exact (Set.ncard_diff_singleton_add_one (show x ∈ bitsSet V from hx) (bitsSet_finite V)).symm

theorem cnt2_spec : ∀ (f V : ℕ), (cnt2 f V = f → f ≤ (bitsSet V).ncard) ∧
    (cnt2 f V < f → (bitsSet V).ncard = cnt2 f V)
  | 0, V => by simp [cnt2]
  | f + 1, V => by
    by_cases hV : V = 0
    · subst hV
      simp [cnt2, bitsSet]
    · obtain ⟨x, hx1, hx2⟩ := lowbit_spec V hV
      have hc : cnt2 (f + 1) V = cnt2 f (V ^^^ 2 ^ x) + 1 := by
        have hb : Nat.beq V 0 = false := beq0_false hV
        simp only [cnt2, hb, cond_false, hx1]
        rfl
      obtain ⟨h1, h2⟩ := cnt2_spec f (V ^^^ 2 ^ x)
      rw [hc, ncard_bitsSet_clear' hx2]
      exact ⟨fun h => by have := h1 (by omega); omega, fun h => by have := h2 (by omega); omega⟩

theorem cnt2_le : ∀ (f V : ℕ), cnt2 f V ≤ f
  | 0, V => by simp [cnt2]
  | f + 1, V => by
    unfold cnt2
    cases hb : Nat.beq V 0
    · simp only [cond_false]
      have := cnt2_le f (Nat.xor V (lowbit V))
      omega
    · simp

@[expose] def memb2 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, V => bif Nat.beq V 0 then [] else Nat.log2 (lowbit V) :: memb2 f (Nat.xor V (lowbit V))

theorem testBit_of_mem_memb2 : ∀ (f V x : ℕ), x ∈ memb2 f V → V.testBit x = true
  | 0, V, x, h => by simp [memb2] at h
  | f + 1, V, x, h => by
    unfold memb2 at h
    by_cases hV : V = 0
    · subst hV
      simp at h
    · have hb : Nat.beq V 0 = false := beq0_false hV
      rw [hb] at h
      simp only [cond_false] at h
      obtain ⟨y, hy1, hy2⟩ := lowbit_spec V hV
      rw [hy1] at h
      rcases List.mem_cons.1 h with rfl | h
      · rw [Nat.log2_two_pow]; exact hy2
      · have := testBit_of_mem_memb2 f _ x h
        have hxor : Nat.xor V (2 ^ y) = V ^^^ 2 ^ y := rfl
        rw [hxor] at this
        simp only [Nat.testBit_xor, Nat.testBit_two_pow] at this
        by_contra hne
        have hf : V.testBit x = false := by simpa using hne
        simp [hf] at this
        subst this
        exact hne hy2

@[expose] def glue2 (τ : Tag) (d : List ℕ) (V : ℕ) : Bool :=
  match memb2 6 V with
  | [] => false
  | k₁ :: ks => ks.any (fun k₂ => a2Wit τ d k₁ k₂)

@[expose] def okC2 (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) (d : List ℕ) (V : ℕ) : Bool :=
  okS (cnt2 cap V) && (cnt2 cap V != 6 || glue2 τ d V)

@[expose] def rowM2 (τ : Tag) (lb : ℕ) : ℕ :=
  tblOf (2 ^ τ.artifactRoots.length) (rowsFast τ) / lb ^ τ.artifactRoots.length %
    2 ^ τ.artifactRoots.length

theorem rowM2_pow {τ : Tag}
    (hτ : NoG2 τ) (x : ℕ) : rowM2 τ (2 ^ x) = rowOf τ x := by
  rw [← rowFast_eq hτ, rowFast, fetchT, rowM2, ← pow_mul, mul_comm, pow_mul]

@[expose] def eCheck2 (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) (d : List ℕ) : Bool :=
  compLoop2 (rowM2 τ) (kerMaskFast τ d) (τ.artifactRoots.length + 1) (okC2 τ cap okS d)
    τ.artifactRoots.length (kerMaskFast τ d)

@[expose] def rdCheck2 (τ : Tag) (cap : ℕ) (okS : ℕ → Bool) : Bool :=
  (allVecs τ.rank).all (eCheck2 τ cap okS)

end Loop2

section Extract2

variable {τ : Tag}

theorem class_extract2 (hτ : NoG2 τ) (cap : ℕ) (okS : ℕ → Bool)
    (h : rdCheck2 τ cap okS = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (ω₀ : Lˣ) (e : Fin τ.rank → ℕ) (V b k : ℕ) (hkκ : rt τ k ∈ kernelRoots (rootCharHom a)),
      ω₀ ^ 3 = 1 ∧ (∀ j, e j < 3) ∧ (∀ j, a j = ω₀ ^ e j) ∧ (ω₀ = 1 → ∀ j, e j = 0) ∧
      i = Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩ ∧ V.testBit k = true ∧
      IsComp (rowOf τ) (kerMaskFast τ (List.ofFn e)) V b ∧
      okC2 τ cap okS (List.ofFn e) V = true ∧
      Spec (rootCharHom a) (rowOf τ) (kerMaskFast τ (List.ofFn e)) := by
  obtain ⟨ω₀, e, hω₀, he3, hae, he0⟩ := exists_exps a ha
  have hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0 := by
    by_cases h1 : ω₀ = 1
    · exact Or.inr (he0 h1)
    · exact Or.inl h1
  have hdig : ∀ x ∈ List.ofFn e, x < 3 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact he3 j
  have hSpec : Spec (rootCharHom a) (rowOf τ) (kerMaskFast τ (List.ofFn e)) :=
    ⟨rowOf_spec, fun l => by
      rw [kerMaskFast_eq _ hdig]
      exact kerMask_spec a ω₀ e hω₀ hae hprim l⟩
  induction i using Quotient.inductionOn with
  | _ x =>
    obtain ⟨α, hα⟩ := x
    obtain ⟨k, hk, rfl⟩ := isRoot_iff_exists_rt.1 hα.1
    have hKk : (kerMaskFast τ (List.ofFn e)).testBit k = true := (hSpec.K_iff k).2 ⟨hk, hα⟩
    have hd := List.all_eq_true.1 h _ (ofFn_mem_allVecs _ e he3)
    obtain ⟨V, b, hkV, hV, hok⟩ := compLoop2_sound (fun x => rowM2_pow hτ x) _ _ _ _ _ hd
      (fun x hx => hx) k hKk
    exact ⟨ω₀, e, V, b, k, hα, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩

theorem size_of_check2 (hτ : NoG2 τ) (cap : ℕ) (okS : ℕ → Bool) (h : rdCheck2 τ cap okS = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ s, okS s = true ∧ ((s < cap ∧ (componentRoots (rootCharHom a) i).ncard = s) ∨
      (s = cap ∧ cap ≤ (componentRoots (rootCharHom a) i).ncard)) := by
  obtain ⟨ω₀, e, V, b, k, hkκ, -, -, -, -, rfl, hkV, hV, hok, hSpec⟩ :=
    class_extract2 hτ cap okS h a ha i
  rw [ncard_componentRoots_eq hSpec hV hkV hkκ]
  simp only [okC2, Bool.and_eq_true] at hok
  obtain ⟨hs, -⟩ := hok
  obtain ⟨h1, h2⟩ := cnt2_spec cap V
  refine ⟨cnt2 cap V, hs, ?_⟩
  by_cases hlt : cnt2 cap V < cap
  · exact Or.inl ⟨hlt, h2 hlt⟩
  · have : cnt2 cap V = cap := le_antisymm (cnt2_le cap V) (not_lt.1 hlt)
    exact Or.inr ⟨this, h1 this⟩

theorem glue_of_check2 (hτ : NoG2 τ) (cap : ℕ) (okS : ℕ → Bool) (hcap : 6 < cap)
    (h : rdCheck2 τ cap okS = true) {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (ha : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a))
    (hi : (componentRoots (rootCharHom a) i).ncard = 6) :
    ∃ γ₁ γ₂ : Fin τ.rank → ℤ, IsA2Pair τ γ₁ γ₂ ∧
      componentRoots (rootCharHom a) i = {γ₁, γ₂, γ₁ + γ₂, -γ₁, -γ₂, -(γ₁ + γ₂)} ∧
      ∀ ω : Lˣ, ω ^ 3 = 1 → ω ≠ 1 →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ j, a j = ω ^ (ε * a2Exp τ γ₁ γ₂ j) := by
  obtain ⟨ω₀, e, V, b, k, hkκ, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩ :=
    class_extract2 hτ cap okS h a ha i
  have hn := ncard_componentRoots_eq hSpec hV hkV hkκ
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a)
    (Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩)
  have himg := componentRoots_eq_image hSpec hV hkV hkκ
  rw [hn] at hi
  obtain ⟨h1, h2⟩ := cnt2_spec cap V
  have hc6 : cnt2 cap V = 6 := by
    by_cases hlt : cnt2 cap V < cap
    · rw [← h2 hlt, hi]
    · have := h1 (le_antisymm (cnt2_le cap V) (not_lt.1 hlt))
      omega
  simp only [okC2, hc6, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at hok
  have hglue := hok.2
  unfold glue2 at hglue
  rcases hm : memb2 6 V with _ | ⟨k₁, ks⟩
  · rw [hm] at hglue; simp at hglue
  · rw [hm] at hglue
    obtain ⟨k₂, hk₂ks, hwit⟩ := List.any_eq_true.1 hglue
    have hk₁V : V.testBit k₁ = true := testBit_of_mem_memb2 _ _ _ (by rw [hm]; simp)
    have hk₂V : V.testBit k₂ = true :=
      testBit_of_mem_memb2 _ _ _ (by rw [hm]; exact List.mem_cons_of_mem _ hk₂ks)
    have hk₁N := ((hSpec.K_iff k₁).1 (hV.reach k₁ hk₁V).1).1
    have hk₂N := ((hSpec.K_iff k₂).1 (hV.reach k₂ hk₂V).1).1
    obtain ⟨hA2, ε, hε, hdvd⟩ := a2Wit_spec hk₁N hk₂N e hwit
    have hmem : ∀ {x : ℕ}, V.testBit x = true → rt τ x ∈
        componentRoots (rootCharHom a) (Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨rt τ k, hkκ⟩) :=
      fun hx => by rw [himg]; exact ⟨_, hx, rfl⟩
    refine ⟨rt τ k₁, rt τ k₂, hA2, ?_, glue_algebra a ω₀ e _ ε hε hω₀ hae he0 hdvd⟩
    symm
    refine Set.eq_of_subset_of_ncard_le (a2_six_subset hΨ hA2 (hmem hk₁V) (hmem hk₂V)) ?_
      (Set.finite_of_ncard_pos (by rw [hn, hi]; norm_num))
    rw [a2_six_ncard hA2, hn, hi]

end Extract2

end RD

end CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
