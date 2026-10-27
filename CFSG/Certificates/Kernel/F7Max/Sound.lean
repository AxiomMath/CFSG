module

public import Certificates.Data.Kernel.F7Max.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.KC.F7Max

open CFSG.KC.Misc

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

@[expose] def matC (c : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 7) :=
  !![((c : ℕ) : ZMod 7), ((c / 7 : ℕ) : ZMod 7); ((c / 49 : ℕ) : ZMod 7), ((c / 343 : ℕ) : ZMod 7)]

theorem mulC_eq (x y : ℕ) : mulC x y =
    (x % 7 * (y % 7) + x / 7 % 7 * (y / 49 % 7)) % 7 +
      7 * ((x % 7 * (y / 7 % 7) + x / 7 % 7 * (y / 343 % 7)) % 7 +
        7 * ((x / 49 % 7 * (y % 7) + x / 343 % 7 * (y / 49 % 7)) % 7 +
          7 * ((x / 49 % 7 * (y / 7 % 7) + x / 343 % 7 * (y / 343 % 7)) % 7))) := by
  simp only [mulC, letN_eq]
  rfl

theorem matC_digits {r0 r1 r2 r3 : ℕ} (h0 : r0 < 7) (h1 : r1 < 7) (h2 : r2 < 7) :
    matC (r0 + 7 * (r1 + 7 * (r2 + 7 * r3))) =
      !![((r0 : ℕ) : ZMod 7), ((r1 : ℕ) : ZMod 7); ((r2 : ℕ) : ZMod 7), ((r3 : ℕ) : ZMod 7)] := by
  have e1 : (r0 + 7 * (r1 + 7 * (r2 + 7 * r3))) / 7 = r1 + 7 * (r2 + 7 * r3) := by omega
  have e2 : (r0 + 7 * (r1 + 7 * (r2 + 7 * r3))) / 49 = r2 + 7 * r3 := by omega
  have e3 : (r0 + 7 * (r1 + 7 * (r2 + 7 * r3))) / 343 = r3 := by omega
  have c7 : ((7 : ℕ) : ZMod 7) = 0 := ZMod.natCast_self 7
  have c7' : (7 : ZMod 7) = 0 := by decide
  rw [matC, e1, e2, e3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c7, c7']

theorem matC_mulC (x y : ℕ) : matC (mulC x y) = matC x * matC y := by
  rw [mulC_eq, matC_digits (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)), matC, matC, Matrix.mul_fin_two]
  simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]

theorem det_matC (x : ℕ) :
    (matC x).det = ((x : ℕ) : ZMod 7) * ((x / 343 : ℕ) : ZMod 7) -
      ((x / 7 : ℕ) : ZMod 7) * ((x / 49 : ℕ) : ZMod 7) := by
  rw [matC, Matrix.det_fin_two_of]

theorem detNZ_iff (x : ℕ) : detNZ x = true ↔ (matC x).det ≠ 0 := by
  have h6 : (6 : ZMod 7) = -1 := by decide
  have key : (((x % 7 * (x / 343 % 7) + 6 * (x / 7 % 7 * (x / 49 % 7))) : ℕ) : ZMod 7) =
      (matC x).det := by
    rw [det_matC]
    push_cast [ZMod.natCast_mod]
    rw [h6]
    ring
  have hv : ∀ n : ℕ, (0 < n % 7) ↔ ((n : ℕ) : ZMod 7) ≠ 0 := fun n => by
    rw [Ne, ← ZMod.val_eq_zero, ZMod.val_natCast]
    omega
  rw [← key, ← hv]
  simp only [detNZ, Nat.blt_eq]
  rfl

@[expose] noncomputable def eltC (c : ℕ) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 7) :=
  if h : (matC c).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (matC c) h else 1

theorem eltC_val {c : ℕ} (h : detNZ c = true) :
    (eltC c : Matrix (Fin 2) (Fin 2) (ZMod 7)) = matC c := by
  rw [eltC, dif_pos ((detNZ_iff c).mp h)]
  rfl

theorem detNZ_mulC {x y : ℕ} (hx : detNZ x = true) (hy : detNZ y = true) :
    detNZ (mulC x y) = true := by
  rw [detNZ_iff, matC_mulC, Matrix.det_mul]
  exact mul_ne_zero ((detNZ_iff x).mp hx) ((detNZ_iff y).mp hy)

theorem eltC_mulC {x y : ℕ} (hx : detNZ x = true) (hy : detNZ y = true) :
    eltC (mulC x y) = eltC x * eltC y := by
  apply Units.ext
  rw [Units.val_mul, eltC_val (detNZ_mulC hx hy), eltC_val hx, eltC_val hy, matC_mulC]

theorem exists_code (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)) :
    ∃ c < 2401, detNZ c = true ∧ eltC c = g := by
  set M : Matrix (Fin 2) (Fin 2) (ZMod 7) := g.val with hM
  have h0 := ZMod.val_lt (M 0 0)
  have h1 := ZMod.val_lt (M 0 1)
  have h2 := ZMod.val_lt (M 1 0)
  have h3 := ZMod.val_lt (M 1 1)
  have hmat : matC ((M 0 0).val + 7 * ((M 0 1).val + 7 * ((M 1 0).val + 7 * (M 1 1).val))) = M := by
    rw [matC_digits h0 h1 h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ZMod.natCast_zmod_val]
  have hdet : (matC ((M 0 0).val + 7 * ((M 0 1).val + 7 * ((M 1 0).val + 7 * (M 1 1).val)))).det
      ≠ 0 := by
    rw [hmat]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hd := (detNZ_iff _).mpr hdet
  refine ⟨_, by omega, hd, ?_⟩
  apply Units.ext
  rw [eltC_val hd, hmat]

theorem bitB_eq (M x : ℕ) : bitB M x = M.testBit x := by
  have h : M &&& 1 <<< x = if M.testBit x = true then 2 ^ x else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases hi : x = i
    · subst hi
      cases hM : M.testBit x <;> simp [Nat.testBit_two_pow]
    · cases hM : M.testBit x <;> simp [hi, Nat.testBit_two_pow]
  have e : bitB M x = Nat.blt 0 (M &&& 1 <<< x) := rfl
  rw [e, h]
  cases hM : M.testBit x
  · rfl
  · simp only [if_true]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos x)

theorem testBit_or_shl (m y c : ℕ) :
    (m ||| 1 <<< y).testBit c = (m.testBit c || decide (y = c)) := by
  rw [Nat.testBit_lor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem testBit_maskUpTo (k c : ℕ) : (maskUpTo k).testBit c = true ↔ c < k ∧ detNZ c = true := by
  induction k with
  | zero => simp [maskUpTo]
  | succ k ih =>
    have e0 : maskUpTo (k + 1) = letN (maskUpTo k) fun m =>
        Bool.rec (motive := fun _ => ℕ) m (m ||| 1 <<< k) (detNZ k) := rfl
    have e : maskUpTo (k + 1) = Bool.rec (motive := fun _ => ℕ) (maskUpTo k)
        (maskUpTo k ||| 1 <<< k) (detNZ k) := by
      rw [e0, letN_eq]
    rw [e]
    cases hk : detNZ k
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact h
        · subst h
          rw [hk] at h2
          exact absurd h2 (by decide)
    · change (maskUpTo k ||| 1 <<< k).testBit c = true ↔ _
      rw [testBit_or_shl, Bool.or_eq_true, ih, decide_eq_true_eq]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨by omega, h2⟩
        · exact ⟨by omega, hk⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr h.symm

theorem testBit_maskG {c : ℕ} (hc : c < 2401) (hd : detNZ c = true) : maskG.testBit c = true :=
  (testBit_maskUpTo 2401 c).mpr ⟨hc, hd⟩

def Inv (S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))) (M : ℕ) : Prop :=
  ∀ c, M.testBit c = true → detNZ c = true ∧ eltC c ∈ S

theorem inv_single {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {r : ℕ}
    (hr : detNZ r = true) (hS : eltC r ∈ S) : Inv S (1 <<< r) := by
  intro c hc
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at hc
  subst hc
  exact ⟨hr, hS⟩

theorem inv_or_shl {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {m y : ℕ}
    (hm : Inv S m) (hy : detNZ y = true ∧ eltC y ∈ S) : Inv S (m ||| 1 <<< y) := by
  intro c hc
  rw [testBit_or_shl, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hc | rfl
  · exact hm c hc
  · exact hy

theorem passRUpTo_inv {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {g : ℕ}
    (hg : detNZ g = true) (hS : ∀ x ∈ S, x * eltC g ∈ S) {M : ℕ} (hM : Inv S M) :
    ∀ k, Inv S (passRUpTo g M k) := by
  intro k
  induction k with
  | zero => exact hM
  | succ k ih =>
    have e0 : passRUpTo g M (k + 1) = letN (passRUpTo g M k) fun m =>
        Bool.rec (motive := fun _ => ℕ) m (m ||| 1 <<< mulC k g) (bitB m k) := rfl
    have e : passRUpTo g M (k + 1) = Bool.rec (motive := fun _ => ℕ) (passRUpTo g M k)
        (passRUpTo g M k ||| 1 <<< mulC k g) (bitB (passRUpTo g M k) k) := by
      rw [e0, letN_eq]
    rw [e]
    cases hb : bitB (passRUpTo g M k) k
    · exact ih
    · rw [bitB_eq] at hb
      obtain ⟨hk, hkS⟩ := ih k hb
      exact inv_or_shl ih ⟨detNZ_mulC hk hg, by rw [eltC_mulC hk hg]; exact hS _ hkS⟩

theorem passLUpTo_inv {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {g : ℕ}
    (hg : detNZ g = true) (hS : ∀ x ∈ S, eltC g * x ∈ S) {M : ℕ} (hM : Inv S M) :
    ∀ k, Inv S (passLUpTo g M k) := by
  intro k
  induction k with
  | zero => exact hM
  | succ k ih =>
    have e0 : passLUpTo g M (k + 1) = letN (passLUpTo g M k) fun m =>
        Bool.rec (motive := fun _ => ℕ) m (m ||| 1 <<< mulC g k) (bitB m k) := rfl
    have e : passLUpTo g M (k + 1) = Bool.rec (motive := fun _ => ℕ) (passLUpTo g M k)
        (passLUpTo g M k ||| 1 <<< mulC g k) (bitB (passLUpTo g M k) k) := by
      rw [e0, letN_eq]
    rw [e]
    cases hb : bitB (passLUpTo g M k) k
    · exact ih
    · rw [bitB_eq] at hb
      obtain ⟨hk, hkS⟩ := ih k hb
      exact inv_or_shl ih ⟨detNZ_mulC hg hk, by rw [eltC_mulC hg hk]; exact hS _ hkS⟩

theorem roundsR_inv {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {gs : List ℕ}
    (hgs : ∀ g ∈ gs, detNZ g = true ∧ ∀ x ∈ S, x * eltC g ∈ S) {M : ℕ} (hM : Inv S M) :
    ∀ k, Inv S (roundsR gs k M) := by
  have hp : ∀ m, Inv S m → Inv S (passesR gs m) := by
    induction gs with
    | nil => exact fun m hm => hm
    | cons g gs ih =>
      intro m hm
      have e0 : passesR (g :: gs) m = letN (passR g m) (passesR gs) := rfl
      have e : passesR (g :: gs) m = passesR gs (passR g m) := by
        rw [e0, letN_eq]
      rw [e]
      obtain ⟨hg, hgS⟩ := hgs g (List.mem_cons_self ..)
      exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
        (passRUpTo_inv hg hgS hm 2401)
  intro k
  induction k with
  | zero => exact hM
  | succ k ih =>
    have e0 : roundsR gs (k + 1) M = letN (roundsR gs k M) (passesR gs) := rfl
    have e : roundsR gs (k + 1) M = passesR gs (roundsR gs k M) := by
      rw [e0, letN_eq]
    rw [e]
    exact hp _ ih

theorem roundsLR_inv {S : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))} {gs : List ℕ}
    (hgs : ∀ g ∈ gs, detNZ g = true ∧ (∀ x ∈ S, x * eltC g ∈ S) ∧ ∀ x ∈ S, eltC g * x ∈ S)
    {M : ℕ} (hM : Inv S M) : ∀ k, Inv S (roundsLR gs k M) := by
  have hp : ∀ m, Inv S m → Inv S (passesLR gs m) := by
    induction gs with
    | nil => exact fun m hm => hm
    | cons g gs ih =>
      intro m hm
      have e0 : passesLR (g :: gs) m = letN (passL g (passR g m)) (passesLR gs) := rfl
      have e : passesLR (g :: gs) m = passesLR gs (passL g (passR g m)) := by
        rw [e0, letN_eq]
      rw [e]
      obtain ⟨hg, hR, hL⟩ := hgs g (List.mem_cons_self ..)
      exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _
        (passLUpTo_inv hg hL (passRUpTo_inv hg hR hm 2401) 2401)
  intro k
  induction k with
  | zero => exact hM
  | succ k ih =>
    have e0 : roundsLR gs (k + 1) M = letN (roundsLR gs k M) (passesLR gs) := rfl
    have e : roundsLR gs (k + 1) M = passesLR gs (roundsLR gs k M) := by
      rw [e0, letN_eq]
    rw [e]
    exact hp _ ih

@[expose] noncomputable def U0 : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)) :=
  Subgroup.closure {eltC 477, eltC 2059}

theorem eltC_one : eltC 344 = 1 := by
  apply Units.ext
  rw [eltC_val (by decide +kernel), Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem zeta_mem : eltC 477 ∈ U0 := Subgroup.subset_closure (by simp)

theorem sigma_mem : eltC 2059 ∈ U0 := Subgroup.subset_closure (by simp)

theorem uGensC_mem (K : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))) (hK : U0 ≤ K) :
    ∀ g ∈ uGensC, detNZ g = true ∧ eltC g ∈ K := by
  intro g hg
  simp only [uGensC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨by decide +kernel, hK zeta_mem⟩
  · exact ⟨by decide +kernel, hK sigma_mem⟩

theorem muK_inv : Inv (U0 : Set _) muK :=
  roundsR_inv (fun g hg => ⟨(uGensC_mem U0 le_rfl g hg).1,
      fun x hx => U0.mul_mem hx (uGensC_mem U0 le_rfl g hg).2⟩)
    (inv_single (by decide +kernel) (by rw [eltC_one]; exact U0.one_mem)) 6

def dcSet (r : ℕ) : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)) :=
  {x | ∃ u ∈ U0, ∃ v ∈ U0, x = u * eltC r * v}

theorem mem_dcSet {r : ℕ} {x : Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)} :
    x ∈ dcSet r ↔ ∃ u ∈ U0, ∃ v ∈ U0, x = u * eltC r * v := Iff.rfl

theorem dcK_inv {r : ℕ} (hr : detNZ r = true) : Inv (dcSet r) (dcK r) := by
  have hmem : eltC r ∈ dcSet r :=
    mem_dcSet.mpr ⟨1, U0.one_mem, 1, U0.one_mem, by rw [one_mul, mul_one]⟩
  refine roundsLR_inv (fun g hg => ⟨(uGensC_mem U0 le_rfl g hg).1, ?_, ?_⟩)
    (inv_single hr hmem) 4
  · rintro x ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v * eltC g, U0.mul_mem hv (uGensC_mem U0 le_rfl g hg).2, by
      simp only [mul_assoc]⟩
  · rintro x ⟨u, hu, v, hv, rfl⟩
    exact ⟨eltC g * u, U0.mul_mem (uGensC_mem U0 le_rfl g hg).2 hu, v, hv, by
      simp only [mul_assoc]⟩

theorem eqB_eq {a m : ℕ} (h : eqB a m = true) : a = m := Nat.eq_of_beq_eq_true h

theorem tK_top {r : ℕ} (hr : detNZ r = true) (h : genOK r = true)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))) (hU : U0 ≤ H) (hrH : eltC r ∈ H) :
    H = ⊤ := by
  have hinv : Inv (H : Set _) (tK r) := by
    refine roundsR_inv (fun g hg => ?_)
      (inv_single (by decide +kernel) (by rw [eltC_one]; exact H.one_mem)) 4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨by decide +kernel, fun x hx => H.mul_mem hx (hU zeta_mem)⟩
    · exact ⟨by decide +kernel, fun x hx => H.mul_mem hx (hU sigma_mem)⟩
    · exact ⟨hr, fun x hx => H.mul_mem hx hrH⟩
  have heq : tK r = maskG := eqB_eq h
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨c, hc, hd, rfl⟩ := exists_code g
  have hb : (tK r).testBit c = true := by
    rw [heq]
    exact testBit_maskG hc hd
  exact (hinv c hb).2

theorem coverB_eq {a b d e m : ℕ} (h : coverB a b d e m = true) : a ||| (b ||| (d ||| e)) = m :=
  Nat.eq_of_beq_eq_true h

theorem or_of_testBit_lor {a b d e c : ℕ} (h : (a ||| (b ||| (d ||| e))).testBit c = true) :
    a.testBit c = true ∨ b.testBit c = true ∨ d.testBit c = true ∨ e.testBit c = true := by
  simpa only [Nat.testBit_lor, Bool.or_eq_true] using h

attribute [local irreducible] muK dcK tK maskG

theorem detNZ_399 : detNZ 399 = true := by decide +kernel

theorem detNZ_742 : detNZ 742 = true := by decide +kernel

theorem detNZ_1134 : detNZ 1134 = true := by decide +kernel

theorem cover_cases (hc : coverOK = true) {c : ℕ} (hc' : c < 2401) (hd : detNZ c = true) :
    muK.testBit c = true ∨ (dcK 399).testBit c = true ∨ (dcK 742).testBit c = true ∨
      (dcK 1134).testBit c = true := by
  have heq : (muK ||| (dcK 399 ||| (dcK 742 ||| dcK 1134))) = maskG := coverB_eq hc
  have hcov : (muK ||| (dcK 399 ||| (dcK 742 ||| dcK 1134))).testBit c = true :=
    Eq.mpr (congrArg (fun M => M.testBit c = true) heq) (testBit_maskG hc' hd)
  exact or_of_testBit_lor hcov

theorem top_of_dc {r : ℕ} (hr : detNZ r = true) (hg : genOK r = true)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))) (hU : U0 ≤ H) {c : ℕ}
    (hcH : eltC c ∈ H) (hb : (dcK r).testBit c = true) : H = ⊤ := by
  obtain ⟨-, hm⟩ := dcK_inv hr c hb
  obtain ⟨u, hu, v, hv, he⟩ := mem_dcSet.mp hm
  refine tK_top hr hg H hU ?_
  have hr' : eltC r = u⁻¹ * eltC c * v⁻¹ := by
    rw [he]
    group
  rw [hr']
  exact H.mul_mem (H.mul_mem (H.inv_mem (hU hu)) hcH) (H.inv_mem (hU hv))

theorem maximal_of_checks (hc : coverOK = true) (h1 : genOK 399 = true) (h2 : genOK 742 = true)
    (h3 : genOK 1134 = true) :
    ∀ H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7)), U0 ≤ H → H = U0 ∨ H = ⊤ := by
  intro H hU
  by_cases hHU : H ≤ U0
  · exact Or.inl (le_antisymm hHU hU)
  right
  obtain ⟨g, hgH, hgU⟩ := SetLike.not_le_iff_exists.mp hHU
  obtain ⟨c, hc', hd, rfl⟩ := exists_code g
  rcases cover_cases hc hc' hd with hb | hb | hb | hb
  · exact absurd (muK_inv c hb).2 hgU
  · exact top_of_dc detNZ_399 h1 H hU hgH hb
  · exact top_of_dc detNZ_742 h2 H hU hgH hb
  · exact top_of_dc detNZ_1134 h3 H hU hgH hb

end CFSG.KC.F7Max
