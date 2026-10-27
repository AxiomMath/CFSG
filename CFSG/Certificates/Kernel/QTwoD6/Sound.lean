module

public import Certificates.Data.Kernel.QTwoD6K2
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6LinDefs

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K

@[expose] def rowF (r : V7) : Dual (ZMod 3) V7 :=
  ∑ i : Fin 7, r i • (LinearMap.proj i : V7 →ₗ[ZMod 3] ZMod 3)

@[expose] def ub : Fin 7 → V7 :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 2, 0, 1, 0], ![0, 1, 1, 2, 0, 1, 0], ![0, 1, 2, 2, 0, 1, 0],
    ![0, 1, 2, 0, 0, 1, 0], ![0, 1, 2, 0, 1, 1, 0], ![0, 1, 2, 0, 1, 1, 1]]

@[expose] def usRow : Fin 7 → V7 :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 1, 0], ![0, 1, 2, 0, 0, 1, 0], ![0, 0, 1, 2, 0, 1, 0],
    ![0, 0, 0, 1, 2, 1, 0], ![0, 0, 0, 0, 1, 0, 2], ![0, 0, 0, 0, 0, 0, 1]]

@[expose] def us (j : Fin 7) : Dual (ZMod 3) V7 := rowF (usRow j)

@[expose] def epsV : Fin 6 → V7 :=
  ![![0, 1, 1, 1, 1, 2, 2], ![0, 0, 1, 1, 1, 2, 2], ![0, 0, 0, 1, 1, 2, 2], ![0, 0, 0, 0, 1, 2, 2],
    ![0, 0, 0, 0, 0, 2, 2], ![0, 0, 0, 0, 0, 1, 2]]

@[expose] noncomputable def cd (v : Nat) (j : Fin 7) : ZMod 3 := (coordK v j.val : ZMod 3)

@[expose] noncomputable def decV (v : Nat) : V7 := ∑ j : Fin 7, cd v j • ub j

@[expose] noncomputable def decA (a : Nat) : Dual (ZMod 3) V7 := ∑ j : Fin 7, cd a j • us j

@[expose] noncomputable def decL (t : Nat) : V7 →ₗ[ZMod 3] V7 :=
  LinearMap.id - (decA (aK t)).smulRight (decV (hK t))

@[expose] noncomputable def twL (k : Nat) : V7 →ₗ[ZMod 3] V7 :=
  ((twLam k : Nat) : ZMod 3) • (us 0).smulRight e0 +
    ((twC k : Nat) : ZMod 3) • ∑ j : Fin 6, (us j.succ).smulRight (decV (sigU (j.val + 1)))

@[expose] def uSpan : Submodule (ZMod 3) V7 := Submodule.span (ZMod 3) (Set.range fun j : Fin 6 => ub j.succ)

@[expose] def MonoEps (f : V7 →ₗ[ZMod 3] V7) : Prop :=
  ∃ σ : Equiv.Perm (Fin 6), ∃ s : Fin 6 → ZMod 3, (∀ i, s i ≠ 0) ∧ ∀ i, f (epsV i) = s i • epsV (σ i)

@[expose] noncomputable def cl (L : Set (V7 ≃ₗ[ZMod 3] V7)) : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
  Subgroup.closure (Set.range simpleD6 ∪ L)

@[expose] def CodeIn (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) (t : Nat) : Prop :=
  decA (aK t) (decV (hK t)) = 2 ∧ ∃ ρ ∈ B, (ρ : V7 →ₗ[ZMod 3] V7) = decL t

@[expose] def TVFact (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) : Prop :=
  ∃ t₁ t₂, CodeIn B t₁ ∧ CodeIn B t₂ ∧ decL t₁ ≠ decL t₂ ∧
    (decV (hK t₁) = decV (hK t₂) ∨ ∃ μ : ZMod 3, decA (aK t₂) = μ • decA (aK t₁))

@[expose] def HLFact (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) : Prop :=
  ∃ t, CodeIn B t ∧ decA (aK t) e0 = 0 ∧ (decV (hK t) ∉ uSpan ∨ ¬ MonoEps (decL t))

@[expose] def PlaneFact (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) (k : Nat) : Prop :=
  ∃ ψ ∈ B, ψ e0 ∈ Submodule.span (ZMod 3) {twL k e0, twL k wb} ∧
    ψ wb ∈ Submodule.span (ZMod 3) {twL k e0, twL k wb}

namespace CovS

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem ifN_eq (c : Bool) (t e : ℕ) : ifN c t e = if c then t else e := by cases c <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem foldUpN_succ (n : ℕ) (f : ℕ → ℕ → ℕ) (i : ℕ) :
    foldUpN (n + 1) f i = f n (foldUpN n f i) := by
  change letN (foldUpN n f i) (fun s => f n s) = _
  rw [letN_eq]

def Absorb (N : ℕ) (g : ℕ → ℕ) : Prop := g (N + 1) = N + 1

def Wit (F : ℕ → ℕ) (N code : ℕ) (g : ℕ → ℕ) : Prop := ∀ s, g s ≠ N + 1 → ∃ i < N, F i = code

theorem absorb_foldUpN {N : ℕ} {f : ℕ → ℕ → ℕ} : ∀ {n : ℕ}, (∀ j < n, Absorb N (f j)) →
    Absorb N (foldUpN n f)
  | 0, _ => rfl
  | n + 1, h => by
    unfold Absorb
    rw [foldUpN_succ, absorb_foldUpN (fun j hj => h j (by omega)), h n (by omega)]

theorem wit_foldUpN {F : ℕ → ℕ} {N code : ℕ} {f : ℕ → ℕ → ℕ} {j0 : ℕ} (hw : Wit F N code (f j0)) :
    ∀ {n : ℕ}, (∀ j < n, Absorb N (f j)) → j0 < n → Wit F N code (foldUpN n f)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, hj => by
    intro s hs
    rw [foldUpN_succ] at hs
    by_cases hjn : j0 = n
    · subst hjn
      exact hw _ hs
    · refine wit_foldUpN (n := n) hw (fun j hj => h j (by omega)) (by omega) s fun h0 => hs ?_
      rw [h0]
      exact h n (by omega)

theorem covF_zero (keep : ℕ → ℕ → Bool) (F : ℕ → ℕ) (N k lo h a i : ℕ) :
    covF keep F N 0 k lo h a i = ifN (keep h a) (stepI F N (mkR h a) i) i := rfl

theorem covF_succ (keep : ℕ → ℕ → Bool) (F : ℕ → ℕ) (N n k lo h a i : ℕ) :
    covF keep F N (n + 1) k lo h a i = foldUpN (9 - lo) (fun j s => covF keep F N n (k + 1) (lo + j)
      (h ||| cbitK ((lo + j) / 3) k) (a ||| cbitK ((lo + j) % 3) k) s) i := by
  change foldUpN (Nat.sub 9 lo) (fun j s => letN (Nat.add lo j) fun p => covF keep F N n
    (Nat.succ k) p (Nat.lor h (cbitK (Nat.div p 3) k)) (Nat.lor a (cbitK (Nat.mod p 3) k)) s) i = _
  simp only [letN_eq]
  rfl

theorem absorb_stepI (F : ℕ → ℕ) (N code : ℕ) : Absorb N (stepI F N code) := by
  unfold Absorb stepI
  rw [ifN_eq, andB_eq]
  simp

theorem absorb_covF (keep : ℕ → ℕ → Bool) (F : ℕ → ℕ) (N : ℕ) :
    ∀ n k lo h a, Absorb N (covF keep F N n k lo h a)
  | 0, k, lo, h, a => by
    unfold Absorb
    rw [covF_zero, ifN_eq]
    split
    · exact absorb_stepI F N _
    · rfl
  | n + 1, k, lo, h, a => by
    unfold Absorb
    rw [covF_succ]
    exact absorb_foldUpN fun j _ => absorb_covF keep F N n _ _ _ _

@[expose] noncomputable def accC (P : ℕ → ℕ) (d : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | n + 1, k, x => accC P d n (k + 1) (x ||| cbitK (d (P k)) k)

theorem wit_covF (keep : ℕ → ℕ → Bool) (F : ℕ → ℕ) (N : ℕ) (P : ℕ → ℕ) :
    ∀ n k lo h a, (∀ m < n, lo ≤ P (k + m) ∧ P (k + m) ≤ 8) →
      (∀ m m', m ≤ m' → m' < n → P (k + m) ≤ P (k + m')) →
      keep (accC P (· / 3) n k h) (accC P (· % 3) n k a) = true →
      Wit F N (mkR (accC P (· / 3) n k h) (accC P (· % 3) n k a)) (covF keep F N n k lo h a)
  | 0, k, lo, h, a, _, _, hk => by
    intro s hs
    simp only [accC] at hk
    rw [covF_zero, hk, ifN_eq, if_pos rfl] at hs
    unfold stepI at hs
    rw [ifN_eq, andB_eq] at hs
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      exact ⟨s, hc.1, hc.2⟩
    · exact absurd rfl hs
  | n + 1, k, lo, h, a, hP, hm, hk => by
    intro s hs
    rw [covF_succ] at hs
    have h0 := hP 0 (by omega)
    simp only [Nat.add_zero] at h0
    refine wit_foldUpN (j0 := P k - lo) ?_ (fun j _ => absorb_covF keep F N n _ _ _ _)
      (by omega) s hs
    have hlo : lo + (P k - lo) = P k := by omega
    simp only [hlo]
    refine wit_covF keep F N P n (k + 1) (P k) _ _ (fun m hm' => ⟨?_, ?_⟩) (fun m m' h1 h2 => ?_)
      hk
    · have := hm 0 (m + 1) (by omega) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this
    · have := (hP (m + 1) (by omega)).2
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this
    · have := hm (m + 1) (m' + 1) (by omega) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 m, Nat.add_comm 1 m'] using this

theorem beq_decide (b k : ℕ) : (b == k) = decide (k = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact eq_comm

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem testBit_land' (a b i : ℕ) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i

theorem testBit_lor' (a b i : ℕ) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem testBit_cbitK (c k b : ℕ) :
    (cbitK c k).testBit b = ((c == 1 && b == k) || (c == 2 && b == k + 7)) := by
  unfold cbitK
  rw [ifN_eq, ifN_eq]
  by_cases h1 : c = 1
  · subst h1
    simp only [show Nat.beq 1 1 = true from rfl, if_true]
    rw [shl_eq, one_mul, Nat.testBit_two_pow]
    simp only [show ((1 : ℕ) == 1) = true from rfl, show ((1 : ℕ) == 2) = false from rfl,
      Bool.true_and, Bool.false_and, Bool.or_false]
    exact (beq_decide b k).symm
  · by_cases h2 : c = 2
    · subst h2
      simp only [show Nat.beq 2 1 = false from rfl, show Nat.beq 2 2 = true from rfl,
        Bool.false_eq_true, if_true, if_false]
      rw [shl_eq, one_mul, Nat.testBit_two_pow]
      simp only [show ((2 : ℕ) == 1) = false from rfl, show ((2 : ℕ) == 2) = true from rfl,
        Bool.true_and, Bool.false_and, Bool.false_or]
      exact (beq_decide b (k + 7)).symm
    · rw [if_neg (by simpa [Nat.beq_eq] using h1), if_neg (by simpa [Nat.beq_eq] using h2),
        Nat.zero_testBit, beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2]
      rfl

theorem bit_eq (v j : ℕ) : Nat.land (Nat.shiftRight v j) 1 = if v.testBit j then 1 else 0 := by
  change (v >>> j) &&& 1 = _
  rw [Nat.and_one_is_mod]
  have h : v.testBit j = (v >>> j).testBit 0 := by rw [Nat.testBit_shiftRight, Nat.add_zero]
  rw [h, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one (v >>> j) with h' | h' <;> simp [h']

theorem coordK_eq (v j : ℕ) :
    coordK v j = (if v.testBit j then 1 else 0) + 2 * (if v.testBit (j + 7) then 1 else 0) := by
  unfold coordK
  rw [bit_eq, bit_eq]
  rfl

@[expose] noncomputable def code7 (c : Fin 7 → ℕ) : ℕ :=
  cbitK (c 0) 0 ||| cbitK (c 1) 1 ||| cbitK (c 2) 2 ||| cbitK (c 3) 3 ||| cbitK (c 4) 4 |||
    cbitK (c 5) 5 ||| cbitK (c 6) 6

theorem code7_testBit_lo {c : Fin 7 → ℕ} (j : Fin 7) :
    (code7 c).testBit j = (c j == 1) := by
  fin_cases j <;> simp only [code7, Nat.testBit_or, testBit_cbitK] <;> simp

theorem code7_testBit_hi {c : Fin 7 → ℕ} (j : Fin 7) :
    (code7 c).testBit (j + 7) = (c j == 2) := by
  fin_cases j <;> simp only [code7, Nat.testBit_or, testBit_cbitK] <;> simp

theorem code7_testBit_big {c : Fin 7 → ℕ} {b : ℕ} (hb : 14 ≤ b) : (code7 c).testBit b = false := by
  simp only [code7, Nat.testBit_or, testBit_cbitK]
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem code7_lt (c : Fin 7 → ℕ) : code7 c < 2 ^ 14 := by
  refine Nat.lt_pow_two_of_testBit _ fun b hb => code7_testBit_big hb

theorem coordK_code7 {c : Fin 7 → ℕ} (hc : ∀ j, c j < 3) (j : Fin 7) : coordK (code7 c) j = c j := by
  rw [coordK_eq, code7_testBit_lo, code7_testBit_hi]
  have := hc j
  interval_cases (c j) <;> rfl

theorem cd_code7 {c : Fin 7 → ℕ} (hc : ∀ j, c j < 3) : cd (code7 c) = fun j => (c j : ZMod 3) := by
  funext j
  rw [cd, coordK_code7 hc]

theorem valid_code7 {c : Fin 7 → ℕ} : Nat.land (pM (code7 c)) (nM (code7 c)) = 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  change ((code7 c &&& 127) &&& ((code7 c >>> 7) &&& 127)).testBit b = (0 : ℕ).testBit b
  rw [Nat.zero_testBit, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight,
    show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 7
  · have h1 := code7_testBit_lo (c := c) ⟨b, hb⟩
    have h2 := code7_testBit_hi (c := c) ⟨b, hb⟩
    simp only at h1 h2
    rw [Nat.add_comm 7 b, h1, h2]
    by_cases h : c ⟨b, hb⟩ = 1 <;> simp [h]
  · simp [hb]

theorem hK_mkR {h a : ℕ} (hh : h < 2 ^ 14) : hK (mkR h a) = h := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  change ((h ||| a <<< 14) &&& (2 ^ 14 - 1)).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 14
  · simp [hb]
  · simp [hb, Nat.testBit_lt_two_pow (lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega)
      (by omega : 14 ≤ b)))]

theorem aK_mkR {h a : ℕ} (hh : h < 2 ^ 14) (ha : a < 2 ^ 14) : aK (mkR h a) = a := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  change (((h ||| a <<< 14) >>> 14) &&& (2 ^ 14 - 1)).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  have h1 : h.testBit (14 + b) = false := Nat.testBit_lt_two_pow
    (lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by omega)))
  by_cases hb : b < 14
  · simp [hb, h1]
  · simp [hb, h1, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega)
      (by omega : 14 ≤ b)))]

def b3 (b : Bool) : ZMod 3 := if b then 1 else 0

theorem pc7_cast (x : ℕ) : (pc7 x : ZMod 3) = ∑ j : Fin 7, b3 (x.testBit j) := by
  have e : pc7 x = Nat.land (Nat.shiftRight x 0) 1 + (Nat.land (Nat.shiftRight x 1) 1 +
      (Nat.land (Nat.shiftRight x 2) 1 + (Nat.land (Nat.shiftRight x 3) 1 +
      (Nat.land (Nat.shiftRight x 4) 1 + (Nat.land (Nat.shiftRight x 5) 1 +
      Nat.land (Nat.shiftRight x 6) 1))))) := rfl
  rw [e]
  simp only [bit_eq, Fin.sum_univ_seven, b3]
  push_cast
  norm_num <;> ring

theorem lane3 (pa na pv nv : Bool) (h : ¬(pa = true ∧ na = true)) :
    b3 (pa && pv || na && nv) + 2 * b3 (pa && nv || na && pv) =
      (b3 pa + 2 * b3 na) * (b3 pv + 2 * b3 nv) := by
  revert pa na pv nv
  decide

theorem testBit_pM (x j : ℕ) (hj : j < 7) : (pM x).testBit j = x.testBit j := by
  change (x &&& (2 ^ 7 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem testBit_nM (x j : ℕ) (hj : j < 7) : (nM x).testBit j = x.testBit (j + 7) := by
  change ((x >>> 7) &&& (2 ^ 7 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  simp [hj, Nat.add_comm]

theorem cast_coordK (v j : ℕ) :
    (coordK v j : ZMod 3) = b3 (v.testBit j) + 2 * b3 (v.testBit (j + 7)) := by
  rw [coordK_eq]
  unfold b3
  push_cast
  split_ifs <;> simp

theorem dotK_cast {a v : ℕ} (ha : Nat.land (pM a) (nM a) = 0) :
    (dotK a v : ZMod 3) = ∑ j : Fin 7, (coordK a j : ZMod 3) * (coordK v j : ZMod 3) := by
  have e : dotK a v = (pc7 (Nat.lor (Nat.land (pM a) (pM v)) (Nat.land (nM a) (nM v))) +
      2 * pc7 (Nat.lor (Nat.land (pM a) (nM v)) (Nat.land (nM a) (pM v)))) % 3 := by
    unfold dotK
    simp only [letN_eq]
    rfl
  rw [e, ZMod.natCast_mod]
  push_cast
  rw [pc7_cast, pc7_cast, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.2
  simp only [cast_coordK]
  have hna : ¬(a.testBit j = true ∧ a.testBit (j + 7) = true) := by
    intro ⟨h1, h2⟩
    have := congrArg (fun x => Nat.testBit x j) ha
    simp only [Nat.zero_testBit] at this
    rw [testBit_land', testBit_pM _ _ hj, testBit_nM _ _ hj, h1, h2] at this
    exact Bool.noConfusion this
  rw [← lane3 _ _ _ _ hna]
  simp only [testBit_lor', testBit_land', testBit_pM _ _ hj, testBit_nM _ _ hj]

theorem dotK_lt (a v : ℕ) : dotK a v < 3 := by
  unfold dotK
  simp only [letN_eq]
  exact Nat.mod_lt _ (by omega)

theorem dotK_eq {a v n : ℕ} (ha : Nat.land (pM a) (nM a) = 0) (hn : n < 3)
    (h : ∑ j : Fin 7, (coordK a j : ZMod 3) * (coordK v j : ZMod 3) = n) : dotK a v = n := by
  rw [← dotK_cast ha] at h
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (dotK_lt a v),
    Nat.mod_eq_of_lt hn] at this

def pathP (hc ac : Fin 7 → ZMod 3) (j : ℕ) : ℕ :=
  if h : j < 7 then 3 * (hc ⟨j, h⟩).val + (ac ⟨j, h⟩).val else 0

theorem accC_eq (P : ℕ → ℕ) (d : ℕ → ℕ) (x : ℕ) :
    accC P d 6 1 x = x ||| cbitK (d (P 1)) 1 ||| cbitK (d (P 2)) 2 ||| cbitK (d (P 3)) 3 |||
      cbitK (d (P 4)) 4 ||| cbitK (d (P 5)) 5 ||| cbitK (d (P 6)) 6 := rfl

theorem accC_code7 (c : Fin 7 → ZMod 3) (P : ℕ → ℕ) (d : ℕ → ℕ)
    (hP : ∀ j (hj : j < 7), j ≠ 0 → d (P j) = (c ⟨j, hj⟩).val) :
    accC P d 6 1 (cbitK (c 0).val 0) = code7 fun j => (c j).val := by
  rw [accC_eq, code7, hP 1 (by omega) (by omega), hP 2 (by omega) (by omega),
    hP 3 (by omega) (by omega), hP 4 (by omega) (by omega), hP 5 (by omega) (by omega),
    hP 6 (by omega) (by omega)]
  rfl

theorem cov_main {keep : ℕ → ℕ → Bool} {F : ℕ → ℕ} {N : ℕ} {G : ℕ → ℕ → ℕ} {n j0 : ℕ}
    {hd ha : ℕ → ℕ}
    (hG : ∀ j, G j = covF keep F N 6 1 0 (cbitK (hd j) 0) (cbitK (ha j) 0))
    (hfold : foldUpN n G 0 = N) (hj : j0 < n) (hc ac : Fin 7 → ZMod 3)
    (hh : hd j0 = (hc 0).val) (ha' : ha j0 = (ac 0).val)
    (hsort : Monotone fun k : Fin 6 => 3 * (hc k.succ).val + (ac k.succ).val)
    (hkeep : keep (code7 fun j => (hc j).val) (code7 fun j => (ac j).val) = true) :
    ∃ i < N, cd (hK (F i)) = hc ∧ cd (aK (F i)) = ac := by
  have hval : ∀ z : ZMod 3, z.val < 3 := fun z => ZMod.val_lt z
  have hdiv : ∀ j (hj : j < 7), j ≠ 0 → pathP hc ac j / 3 = (hc ⟨j, hj⟩).val := fun j hj _ => by
    simp only [pathP, hj, dif_pos]
    have := hval (ac ⟨j, hj⟩)
    omega
  have hmod : ∀ j (hj : j < 7), j ≠ 0 → pathP hc ac j % 3 = (ac ⟨j, hj⟩).val := fun j hj _ => by
    simp only [pathP, hj, dif_pos]
    have := hval (ac ⟨j, hj⟩)
    omega
  have eH := accC_code7 hc (pathP hc ac) (· / 3) hdiv
  have eA := accC_code7 ac (pathP hc ac) (· % 3) hmod
  have hw := wit_covF keep F N (pathP hc ac) 6 1 0 (cbitK (hc 0).val 0) (cbitK (ac 0).val 0)
    (fun m hm => ⟨Nat.zero_le _, by
      simp only [pathP, show 1 + m < 7 by omega, dif_pos]
      have := hval (hc ⟨1 + m, by omega⟩)
      have := hval (ac ⟨1 + m, by omega⟩)
      omega⟩)
    (fun m m' h1 h2 => by
      have := hsort (show (⟨m, by omega⟩ : Fin 6) ≤ ⟨m', by omega⟩ from h1)
      simp only [pathP, show 1 + m < 7 by omega, show 1 + m' < 7 by omega, dif_pos]
      simp only [Fin.succ_mk] at this
      simpa [Nat.add_comm 1 m, Nat.add_comm 1 m'] using this)
    (by rw [eH, eA]; exact hkeep)
  rw [eH, eA] at hw
  have hw' : Wit F N _ (foldUpN n G) := wit_foldUpN (j0 := j0)
    (by rw [hG, hh, ha']; exact hw)
    (fun j _ => by rw [hG]; exact absorb_covF keep F N 6 1 0 _ _) hj
  obtain ⟨i, hi, hFi⟩ := hw' 0 (by rw [hfold]; omega)
  refine ⟨i, hi, ?_, ?_⟩
  · rw [hFi, hK_mkR (code7_lt _), cd_code7 fun j => hval _]
    simp
  · rw [hFi, aK_mkR (code7_lt _) (code7_lt _), cd_code7 fun j => hval _]
    simp

theorem keepL_code7 {y : ℕ} {hc ac : Fin 7 → ZMod 3} (hah : ∑ j, ac j * hc j = 2)
    (hay : ∑ j, ac j * cd y j = 0) :
    keepL y (code7 fun j => (hc j).val) (code7 fun j => (ac j).val) = true := by
  have hval : ∀ z : ZMod 3, z.val < 3 := fun z => ZMod.val_lt z
  unfold keepL
  rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  constructor
  · refine dotK_eq valid_code7 (by omega) ?_
    simp only [coordK_code7 (fun j => hval _), ZMod.natCast_val, ZMod.cast_id', id]
    rw [Nat.cast_ofNat]
    exact hah
  · refine dotK_eq valid_code7 (by omega) ?_
    simp only [coordK_code7 (fun j => hval _), ZMod.natCast_val, ZMod.cast_id', id]
    rw [Nat.cast_zero]
    exact hay

def ValidC (x : ℕ) : Prop := x < 2 ^ 14 ∧ ∀ j < 7, ¬(x.testBit j = true ∧ x.testBit (j + 7) = true)

theorem testBit_pq {P Q j : ℕ} (hP : P < 2 ^ 7) :
    (Nat.lor P (Nat.shiftLeft Q 7)).testBit j = if j < 7 then P.testBit j else Q.testBit (j - 7) := by
  change (P ||| Q <<< 7).testBit j = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  split_ifs with hj
  · simp [show ¬(j ≥ 7) by omega]
  · have : P.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this, show j ≥ 7 by omega]

theorem pM_lt (x : ℕ) : pM x < 2 ^ 7 := Nat.and_lt_two_pow x (by norm_num)

theorem land_lt_left {a b n : ℕ} (h : a < 2 ^ n) : Nat.land a b < 2 ^ n := by
  change a &&& b < 2 ^ n
  rw [Nat.and_comm]
  exact Nat.and_lt_two_pow b h

theorem nM_lt (x : ℕ) : nM x < 2 ^ 7 := Nat.and_lt_two_pow _ (by norm_num)

theorem validC_pq {P Q : ℕ} (hP : P < 2 ^ 7) (hQ : Q < 2 ^ 7)
    (h : ∀ j < 7, ¬(P.testBit j = true ∧ Q.testBit j = true)) :
    ValidC (Nat.lor P (Nat.shiftLeft Q 7)) := by
  refine ⟨?_, fun j hj => ?_⟩
  · change P ||| Q <<< 7 < 2 ^ 14
    refine Nat.or_lt_two_pow (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by omega) (by omega))) ?_
    rw [Nat.shiftLeft_eq]
    calc Q * 2 ^ 7 < 2 ^ 7 * 2 ^ 7 := Nat.mul_lt_mul_of_pos_right hQ (by positivity)
      _ = 2 ^ 14 := by norm_num
  · rw [testBit_pq hP, testBit_pq hP, if_pos hj, if_neg (by omega), Nat.add_sub_cancel]
    exact h j hj

theorem testBit_xz (x j : ℕ) (hj : j < 7) :
    (Nat.xor 127 (Nat.lor (pM x) (nM x))).testBit j = !(x.testBit j || x.testBit (j + 7)) := by
  rw [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl, Nat.testBit_xor, testBit_lor',
    testBit_pM _ _ hj, testBit_nM _ _ hj,
    show (127 : ℕ) = 2 ^ 7 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem lane_add (xp xn yp yn : Bool) (hx : ¬(xp = true ∧ xn = true))
    (hy : ¬(yp = true ∧ yn = true)) :
    b3 (xp && !(yp || yn) || !(xp || xn) && yp || xn && yn) +
        2 * b3 (xn && !(yp || yn) || !(xp || xn) && yn || xp && yp) =
      (b3 xp + 2 * b3 xn) + (b3 yp + 2 * b3 yn) ∧
    ¬((xp && !(yp || yn) || !(xp || xn) && yp || xn && yn) = true ∧
      (xn && !(yp || yn) || !(xp || xn) && yn || xp && yp) = true) := by
  revert xp xn yp yn
  decide

theorem addV_spec {x y : ℕ} (hx : ValidC x) (hy : ValidC y) :
    ValidC (addV x y) ∧
      ∀ j < 7, (coordK (addV x y) j : ZMod 3) = (coordK x j : ZMod 3) + (coordK y j : ZMod 3) := by
  have e : addV x y = Nat.lor
      (Nat.lor (Nat.lor (Nat.land (pM x) (Nat.xor 127 (Nat.lor (pM y) (nM y))))
        (Nat.land (Nat.xor 127 (Nat.lor (pM x) (nM x))) (pM y))) (Nat.land (nM x) (nM y)))
      (Nat.shiftLeft (Nat.lor (Nat.lor (Nat.land (nM x) (Nat.xor 127 (Nat.lor (pM y) (nM y))))
        (Nat.land (Nat.xor 127 (Nat.lor (pM x) (nM x))) (nM y))) (Nat.land (pM x) (pM y))) 7) := by
    unfold addV
    simp only [letN_eq]
  have hP : Nat.lor (Nat.lor (Nat.land (pM x) (Nat.xor 127 (Nat.lor (pM y) (nM y))))
      (Nat.land (Nat.xor 127 (Nat.lor (pM x) (nM x))) (pM y))) (Nat.land (nM x) (nM y)) < 2 ^ 7 :=
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (land_lt_left (pM_lt x)) (Nat.and_lt_two_pow _
      (pM_lt y))) (Nat.and_lt_two_pow _ (nM_lt y))
  have hQ : Nat.lor (Nat.lor (Nat.land (nM x) (Nat.xor 127 (Nat.lor (pM y) (nM y))))
      (Nat.land (Nat.xor 127 (Nat.lor (pM x) (nM x))) (nM y))) (Nat.land (pM x) (pM y)) < 2 ^ 7 :=
    Nat.or_lt_two_pow (Nat.or_lt_two_pow (land_lt_left (nM_lt x)) (Nat.and_lt_two_pow _
      (nM_lt y))) (Nat.and_lt_two_pow _ (pM_lt y))
  rw [e]
  refine ⟨validC_pq hP hQ fun j hj => ?_, fun j hj => ?_⟩
  · simp only [testBit_lor', testBit_land', testBit_xz _ _ hj, testBit_pM _ _ hj, testBit_nM _ _ hj]
    exact (lane_add _ _ _ _ (hx.2 j hj) (hy.2 j hj)).2
  · rw [cast_coordK, cast_coordK, cast_coordK, testBit_pq hP, testBit_pq hP, if_pos hj,
      if_neg (by omega), Nat.add_sub_cancel]
    simp only [testBit_lor', testBit_land', testBit_xz _ _ hj, testBit_pM _ _ hj, testBit_nM _ _ hj]
    exact (lane_add _ _ _ _ (hx.2 j hj) (hy.2 j hj)).1

theorem negV_spec {x : ℕ} (hx : ValidC x) :
    ValidC (negV x) ∧ ∀ j < 7, (coordK (negV x) j : ZMod 3) = -(coordK x j : ZMod 3) := by
  have e : negV x = Nat.lor (nM x) (Nat.shiftLeft (pM x) 7) := rfl
  rw [e]
  refine ⟨validC_pq (nM_lt x) (pM_lt x) fun j hj => ?_, fun j hj => ?_⟩
  · rw [testBit_pM _ _ hj, testBit_nM _ _ hj]
    exact fun h => hx.2 j hj ⟨h.2, h.1⟩
  · rw [cast_coordK, cast_coordK, testBit_pq (nM_lt x), testBit_pq (nM_lt x), if_pos hj,
      if_neg (by omega), Nat.add_sub_cancel, testBit_pM _ _ hj, testBit_nM _ _ hj]
    have := hx.2 j hj
    revert this
    cases x.testBit j <;> cases x.testBit (j + 7) <;> decide

theorem validC_land {x : ℕ} (hx : ValidC x) : Nat.land (pM x) (nM x) = 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_land', Nat.zero_testBit]
  by_cases hb : b < 7
  · rw [testBit_pM _ _ hb, testBit_nM _ _ hb]
    have := hx.2 b hb
    revert this
    cases x.testBit b <;> cases x.testBit (b + 7) <;> decide
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (pM_lt x)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl

theorem axpy_spec {v w c : ℕ} (hv : ValidC v) (hw : ValidC w) (hc : c < 3) :
    ValidC (axpy v c w) ∧ ∀ j < 7,
      (coordK (axpy v c w) j : ZMod 3) = coordK v j - (c : ZMod 3) * coordK w j := by
  unfold axpy
  rw [ifN_eq, ifN_eq]
  interval_cases c
  · simp only [show Nat.beq 0 0 = true from rfl, if_true]
    exact ⟨hv, fun j _ => by simp⟩
  · simp only [show Nat.beq 1 0 = false from rfl, show Nat.beq 1 1 = true from rfl,
      Bool.false_eq_true, if_true, if_false]
    obtain ⟨hn, hnc⟩ := negV_spec hw
    obtain ⟨ha, hac⟩ := addV_spec hv hn
    refine ⟨ha, fun j hj => ?_⟩
    rw [hac j hj, hnc j hj]
    simp only [Nat.cast_one, one_mul]
    ring
  · simp only [show Nat.beq 2 0 = false from rfl, show Nat.beq 2 1 = false from rfl,
      Bool.false_eq_true, if_false]
    obtain ⟨ha, hac⟩ := addV_spec hv hw
    refine ⟨ha, fun j hj => ?_⟩
    rw [hac j hj]
    have h3 : (3 : ZMod 3) = 0 := rfl
    push_cast
    linear_combination (coordK w j : ZMod 3) * h3

theorem us_ub (i j : Fin 7) : us i (ub j) = if i = j then 1 else 0 := by
  have key : ∀ i j : Fin 7, (∑ k : Fin 7, usRow i k * ub j k) = if i = j then 1 else 0 := by
    decide
  rw [← key i j]
  simp [us, rowF, LinearMap.sum_apply]

theorem decA_decV (a v : ℕ) : decA a (decV v) = ∑ j : Fin 7, cd a j * cd v j := by
  simp only [decA, decV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, us_ub,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm]

theorem dotK_decA {a v : ℕ} (ha : ValidC a) : (dotK a v : ZMod 3) = decA a (decV v) := by
  rw [dotK_cast (validC_land ha), decA_decV]
  rfl

theorem decV_axpy {v w c : ℕ} (hv : ValidC v) (hw : ValidC w) (hc : c < 3) :
    decV (axpy v c w) = decV v - (c : ZMod 3) • decV w := by
  have h := (axpy_spec hv hw hc).2
  simp only [decV, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cd, cd, cd, h j j.2]

theorem decA_axpy {v w c : ℕ} (hv : ValidC v) (hw : ValidC w) (hc : c < 3) :
    decA (axpy v c w) = decA v - (c : ZMod 3) • decA w := by
  have h := (axpy_spec hv hw hc).2
  simp only [decA, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cd, cd, cd, h j j.2]
  exact LinearMap.ext fun x => by simp [sub_mul]

theorem decV_negV {v : ℕ} (hv : ValidC v) : decV (negV v) = -decV v := by
  have h := (negV_spec hv).2
  simp only [decV, ← Finset.sum_neg_distrib, ← neg_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cd, cd, h j j.2]

theorem decA_negV {v : ℕ} (hv : ValidC v) : decA (negV v) = -decA v := by
  have h := (negV_spec hv).2
  simp only [decA, ← Finset.sum_neg_distrib, ← neg_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cd, cd, h j j.2]
  exact LinearMap.ext fun x => by simp

theorem refl_conj {α β : Dual (ZMod 3) V7} {η θ : V7} (hα : α η = 2) :
    (LinearMap.id - α.smulRight η) ∘ₗ (LinearMap.id - β.smulRight θ) ∘ₗ
        (LinearMap.id - α.smulRight η) =
      LinearMap.id - (β - β η • α).smulRight (θ - α θ • η) := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, map_sub, map_smul, hα, smul_eq_mul, LinearMap.smul_apply]
  module

def ReflC (t : ℕ) : Prop :=
  ValidC (hK t) ∧ ValidC (aK t) ∧ decA (aK t) (decV (hK t)) = 2

theorem hK_mkR' {h a : ℕ} (hh : ValidC h) : hK (mkR h a) = h := hK_mkR hh.1

theorem aK_mkR' {h a : ℕ} (hh : ValidC h) (ha : ValidC a) : aK (mkR h a) = a := aK_mkR hh.1 ha.1

theorem normR_spec {t : ℕ} (ht : ReflC t) : ReflC (normR t) ∧ decL (normR t) = decL t := by
  unfold normR
  rw [letN_eq, ifN_eq]
  split
  · exact ⟨ht, rfl⟩
  · obtain ⟨hh, ha, hp⟩ := ht
    obtain ⟨hh', -⟩ := negV_spec hh
    obtain ⟨ha', -⟩ := negV_spec ha
    refine ⟨⟨by rw [hK_mkR' hh']; exact hh', by rw [aK_mkR' hh' ha']; exact ha', ?_⟩, ?_⟩
    · rw [hK_mkR' hh', aK_mkR' hh' ha', decA_negV ha, decV_negV hh, LinearMap.neg_apply, map_neg,
        neg_neg, hp]
    · unfold decL
      rw [hK_mkR' hh', aK_mkR' hh' ha', decA_negV ha, decV_negV hh]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        LinearMap.neg_apply, neg_smul, smul_neg, neg_neg]

theorem conjK_spec {s t : ℕ} (hs : ReflC s) (ht : ReflC t) :
    ReflC (conjK s t) ∧ decL (conjK s t) = decL s ∘ₗ decL t ∘ₗ decL s := by
  obtain ⟨hsh, hsa, hsp⟩ := hs
  obtain ⟨hth, hta, htp⟩ := ht
  have e : conjK s t = normR (mkR (axpy (hK t) (dotK (aK s) (hK t)) (hK s))
      (axpy (aK t) (dotK (aK t) (hK s)) (aK s))) := by
    unfold conjK
    simp only [letN_eq]
  have hh := axpy_spec hth hsh (dotK_lt (aK s) (hK t))
  have ha := axpy_spec hta hsa (dotK_lt (aK t) (hK s))
  have hdh := decV_axpy hth hsh (dotK_lt (aK s) (hK t))
  have hda := decA_axpy hta hsa (dotK_lt (aK t) (hK s))
  rw [dotK_decA hsa] at hdh
  rw [dotK_decA hta] at hda
  have hR : ReflC (mkR (axpy (hK t) (dotK (aK s) (hK t)) (hK s))
      (axpy (aK t) (dotK (aK t) (hK s)) (aK s))) := by
    refine ⟨by rw [hK_mkR' hh.1]; exact hh.1, by rw [aK_mkR' hh.1 ha.1]; exact ha.1, ?_⟩
    rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1, hdh, hda]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hsp, htp]
    ring
  obtain ⟨hn, hnl⟩ := normR_spec hR
  rw [e]
  refine ⟨hn, ?_⟩
  rw [hnl]
  unfold decL
  rw [refl_conj hsp, hK_mkR' hh.1, aK_mkR' hh.1 ha.1, hdh, hda]

def InB (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) (t : ℕ) : Prop :=
  ReflC t ∧ ∃ ρ ∈ B, (ρ : V7 →ₗ[ZMod 3] V7) = decL t

theorem inB_conjK {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {s t : ℕ} (hs : InB B s) (ht : InB B t) :
    InB B (conjK s t) := by
  obtain ⟨hsR, ρs, hρs, es⟩ := hs
  obtain ⟨htR, ρt, hρt, et⟩ := ht
  obtain ⟨hR, hL⟩ := conjK_spec hsR htR
  refine ⟨hR, ρs * ρt * ρs, B.mul_mem (B.mul_mem hρs hρt) hρs, ?_⟩
  rw [hL, ← es, ← et]
  rfl

theorem validC_of_validV {x : ℕ} (h : validV x = true) : ValidC x := by
  unfold validV at h
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  refine ⟨h.1, fun j hj hb => ?_⟩
  have := congrArg (fun y => Nat.testBit y j) h.2
  simp only [testBit_land', testBit_pM _ _ hj, testBit_nM _ _ hj, hb.1, hb.2, Nat.zero_testBit,
    Bool.and_self] at this
  exact Bool.noConfusion this

theorem reflection_coe {f : Dual (ZMod 3) V7} {x : V7} (h : f x = 2) :
    ((Module.reflection h : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) =
      LinearMap.id - f.smulRight x := by
  refine LinearMap.ext fun v => ?_
  simp [Module.reflection_apply]

theorem decA_single (a : ℕ) (k : Fin 7) :
    decA a (Pi.single k 1) = ∑ j : Fin 7, cd a j * usRow j k := by
  simp [decA, us, rowF, LinearMap.sum_apply, Pi.single_apply]

theorem avec_single (i : Fin 6) (k : Fin 7) :
    avec i (Pi.single k 1) = ∑ m : Fin 6, (cartanD6 m i : ZMod 3) * (if k = m.succ then 1 else 0) := by
  simp [avec, LinearMap.sum_apply, Pi.single_apply, eq_comm]

theorem genU_spec (r : ℕ) (i : Fin 6) : ReflC (genU r i) ∧
    decL (genU r i) = ((simpleD6 i : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7) := by
  have e : genU r i = genU 0 i := by
    fin_cases i <;> rfl
  rw [e]
  have hv : ∀ i : Fin 6, ValidC (hK (genU 0 i)) ∧ ValidC (aK (genU 0 i)) := by
    unfold ValidC
    decide +kernel
  have hrank : ∀ (i : Fin 6) (k k' : Fin 7),
      (∑ j : Fin 7, cd (aK (genU 0 i)) j * usRow j k') * (∑ x : Fin 7, cd (hK (genU 0 i)) x * ub x k) =
        (∑ m : Fin 6, (cartanD6 m i : ZMod 3) * (if k' = m.succ then 1 else 0)) * hvec i k := by
    decide +kernel
  have hp : ∀ i : Fin 6, ∑ j : Fin 7, cd (aK (genU 0 i)) j * cd (hK (genU 0 i)) j = 2 := by
    decide +kernel
  refine ⟨⟨(hv i).1, (hv i).2, by rw [decA_decV]; exact hp i⟩, ?_⟩
  unfold decL simpleD6
  rw [reflection_coe]
  refine congrArg (LinearMap.id - ·) ?_
  refine LinearMap.pi_ext' fun k' => LinearMap.ext_ring (funext fun k => ?_)
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul]
  have hs : (LinearMap.single (ZMod 3) (fun _ : Fin 7 => ZMod 3) k') 1 = Pi.single k' 1 := rfl
  rw [hs, decA_single, avec_single, ← hrank i k k']
  simp only [decV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

noncomputable def normT (P N : ℕ) : Bool := Nat.beq (Nat.land N (lowbit (Nat.lor P N))) 0

theorem normT_neg : ∀ P < 128, ∀ N < 128, Nat.land P N = 0 → normT P N = false →
    normT N P = true := by
  unfold normT lowbit
  decide +kernel

theorem normT_both' : ∀ P < 128, ∀ N < 128,
    (Nat.land P N == 0 && normT P N && normT N P) = true → (P == 0 && N == 0) = true := by
  unfold normT lowbit
  decide +kernel

theorem normT_both {P N : ℕ} (hP : P < 128) (hN : N < 128) (h0 : Nat.land P N = 0)
    (h1 : normT P N = true) (h2 : normT N P = true) : P = 0 ∧ N = 0 := by
  have := normT_both' P hP N hN (by rw [h0, h1, h2]; rfl)
  simpa using this

theorem smul_eq_zero3 {c : ZMod 3} {x : V7} (h : c • x = 0) : c = 0 ∨ x = 0 := by
  by_cases hc : c = 0
  · exact Or.inl hc
  · have hcc : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
    refine Or.inr ?_
    calc x = (c * c) • x := by rw [hcc c hc, one_smul]
      _ = 0 := by rw [mul_smul, h, smul_zero]

theorem us_decV (v : ℕ) (j : Fin 7) : us j (decV v) = cd v j := by
  simp only [decV, map_sum, map_smul, us_ub, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lane_bits {x : ℕ} (hx : ValidC x) (j : ℕ) (hj : j < 7) :
    x.testBit j = decide (cd x ⟨j, hj⟩ = 1) ∧ x.testBit (j + 7) = decide (cd x ⟨j, hj⟩ = 2) := by
  have h := hx.2 j hj
  have e : cd x ⟨j, hj⟩ = b3 (x.testBit j) + 2 * b3 (x.testBit (j + 7)) := cast_coordK x j
  rw [e]
  revert h
  cases x.testBit j <;> cases x.testBit (j + 7) <;> decide

theorem eq_of_cd {x y : ℕ} (hx : ValidC x) (hy : ValidC y) (h : ∀ j, cd x j = cd y j) : x = y := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < 7
  · rw [(lane_bits hx b hb).1, (lane_bits hy b hb).1, h]
  by_cases hb' : b < 14
  · have := (lane_bits hx (b - 7) (by omega)).2
    rw [show b - 7 + 7 = b by omega] at this
    rw [this]
    have := (lane_bits hy (b - 7) (by omega)).2
    rw [show b - 7 + 7 = b by omega] at this
    rw [this, h]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx.1 (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy.1 (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem masks_of_neg {x y : ℕ} (hx : ValidC x) (hy : ValidC y) (h : ∀ j, cd y j = -cd x j) :
    pM y = nM x ∧ nM y = pM x := by
  have key : ∀ j (hj : j < 7), y.testBit j = x.testBit (j + 7) ∧ y.testBit (j + 7) = x.testBit j := by
    intro j hj
    rw [(lane_bits hx j hj).1, (lane_bits hx j hj).2, (lane_bits hy j hj).1, (lane_bits hy j hj).2,
      h]
    generalize cd x ⟨j, hj⟩ = z
    revert z
    decide
  constructor <;> refine Nat.eq_of_testBit_eq fun b => ?_
  · by_cases hb : b < 7
    · rw [testBit_pM _ _ hb, testBit_nM _ _ hb, (key b hb).1]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (pM_lt y) (Nat.pow_le_pow_right (by omega)
        (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (nM_lt x) (Nat.pow_le_pow_right
        (by omega) (by omega)))]
  · by_cases hb : b < 7
    · rw [testBit_pM _ _ hb, testBit_nM _ _ hb, (key b hb).2]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (nM_lt y) (Nat.pow_le_pow_right (by omega)
        (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (pM_lt x) (Nat.pow_le_pow_right
        (by omega) (by omega)))]

def ReflN (t : ℕ) : Prop :=
  ReflC t ∧ normT (pM (hK t)) (nM (hK t)) = true ∧ t = mkR (hK t) (aK t)

theorem pM_negV (x : ℕ) : pM (negV x) = nM x := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < 7
  · rw [testBit_pM _ _ hb]
    change (Nat.lor (nM x) (Nat.shiftLeft (pM x) 7)).testBit b = _
    rw [testBit_pq (nM_lt x), if_pos hb]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (pM_lt _) (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (nM_lt x) (Nat.pow_le_pow_right
      (by omega) (by omega)))]

theorem nM_negV (x : ℕ) : nM (negV x) = pM x := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < 7
  · rw [testBit_nM _ _ hb]
    change (Nat.lor (nM x) (Nat.shiftLeft (pM x) 7)).testBit (b + 7) = _
    rw [testBit_pq (nM_lt x), if_neg (by omega), Nat.add_sub_cancel]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (nM_lt _) (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le (pM_lt x) (Nat.pow_le_pow_right
      (by omega) (by omega)))]

theorem normR_normal {t : ℕ} (ht : ReflC t) (hm : t = mkR (hK t) (aK t)) : ReflN (normR t) := by
  obtain ⟨hR, -⟩ := normR_spec ht
  refine ⟨hR, ?_⟩
  unfold normR
  rw [letN_eq, ifN_eq]
  split
  · rename_i hc
    exact ⟨hc, hm⟩
  · rename_i hc
    obtain ⟨hh', -⟩ := negV_spec ht.1
    obtain ⟨ha', -⟩ := negV_spec ht.2.1
    rw [hK_mkR' hh', aK_mkR' hh' ha', pM_negV, nM_negV]
    exact ⟨normT_neg _ (pM_lt _) _ (nM_lt _) (validC_land ht.1) (Bool.eq_false_iff.mpr hc), rfl⟩

theorem mkR_hK_aK {t : ℕ} (ht : t < 2 ^ 28) : t = mkR (hK t) (aK t) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  change _ = ((t &&& (2 ^ 14 - 1)) ||| (((t >>> 14) &&& (2 ^ 14 - 1)) <<< 14)).testBit b
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 14
  · simp [hb]
  · by_cases hb' : b < 28
    · simp [hb, show b - 14 < 14 by omega, show 14 + (b - 14) = b by omega, show b ≥ 14 by omega]
    · simp [hb, show ¬(b - 14 < 14) by omega, Nat.testBit_lt_two_pow (lt_of_lt_of_le ht
        (Nat.pow_le_pow_right (by omega) (by omega : 28 ≤ b)))]

theorem decL_ne {t₁ t₂ : ℕ} (h₁ : ReflN t₁) (h₂ : ReflN t₂) (hne : t₁ ≠ t₂) :
    decL t₁ ≠ decL t₂ := by
  intro heq
  obtain ⟨⟨hh₁, ha₁, hp₁⟩, hn₁, hm₁⟩ := h₁
  obtain ⟨⟨hh₂, ha₂, hp₂⟩, hn₂, hm₂⟩ := h₂
  set H₁ := decV (hK t₁)
  set H₂ := decV (hK t₂)
  set A₁ := decA (aK t₁)
  set A₂ := decA (aK t₂)
  have hrank : ∀ v, A₁ v • H₁ = A₂ v • H₂ := fun v => by
    have := congrArg (fun f : V7 →ₗ[ZMod 3] V7 => v - f v) heq
    simpa [decL] using this
  have hH₁ : H₁ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hp₁
    exact absurd hp₁ (by decide)
  have key := hrank H₁
  rw [hp₁] at key
  have hz : A₂ H₁ ≠ 0 := fun h0 => by
    rw [h0, zero_smul] at key
    rcases smul_eq_zero3 key with h | h
    · exact absurd h (by decide)
    · exact hH₁ h
  have hc : A₂ H₁ = 1 ∨ A₂ H₁ = 2 := by
    have : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = 2 := by decide
    exact this _ hz
  rcases hc with hc | hc
  ·
    rw [hc, one_smul] at key
    have hcd : ∀ j, cd (hK t₂) j = -cd (hK t₁) j := fun j => by
      rw [← us_decV, ← us_decV]
      change us j H₂ = -(us j H₁)
      rw [← key, map_smul, smul_eq_mul]
      have : (2 : ZMod 3) = -1 := by decide
      rw [this, neg_one_mul]
    obtain ⟨e1, e2⟩ := masks_of_neg hh₁ hh₂ hcd
    rw [e1, e2] at hn₂
    obtain ⟨z1, z2⟩ := normT_both (pM_lt _) (nM_lt _) (validC_land hh₁) hn₁ hn₂
    apply hH₁
    have hz : ∀ j, cd (hK t₁) j = 0 := fun j => by
      have := lane_bits hh₁ j j.2
      have b1 : (hK t₁).testBit j = false := by
        rw [← testBit_pM _ _ j.2, z1, Nat.zero_testBit]
      have b2 : (hK t₁).testBit (j + 7) = false := by
        rw [← testBit_nM _ _ j.2, z2, Nat.zero_testBit]
      rw [cd, cast_coordK, b1, b2]
      rfl
    simp only [H₁, decV, hz, zero_smul, Finset.sum_const_zero]
  ·
    rw [hc] at key
    have hH : H₂ = H₁ := by
      have h2 : (2 : ZMod 3) * 2 = 1 := by decide
      calc H₂ = ((2 : ZMod 3) * 2) • H₂ := by rw [h2, one_smul]
        _ = H₁ := by rw [mul_smul, ← key, ← mul_smul, h2, one_smul]
    have hA : A₁ = A₂ := LinearMap.ext fun v => by
      have := hrank v
      rw [hH, ← sub_eq_zero, ← sub_smul] at this
      rcases smul_eq_zero3 this with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hH₁
    have ech : hK t₁ = hK t₂ := eq_of_cd hh₁ hh₂ fun j => by
      rw [← us_decV, ← us_decV]
      exact congrArg (us j) hH.symm
    have eca : aK t₁ = aK t₂ := eq_of_cd ha₁ ha₂ fun j => by
      have := congrArg (fun f : Dual (ZMod 3) V7 => f (ub j)) hA
      simpa [A₁, A₂, decA, us_ub] using this
    exact hne (by rw [hm₁, hm₂, ech, eca])

theorem ifB_eq (c t e : Bool) : ifB c t e = if c then t else e := by cases c <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem conjK_normal {s t : ℕ} (hs : ReflC s) (ht : ReflC t) : ReflN (conjK s t) := by
  obtain ⟨hsh, hsa, hsp⟩ := hs
  obtain ⟨hth, hta, htp⟩ := ht
  have e : conjK s t = normR (mkR (axpy (hK t) (dotK (aK s) (hK t)) (hK s))
      (axpy (aK t) (dotK (aK t) (hK s)) (aK s))) := by
    unfold conjK
    simp only [letN_eq]
  have hh := axpy_spec hth hsh (dotK_lt (aK s) (hK t))
  have ha := axpy_spec hta hsa (dotK_lt (aK t) (hK s))
  have hR : ReflC (mkR (axpy (hK t) (dotK (aK s) (hK t)) (hK s))
      (axpy (aK t) (dotK (aK t) (hK s)) (aK s))) := by
    refine ⟨by rw [hK_mkR' hh.1]; exact hh.1, by rw [aK_mkR' hh.1 ha.1]; exact ha.1, ?_⟩
    rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1, decV_axpy hth hsh (dotK_lt _ _),
      decA_axpy hta hsa (dotK_lt _ _), dotK_decA hsa, dotK_decA hta]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul, hsp,
      htp]
    ring
  rw [e]
  exact normR_normal hR (by rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1])

def InN (B : Subgroup (V7 ≃ₗ[ZMod 3] V7)) (t : ℕ) : Prop :=
  ReflN t ∧ ∃ ρ ∈ B, (ρ : V7 →ₗ[ZMod 3] V7) = decL t

theorem inN_wordF {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {r : ℕ} (hg : ∀ i, InB B (genU r i)) :
    ∀ fuel t w, InN B t → InN B (wordF r fuel t w)
  | 0, t, _, ht => ht
  | fuel + 1, t, w, ht => by
    change InN B (ifN (Nat.beq w 0) t (letN (conjK (genU r (Nat.sub (Nat.mod w 8) 1)) t)
      fun t' => wordF r fuel t' (Nat.div w 8)))
    rw [ifN_eq, letN_eq]
    split
    · exact ht
    · refine inN_wordF hg fuel _ _ ⟨conjK_normal (hg _).1 ht.1.1, ?_⟩
      exact (inB_conjK (hg _) ⟨ht.1.1, ht.2⟩).2

theorem memL_mem {i : ℕ} : ∀ {S : List ℕ}, memL i S = true → i ∈ S
  | [], h => Bool.noConfusion h
  | j :: S, h => by
    change orB (Nat.beq i j) (memL i S) = true at h
    rw [orB_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.beq_eq] at h
      rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memL_mem h)

theorem normV_cases (v : ℕ) : normV v = v ∨ normV v = negV v := by
  unfold normV
  rw [ifN_eq]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tvFact_of_tvK {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {t₁ t₂ : ℕ} (h₁ : InN B t₁)
    (h₂ : InN B t₂) (h : tvK t₁ t₂ = true) : TVFact B := by
  unfold tvK at h
  rw [andB_eq, notB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨hne, hc⟩ := h
  have hne' : t₁ ≠ t₂ := fun he => by rw [he, Nat.beq_refl] at hne; exact Bool.noConfusion hne
  refine ⟨t₁, t₂, ⟨h₁.1.1.2.2, h₁.2⟩, ⟨h₂.1.1.2.2, h₂.2⟩, decL_ne h₁.1 h₂.1 hne', ?_⟩
  rcases hc with hc | hc
  · exact Or.inl (by rw [hc])
  · refine Or.inr ?_
    have va₁ := h₁.1.1.2.1
    have va₂ := h₂.1.1.2.1
    rcases normV_cases (aK t₁) with e1 | e1 <;> rcases normV_cases (aK t₂) with e2 | e2 <;>
      rw [e1, e2] at hc
    · exact ⟨1, by rw [hc, one_smul]⟩
    · refine ⟨-1, ?_⟩
      have := congrArg decA hc
      rw [decA_negV va₂] at this
      exact LinearMap.ext fun v => by simp [this]
    · refine ⟨-1, ?_⟩
      have := congrArg decA hc
      rw [decA_negV va₁] at this
      exact LinearMap.ext fun v => by simp [← this]
    · refine ⟨1, ?_⟩
      have := congrArg decA hc
      rw [decA_negV va₁, decA_negV va₂, neg_inj] at this
      rw [one_smul, this]

theorem testBit_129 (b : ℕ) : (129 : ℕ).testBit b = (b == 0 || b == 7) := by
  by_cases hb : b < 8
  · interval_cases b <;> rfl
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : (129 : ℕ) < 2 ^ 8)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    rw [beq_eq_false_iff_ne.mpr (by omega : b ≠ 0), beq_eq_false_iff_ne.mpr (by omega : b ≠ 7)]
    rfl

theorem land129_bits (x b : ℕ) : (Nat.land x 129).testBit b = (x.testBit b && (b == 0 || b == 7)) := by
  rw [testBit_land', testBit_129]

theorem cd0_of_land {x : ℕ} (hx : ValidC x) :
    (Nat.land x 129 = 0 → cd x 0 = 0) ∧ (Nat.land x 129 = 1 → cd x 0 = 1) ∧
      (Nat.land x 129 ≠ 0 → cd x 0 ≠ 0) := by
  have e : cd x 0 = b3 (x.testBit 0) + 2 * b3 (x.testBit 7) := cast_coordK x 0
  have h0 := land129_bits x 0
  have h7 := land129_bits x 7
  have hv := hx.2 0 (by omega)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, Nat.zero_testBit] at h0 h7
    have a0 : x.testBit 0 = false := by simpa using h0.symm
    have a7 : x.testBit 7 = false := by simpa using h7.symm
    rw [e, a0, a7]
    rfl
  · rw [h, show Nat.testBit 1 0 = true from rfl] at h0
    rw [h, show Nat.testBit 1 7 = false from rfl] at h7
    have a0 : x.testBit 0 = true := by simpa using h0.symm
    have a7 : x.testBit 7 = false := by simpa using h7.symm
    rw [e, a0, a7]
    rfl
  · rw [e]
    have hne : x.testBit 0 = true ∨ x.testBit 7 = true := by
      by_contra hc
      simp only [not_or, Bool.not_eq_true] at hc
      apply h
      refine Nat.eq_of_testBit_eq fun b => ?_
      rw [land129_bits, Nat.zero_testBit]
      by_cases b0 : b = 0
      · rw [b0, hc.1]
        rfl
      · by_cases b7 : b = 7
        · rw [b7, hc.2]
          rfl
        · simp [b0, b7]
    simp only [Nat.zero_add] at hv
    revert hv hne
    cases x.testBit 0 <;> cases x.testBit 7 <;> decide

theorem usRow_zero (j : Fin 7) : usRow j 0 = if j = 0 then 1 else 0 := by
  revert j
  decide

theorem decA_e0 (a : ℕ) : decA a e0 = cd a 0 := by
  have : e0 = Pi.single 0 1 := rfl
  rw [this, decA_single]
  simp [usRow_zero]

theorem not_mem_uSpan {v : V7} (h : us 0 v ≠ 0) : v ∉ uSpan := by
  intro hv
  have hle : uSpan ≤ LinearMap.ker (us 0) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, us_ub, (Fin.succ_ne_zero j).symm, if_false]
  exact h (hle hv)

theorem epsBit_eq (d i : ℕ) : epsBit d i = cbitK d (i + 1) := by
  unfold epsBit cbitK
  have : Nat.add i 8 = Nat.add (i + 1) 7 := by
    simp only [Nat.add_eq]
  rw [this]

theorem validC_code7 {c : Fin 7 → ℕ} : ValidC (code7 c) := by
  refine ⟨code7_lt c, fun j hj h => ?_⟩
  have h1 := code7_testBit_lo (c := c) ⟨j, hj⟩
  have h2 := code7_testBit_hi (c := c) ⟨j, hj⟩
  simp only at h1 h2
  rw [h1, h2] at h
  obtain ⟨a, b⟩ := h
  rw [beq_iff_eq] at a b
  omega

theorem epsK_eq (row : ℕ → ℕ) (v : ℕ) : epsK row v =
    code7 fun j => if (j : ℕ) = 0 then 0 else dotK (row ((j : ℕ) - 1)) v := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  simp only [epsK, epsBit_eq, code7, testBit_lor', Nat.testBit_or, testBit_cbitK]
  simp [Bool.or_assoc]

noncomputable def epsF (i : Fin 6) : Dual (ZMod 3) V7 := ∑ k : Fin 7, cd (cRow i) k • us k

theorem epsF_epsV : ∀ i m : Fin 6, epsF i (epsV m) = if i = m then 1 else 0 := by
  have key : ∀ i m : Fin 6, (∑ k : Fin 7, cd (cRow i) k * ∑ l : Fin 7, usRow k l * epsV m l) =
      if i = m then 1 else 0 := by
    decide +kernel
  intro i m
  rw [← key i m]
  simp [epsF, us, rowF, LinearMap.sum_apply]

theorem us_epsV : ∀ (m : Fin 6) (k : Fin 7), us k (epsV m) = cd (dRow m) k := by
  have key : ∀ (m : Fin 6) (k : Fin 7), (∑ l : Fin 7, usRow k l * epsV m l) = cd (dRow m) k := by
    decide +kernel
  intro m k
  rw [← key m k]
  simp [us, rowF, LinearMap.sum_apply]

theorem valid_rows : ∀ i : Fin 6, ValidC (cRow i) ∧ ValidC (dRow i) := by
  unfold ValidC
  decide +kernel

theorem dotK_cRow {h : ℕ} (i : Fin 6) : (dotK (cRow i) h : ZMod 3) = epsF i (decV h) := by
  rw [dotK_cast (validC_land (valid_rows i).1)]
  simp only [epsF, LinearMap.sum_apply, LinearMap.smul_apply, us_decV, smul_eq_mul]
  rfl

theorem dotK_dRow {a : ℕ} (m : Fin 6) : (dotK (dRow m) a : ZMod 3) = decA a (epsV m) := by
  rw [dotK_cast (validC_land (valid_rows m).2)]
  simp only [decA, LinearMap.sum_apply, LinearMap.smul_apply, us_epsV, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem oneBit_of : ∀ x < 128, (∃ j < 7, x.testBit j = true ∧ ∀ k < 7, x.testBit k = true → k = j) →
    oneBit x = true := by
  decide +kernel

theorem eq126 : ∀ x < 128, (∀ j < 7, x.testBit j = decide (j ≠ 0)) → x = 126 := by
  decide +kernel

theorem suppRow_bits {he ae : ℕ} (hhe : ValidC he) (hae : ValidC ae) (i : ℕ) (hi : i < 6) :
    suppRow he ae i < 2 ^ 7 ∧ ∀ j (hj : j < 7), (suppRow he ae i).testBit j =
      decide ((if j = i + 1 then 1 else 0) - cd he ⟨i + 1, by omega⟩ * cd ae ⟨j, hj⟩ ≠ 0) := by
  have ee : Nat.shiftLeft 1 (Nat.succ i) =
      code7 fun j => if (j : ℕ) = i + 1 then 1 else 0 := by
    refine Nat.eq_of_testBit_eq fun b => ?_
    rw [shl_eq, one_mul, Nat.testBit_two_pow]
    simp only [code7, Nat.testBit_or, testBit_cbitK]
    by_cases hb : b = i + 1
    · subst hb
      interval_cases i <;> simp
    · interval_cases i <;> simp [Ne.symm hb] <;> omega
  have hve : ValidC (Nat.shiftLeft 1 (Nat.succ i)) := by rw [ee]; exact validC_code7
  have hcd : ∀ j : Fin 7, cd (Nat.shiftLeft 1 (Nat.succ i)) j = if (j : ℕ) = i + 1 then 1 else 0 :=
    fun j => by
      rw [ee, cd_code7 (fun k => by split <;> omega)]
      by_cases h : (j : ℕ) = i + 1 <;> simp [h]
  have hdot : dotK (Nat.shiftLeft 1 (Nat.succ i)) he = (cd he ⟨i + 1, by omega⟩).val := by
    refine dotK_eq (validC_land hve) (ZMod.val_lt _) ?_
    have : ∑ j : Fin 7, (coordK (Nat.shiftLeft 1 (Nat.succ i)) j : ZMod 3) * (coordK he j : ZMod 3) =
        ∑ j : Fin 7, cd (Nat.shiftLeft 1 (Nat.succ i)) j * cd he j := rfl
    rw [this]
    simp only [hcd, ite_mul, one_mul, zero_mul, ZMod.natCast_val, ZMod.cast_id', id]
    rw [Finset.sum_eq_single (⟨i + 1, by omega⟩ : Fin 7)]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have e : suppRow he ae i = Nat.lor (pM (axpy (Nat.shiftLeft 1 (Nat.succ i))
      (dotK (Nat.shiftLeft 1 (Nat.succ i)) he) ae))
      (nM (axpy (Nat.shiftLeft 1 (Nat.succ i)) (dotK (Nat.shiftLeft 1 (Nat.succ i)) he) ae)) := by
    unfold suppRow
    simp only [letN_eq]
  obtain ⟨hv, hc⟩ := axpy_spec hve hae (dotK_lt (Nat.shiftLeft 1 (Nat.succ i)) he)
  rw [e]
  refine ⟨Nat.or_lt_two_pow (pM_lt _) (nM_lt _), fun j hj => ?_⟩
  rw [testBit_lor', testBit_pM _ _ hj, testBit_nM _ _ hj, (lane_bits hv j hj).1,
    (lane_bits hv j hj).2]
  have hcj : cd (axpy (Nat.shiftLeft 1 (Nat.succ i)) (dotK (Nat.shiftLeft 1 (Nat.succ i)) he) ae)
      ⟨j, hj⟩ = (if j = i + 1 then 1 else 0) - cd he ⟨i + 1, by omega⟩ * cd ae ⟨j, hj⟩ := by
    rw [cd, hc j hj, hdot, ZMod.natCast_val, ZMod.cast_id', id]
    have := hcd ⟨j, hj⟩
    simp only at this
    rw [← this]
    rfl
  rw [hcj]
  generalize (if j = i + 1 then (1 : ZMod 3) else 0) - cd he ⟨i + 1, by omega⟩ * cd ae ⟨j, hj⟩ = z
  revert z
  decide

theorem code7_entry_lt (row : ℕ → ℕ) (v : ℕ) (j : Fin 7) :
    (if (j : ℕ) = 0 then 0 else dotK (row ((j : ℕ) - 1)) v) < 3 := by
  split
  · omega
  · exact dotK_lt _ _

theorem cd_epsK (row : ℕ → ℕ) (v : ℕ) (j : Fin 7) :
    cd (epsK row v) j = if (j : ℕ) = 0 then 0 else (dotK (row ((j : ℕ) - 1)) v : ZMod 3) := by
  rw [epsK_eq, cd_code7 (code7_entry_lt row v)]
  simp only
  split <;> simp

theorem monoK_of_mono {t : ℕ} (ht : ReflC t) (hh0 : cd (hK t) 0 = 0) (hm : MonoEps (decL t)) :
    monoK t = true := by
  obtain ⟨σ, s, hs, hf⟩ := hm
  have hve : ValidC (epsK cRow (hK t)) := by rw [epsK_eq]; exact validC_code7
  have hva : ValidC (epsK dRow (aK t)) := by rw [epsK_eq]; exact validC_code7
  have hhe : ∀ i : Fin 6, cd (epsK cRow (hK t)) ⟨i + 1, by omega⟩ = epsF i (decV (hK t)) := by
    intro i
    rw [cd_epsK]
    simp only [show (i : ℕ) + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    exact dotK_cRow i
  have hae : ∀ m : Fin 6, cd (epsK dRow (aK t)) ⟨m + 1, by omega⟩ = decA (aK t) (epsV m) := by
    intro m
    rw [cd_epsK]
    simp only [show (m : ℕ) + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
    exact dotK_dRow m
  have hae0 : cd (epsK dRow (aK t)) ⟨0, by omega⟩ = 0 := by
    rw [cd_epsK]
    rfl
  have hM : ∀ i m : Fin 6, (if i = m then (1 : ZMod 3) else 0) -
      epsF i (decV (hK t)) * decA (aK t) (epsV m) = s m * (if i = σ m then 1 else 0) := by
    intro i m
    have := congrArg (epsF i) (hf m)
    simp only [decL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
      map_smul, smul_eq_mul, epsF_epsV] at this
    rw [mul_comm (epsF i (decV (hK t)))]
    exact this
  have hbits : ∀ i (hi : i < 6) j (hj : j < 7), (suppRow (epsK cRow (hK t)) (epsK dRow (aK t)) i).testBit j =
      decide (∃ m : Fin 6, (m : ℕ) + 1 = j ∧ σ m = ⟨i, hi⟩) := by
    intro i hi j hj
    rw [(suppRow_bits hve hva i hi).2 j hj]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hae0]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hm6 : m < 6 := by omega
      have e1 := hhe ⟨i, hi⟩
      have e2 := hae ⟨m, hm6⟩
      simp only at e1 e2
      rw [e1, e2]
      have := hM ⟨i, hi⟩ ⟨m, hm6⟩
      have hc : (if m + 1 = i + 1 then (1 : ZMod 3) else 0) =
          if (⟨i, hi⟩ : Fin 6) = ⟨m, hm6⟩ then 1 else 0 := by
        by_cases h : m = i
        · subst h
          simp
        · simp [h, Ne.symm h, Fin.ext_iff]
      rw [hc, this]
      have hex : (∃ m' : Fin 6, (m' : ℕ) + 1 = m + 1 ∧ σ m' = ⟨i, hi⟩) ↔ σ ⟨m, hm6⟩ = ⟨i, hi⟩ := by
        constructor
        · rintro ⟨m', h1, h2⟩
          have : m' = ⟨m, hm6⟩ := Fin.ext (by simp only at h1 ⊢; omega)
          rw [← this]
          exact h2
        · intro h
          exact ⟨⟨m, hm6⟩, rfl, h⟩
      rw [decide_eq_decide.2 hex]
      have hsm := hs ⟨m, hm6⟩
      by_cases h : (⟨i, hi⟩ : Fin 6) = σ ⟨m, hm6⟩
      · rw [if_pos h, mul_one, decide_eq_true hsm, decide_eq_true h.symm]
      · rw [if_neg h, mul_zero, decide_eq_false (by simp), decide_eq_false (fun h' => h h'.symm)]
  unfold monoK
  rw [letB_eq, letB_eq, andB_eq, Bool.and_eq_true, allN_iff, Nat.beq_eq]
  refine ⟨fun i hi => oneBit_of _ (suppRow_bits hve hva i hi).1 ?_, ?_⟩
  · refine ⟨(σ.symm ⟨i, hi⟩ : ℕ) + 1, by omega, ?_, fun k hk hb => ?_⟩
    · rw [hbits i hi _ (by omega), decide_eq_true_iff]
      exact ⟨σ.symm ⟨i, hi⟩, rfl, by simp⟩
    · rw [hbits i hi k hk, decide_eq_true_iff] at hb
      obtain ⟨m, h1, h2⟩ := hb
      rw [← h1, ← h2, Equiv.symm_apply_apply]
  · refine eq126 _ ?_ fun j hj => ?_
    · exact Nat.or_lt_two_pow (suppRow_bits hve hva 0 (by omega)).1 (Nat.or_lt_two_pow
        (suppRow_bits hve hva 1 (by omega)).1 (Nat.or_lt_two_pow (suppRow_bits hve hva 2
        (by omega)).1 (Nat.or_lt_two_pow (suppRow_bits hve hva 3 (by omega)).1
        (Nat.or_lt_two_pow (suppRow_bits hve hva 4 (by omega)).1
        (suppRow_bits hve hva 5 (by omega)).1))))
    · simp only [testBit_lor', hbits _ (by omega : 0 < 6) j hj, hbits _ (by omega : 1 < 6) j hj,
        hbits _ (by omega : 2 < 6) j hj, hbits _ (by omega : 3 < 6) j hj,
        hbits _ (by omega : 4 < 6) j hj, hbits _ (by omega : 5 < 6) j hj]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
        have hm6 : m < 6 := by omega
        have key : ∀ i (hi : i < 6), decide (∃ m' : Fin 6, (m' : ℕ) + 1 = m + 1 ∧ σ m' = ⟨i, hi⟩) =
            decide (σ ⟨m, hm6⟩ = ⟨i, hi⟩) := by
          intro i hi
          refine decide_eq_decide.2 ⟨?_, fun h => ⟨⟨m, hm6⟩, rfl, h⟩⟩
          rintro ⟨m', h1, h2⟩
          have : m' = ⟨m, hm6⟩ := Fin.ext (by simp only at h1 ⊢; omega)
          rw [← this]
          exact h2
        simp only [key]
        have hσ := (σ ⟨m, hm6⟩).2
        generalize σ ⟨m, hm6⟩ = q at hσ
        fin_cases q <;> simp

theorem hlFact_of_hlK {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {t : ℕ} (ht : InN B t)
    (h : hlK t = true) : HLFact B := by
  unfold hlK at h
  rw [andB_eq, orB_eq, notB_eq, notB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq,
    Bool.not_eq_true', Bool.not_eq_true'] at h
  obtain ⟨ha, hor⟩ := h
  have hR := ht.1.1
  refine ⟨t, ⟨hR.2.2, ht.2⟩, by rw [decA_e0]; exact (cd0_of_land hR.2.1).1 ha, ?_⟩
  by_cases h0 : Nat.land (hK t) 129 = 0
  · rcases hor with hh | hm
    · rw [h0] at hh
      exact absurd hh (by decide)
    · exact Or.inr fun hmono => by
        rw [monoK_of_mono hR ((cd0_of_land hR.1).1 h0) hmono] at hm
        exact Bool.noConfusion hm
  · exact Or.inl (not_mem_uSpan (by rw [us_decV]; exact (cd0_of_land hR.1).2.2 h0))

theorem genU_ge (r k : ℕ) (hk : 6 ≤ k) : genU r k = r := by
  unfold genU
  simp only [ifN_eq]
  rw [if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 0)),
    if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 1)),
    if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 2)),
    if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 3)),
    if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 4)),
    if_neg (by simpa [Nat.beq_eq] using (by omega : k ≠ 5))]

theorem genU_normal : ∀ i : Fin 6, normT (pM (hK (genU 0 i))) (nM (hK (genU 0 i))) = true ∧
    genU 0 i = mkR (hK (genU 0 i)) (aK (genU 0 i)) := by
  unfold normT lowbit
  decide +kernel

theorem inN_genU {L : Set (V7 ≃ₗ[ZMod 3] V7)} {r : ℕ} (hr : ReflN r)
    (hrL : ∃ ρ ∈ L, (ρ : V7 →ₗ[ZMod 3] V7) = decL r) (k : ℕ) : InN (cl L) (genU r k) := by
  by_cases hk : k < 6
  · obtain ⟨hR, hL⟩ := genU_spec r ⟨k, hk⟩
    have e : genU r k = genU 0 k := by
      interval_cases k <;> rfl
    have hn := genU_normal ⟨k, hk⟩
    simp only at hR hL hn
    refine ⟨⟨hR, ?_⟩, simpleD6 ⟨k, hk⟩, Subgroup.subset_closure (Or.inl ⟨_, rfl⟩), hL.symm⟩
    rw [e]
    exact hn
  · rw [genU_ge r k (by omega)]
    obtain ⟨ρ, hρ, e⟩ := hrL
    exact ⟨hr, ρ, Subgroup.subset_closure (Or.inr hρ), e⟩

theorem inN_wordK {L : Set (V7 ≃ₗ[ZMod 3] V7)} {r : ℕ} (hr : ReflN r)
    (hrL : ∃ ρ ∈ L, (ρ : V7 →ₗ[ZMod 3] V7) = decL r) (g w : ℕ) : InN (cl L) (wordK r g w) :=
  inN_wordF (fun k => ⟨(inN_genU hr hrL k).1.1, (inN_genU hr hrL k).2⟩) 20 _ w (inN_genU hr hrL g)

theorem prefix_spec {f : ℕ} (hf : f < 268435456) (hvh : validV (hK f) = true)
    (hva : validV (aK f) = true) (hah : dotK (aK f) (hK f) = 2) :
    ∑ j, cd (aK f) j * cd (hK f) j = 2 ∧ ReflN (normR f) ∧ decL (normR f) = decL f := by
  have vh := validC_of_validV hvh
  have va := validC_of_validV hva
  have e := dotK_cast (validC_land va) (v := hK f)
  rw [hah, Nat.cast_ofNat] at e
  have hR : ReflC f := ⟨vh, va, by rw [decA_decV]; exact e.symm⟩
  exact ⟨e.symm, normR_normal hR (mkR_hK_aK hf), (normR_spec hR).2⟩

theorem inN_simp (L : Set (V7 ≃ₗ[ZMod 3] V7)) (k : ℕ) (hk : k < 6) : InN (cl L) (genU 0 k) := by
  obtain ⟨hR, hL⟩ := genU_spec 0 ⟨k, hk⟩
  have hn := genU_normal ⟨k, hk⟩
  simp only at hR hL hn
  exact ⟨⟨hR, hn⟩, simpleD6 ⟨k, hk⟩, Subgroup.subset_closure (Or.inl ⟨_, rfl⟩), hL.symm⟩

theorem tauC_normal : ReflN tauC := by
  have hv : ValidC (hK tauC) ∧ ValidC (aK tauC) := by
    unfold ValidC
    decide +kernel
  have hp : ∑ j : Fin 7, cd (aK tauC) j * cd (hK tauC) j = 2 := by
    decide +kernel
  have hn : normT (pM (hK tauC)) (nM (hK tauC)) = true ∧ tauC = mkR (hK tauC) (aK tauC) := by
    unfold normT lowbit
    decide +kernel
  exact ⟨⟨hv.1, hv.2, by rw [decA_decV]; exact hp⟩, hn⟩

theorem inN_wordFE {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {e : ℕ → ℕ} (hg : ∀ i, InN B (genE e i)) :
    ∀ fuel t w, InN B t → InN B (wordFE e fuel t w)
  | 0, t, _, ht => ht
  | fuel + 1, t, w, ht => by
    change InN B (ifN (Nat.beq w 0) t (letN (conjK (genE e (Nat.sub (Nat.mod w 16) 1)) t)
      fun t' => wordFE e fuel t' (Nat.div w 16)))
    rw [ifN_eq, letN_eq]
    split
    · exact ht
    · refine inN_wordFE hg fuel _ _ ⟨conjK_normal (hg _).1.1 ht.1.1, ?_⟩
      exact (inB_conjK ⟨(hg _).1.1, (hg _).2⟩ ⟨ht.1.1, ht.2⟩).2

theorem wit_spec {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {e : ℕ → ℕ} (hg : ∀ i, InN B (genE e i))
    {kind g₁ w₁ g₂ w₂ : ℕ} (h : witK e kind g₁ w₁ g₂ w₂ = true) : TVFact B ∨ HLFact B := by
  have hw : ∀ g w, InN B (wordE e g w) := fun g w => inN_wordFE hg 30 _ w (hg g)
  unfold witK at h
  rw [ifB_eq, andB_eq] at h
  split_ifs at h
  · exact Or.inl (tvFact_of_tvK (hw g₁ w₁) (hw g₂ w₂) h)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (hlFact_of_hlK (hw g₁ w₁) h.2)

theorem genE_lt (e : ℕ → ℕ) (i : ℕ) (hi : i < 6) : genE e i = genU 0 i := by
  unfold genE
  rw [ifN_eq, if_pos (by simpa using hi)]

theorem genE_ge (e : ℕ → ℕ) (i : ℕ) (hi : 6 ≤ i) : genE e i = e (i - 6) := by
  unfold genE
  rw [ifN_eq, if_neg (by simpa using hi)]
  rfl

theorem ext2_eq (a b j : ℕ) : ext2 a b j = if j = 0 then a else b := by
  unfold ext2
  rw [ifN_eq]
  simp [Nat.beq_eq]

theorem ext3_eq (a b c j : ℕ) : ext3 a b c j = if j = 0 then a else if j = 1 then b else c := by
  unfold ext3
  rw [ifN_eq, ifN_eq]
  simp [Nat.beq_eq]

theorem validC_zero : ValidC 0 := ⟨by norm_num, fun j _ h => by simp at h⟩

theorem decV_zero : decV 0 = 0 := by
  simp [decV, cd, coordK_eq]

theorem coordK_lt {v : ℕ} (hv : ValidC v) {j : ℕ} (hj : j < 7) : coordK v j < 3 := by
  rw [coordK_eq]
  have := hv.2 j hj
  split_ifs <;> simp_all

theorem decV_addV {x y : ℕ} (hx : ValidC x) (hy : ValidC y) :
    decV (addV x y) = decV x + decV y := by
  have h := (addV_spec hx hy).2
  simp only [decV, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cd, cd, cd, h j j.2]

theorem scaleV_spec {c v : ℕ} (hv : ValidC v) (hc : c < 3) :
    ValidC (scaleV c v) ∧ decV (scaleV c v) = (c : ZMod 3) • decV v := by
  unfold scaleV
  rw [ifN_eq, ifN_eq]
  interval_cases c
  · simp only [show Nat.beq 0 1 = false from rfl, show Nat.beq 0 2 = false from rfl,
      Bool.false_eq_true, if_false]
    exact ⟨validC_zero, by rw [decV_zero, Nat.cast_zero, zero_smul]⟩
  · simp only [show Nat.beq 1 1 = true from rfl, if_true]
    exact ⟨hv, by rw [Nat.cast_one, one_smul]⟩
  · simp only [show Nat.beq 2 1 = false from rfl, show Nat.beq 2 2 = true from rfl,
      Bool.false_eq_true, if_true, if_false]
    refine ⟨(negV_spec hv).1, ?_⟩
    rw [decV_negV hv]
    have h2 : ((2 : ℕ) : ZMod 3) = -1 := rfl
    rw [h2, neg_one_smul]

theorem validC_sigU : ∀ j < 6, ValidC (sigU (j + 1)) := by
  unfold ValidC
  decide +kernel

theorem coordK_sigU : ∀ j < 6, coordK (sigU (j + 1)) 0 = 0 := by
  decide +kernel

theorem sigV_spec {v : ℕ} (hv : ValidC v) : ValidC (sigV v) ∧
    decV (sigV v) = ∑ j : Fin 6, cd v j.succ • decV (sigU (j.val + 1)) := by
  have key : ∀ n ≤ 6,
      ValidC (foldUpN n (fun j s => addV s (scaleV (coordK v (Nat.succ j)) (sigU (Nat.succ j))))
        0) ∧
      decV (foldUpN n (fun j s => addV s (scaleV (coordK v (Nat.succ j)) (sigU (Nat.succ j))))
        0) = ∑ j ∈ Finset.range n, (coordK v (j + 1) : ZMod 3) • decV (sigU (j + 1)) := by
    intro n hn
    induction n with
    | zero => exact ⟨validC_zero, by rw [Finset.sum_range_zero]; exact decV_zero⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hs := scaleV_spec (validC_sigU n (by omega)) (coordK_lt hv (j := n + 1) (by omega))
      rw [foldUpN_succ, Finset.sum_range_succ]
      exact ⟨(addV_spec h1 hs.1).1, by rw [decV_addV h1 hs.1, h2, hs.2]⟩
  unfold sigV
  obtain ⟨h1, h2⟩ := key 6 le_rfl
  refine ⟨h1, ?_⟩
  rw [h2, Finset.sum_range (fun j => (coordK v (j + 1) : ZMod 3) • decV (sigU (j + 1)))]
  rfl

theorem decV_consts : decV 1 = e0 ∧ decV 16128 = wb ∧ ValidC 1 ∧ ValidC 16128 := by
  unfold ValidC
  decide +kernel

theorem decV_shl : ∀ m : Fin 6, decV (Nat.shiftLeft 1 (m.val + 1)) = ub m.succ := by
  decide +kernel

theorem ub_zero' : ub 0 = e0 := by
  decide +kernel

theorem twLam_cases (k : ℕ) : twLam k = 1 ∨ twLam k = 2 := by
  unfold twLam
  rw [ifN_eq]
  split <;> simp

theorem twC_cases (k : ℕ) : twC k = 1 ∨ twC k = 2 := by
  unfold twC
  rw [ifN_eq]
  split <;> simp

theorem sq_one_of_cases {n : ℕ} (h : n = 1 ∨ n = 2) : (n : ZMod 3) * n = 1 := by
  rcases h with rfl | rfl <;> decide

theorem twL_apply (k : ℕ) (x : V7) : twL k x = (((twLam k : ℕ) : ZMod 3) * us 0 x) • e0 +
    ((twC k : ℕ) : ZMod 3) • ∑ j : Fin 6, us j.succ x • decV (sigU (j.val + 1)) := by
  simp only [twL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.sum_apply, smul_smul]

theorem decA_ub (b : ℕ) (i : Fin 7) : decA b (ub i) = cd b i := by
  simp [decA, LinearMap.sum_apply, us_ub]

theorem sum_us_smul_ub (v : V7) : ∑ j : Fin 7, us j v • ub j = v := by
  have hs : ∀ i : Fin 7, (Pi.single i 1 : V7) = ∑ j : Fin 7, us j (Pi.single i 1) • ub j := by
    decide +kernel
  have hL : (∑ j : Fin 7, (us j).smulRight (ub j)) = (LinearMap.id : V7 →ₗ[ZMod 3] V7) := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : V7) = x • (Pi.single i 1 : V7) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hx, map_smul, LinearMap.id_apply, LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply]
    rw [← hs]
  have h := LinearMap.congr_fun hL v
  rw [LinearMap.sum_apply, LinearMap.id_apply] at h
  simpa only [LinearMap.smulRight_apply] using h

theorem dual_eq_ub {f g : Dual (ZMod 3) V7} (h : ∀ i, f (ub i) = g (ub i)) : f = g := by
  refine LinearMap.ext fun v => ?_
  rw [← sum_us_smul_ub v, map_sum, map_sum]
  simp only [map_smul, h]

theorem endo_eq_ub {f g : V7 →ₗ[ZMod 3] V7} (h : ∀ i, f (ub i) = g (ub i)) : f = g := by
  refine LinearMap.ext fun v => ?_
  rw [← sum_us_smul_ub v, map_sum, map_sum]
  simp only [map_smul, h]

theorem twL_ub0 (k : ℕ) : twL k (ub 0) = ((twLam k : ℕ) : ZMod 3) • ub 0 := by
  rw [twL_apply]
  simp [us_ub, Fin.succ_ne_zero, ← ub_zero']

theorem twL_ubs (k : ℕ) (m : Fin 6) :
    twL k (ub m.succ) = ((twC k : ℕ) : ZMod 3) • decV (sigU (m.val + 1)) := by
  rw [twL_apply]
  simp [us_ub, (Fin.succ_ne_zero _).symm, Fin.succ_inj]

theorem twL_sq (hσ : sigInvK = true) (k : ℕ) : twL k ∘ₗ twL k = LinearMap.id := by
  have hs := (allN_iff 6 _).1 hσ
  refine endo_eq_ub fun i => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  refine Fin.cases ?_ (fun m => ?_) i
  · rw [twL_ub0, map_smul, twL_ub0, smul_smul, sq_one_of_cases (twLam_cases k), one_smul]
  · have hm : sigV (sigU (Nat.succ m.val)) = Nat.shiftLeft 1 (Nat.succ m.val) :=
      Nat.eq_of_beq_eq_true (hs m.val m.2)
    obtain ⟨-, hsd⟩ := sigV_spec (validC_sigU m.val m.2)
    rw [hm, decV_shl] at hsd
    rw [twL_ubs, map_smul, twL_apply]
    simp only [us_decV]
    rw [← hsd]
    have h0 : cd (sigU (m.val + 1)) 0 = 0 := by
      rw [cd]
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 3)) (coordK_sigU m.val m.2)
    rw [h0, mul_zero, zero_smul, zero_add, smul_smul, sq_one_of_cases (twC_cases k), one_smul]

theorem twV_spec {v : ℕ} (hv : ValidC v) (k : ℕ) :
    ValidC (twV k v) ∧ decV (twV k v) = twL k (decV v) := by
  obtain ⟨d1, -, v1, -⟩ := decV_consts
  have hs1 := scaleV_spec v1 (Nat.mod_lt (twLam k * coordK v 0) (by omega : 3 > 0))
  obtain ⟨sv, sd⟩ := sigV_spec hv
  have hs2 := scaleV_spec sv (by rcases twC_cases k with h | h <;> omega : twC k < 3)
  change ValidC (addV (scaleV (twLam k * coordK v 0 % 3) 1) (scaleV (twC k) (sigV v))) ∧
    decV (addV (scaleV (twLam k * coordK v 0 % 3) 1) (scaleV (twC k) (sigV v))) = twL k (decV v)
  refine ⟨(addV_spec hs1.1 hs2.1).1, ?_⟩
  rw [decV_addV hs1.1 hs2.1, hs1.2, hs2.2, sd, d1, twL_apply]
  simp only [us_decV, ZMod.natCast_mod, Nat.cast_mul]
  rfl

theorem twA_eq (k a : ℕ) : twA k a = code7 fun j =>
    if j.val = 0 then (twLam k * coordK a 0) % 3 else (twC k * dotK a (sigU j.val)) % 3 := by
  unfold twA code7
  simp only [foldUpN_succ]
  rfl

theorem twA_spec {a : ℕ} (ha : ValidC a) (k : ℕ) :
    ValidC (twA k a) ∧ decA (twA k a) = (decA a).comp (twL k) := by
  rw [twA_eq]
  refine ⟨validC_code7, dual_eq_ub fun i => ?_⟩
  rw [decA_ub, cd_code7 (fun j => by split_ifs <;> exact Nat.mod_lt _ (by omega)),
    LinearMap.comp_apply]
  refine Fin.cases ?_ (fun m => ?_) i
  · rw [twL_ub0, map_smul, decA_ub]
    simp only [Fin.val_zero, if_true, ZMod.natCast_mod, Nat.cast_mul, smul_eq_mul]
    rfl
  · rw [twL_ubs, map_smul, ← dotK_decA ha]
    simp only [Fin.val_succ, Nat.add_one_ne_zero, if_false, ZMod.natCast_mod, Nat.cast_mul,
      smul_eq_mul]

theorem twR_spec (hσ : sigInvK = true) {r : ℕ} (hr : ReflC r) (k : ℕ) :
    ReflN (twR k r) ∧ decL (twR k r) = twL k ∘ₗ decL r ∘ₗ twL k := by
  have hGG : ∀ v, twL k (twL k v) = v := fun v => by
    rw [← LinearMap.comp_apply, twL_sq hσ, LinearMap.id_apply]
  have hh := twV_spec hr.1 k
  have ha := twA_spec hr.2.1 k
  have e : twR k r = normR (mkR (twV k (hK r)) (twA k (aK r))) := by
    unfold twR
    simp only [letN_eq]
  have hR : ReflC (mkR (twV k (hK r)) (twA k (aK r))) := by
    refine ⟨by rw [hK_mkR' hh.1]; exact hh.1, by rw [aK_mkR' hh.1 ha.1]; exact ha.1, ?_⟩
    rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1, hh.2, ha.2, LinearMap.comp_apply, hGG]
    exact hr.2.2
  rw [e]
  refine ⟨normR_normal hR (by rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1]), ?_⟩
  rw [(normR_spec hR).2]
  unfold decL
  rw [hK_mkR' hh.1, aK_mkR' hh.1 ha.1, hh.2, ha.2]
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, map_sub, map_smul, hGG]

theorem applyR_spec {s v : ℕ} (hs : ReflC s) (hv : ValidC v) :
    ValidC (applyR s v) ∧ decV (applyR s v) = decL s (decV v) := by
  unfold applyR
  refine ⟨(axpy_spec hv hs.1 (dotK_lt _ _)).1, ?_⟩
  rw [decV_axpy hv hs.1 (dotK_lt _ _), dotK_decA hs.2.1]
  rfl

theorem applyWF_spec {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {e : ℕ → ℕ} (hg : ∀ i, InN B (genE e i)) :
    ∀ fuel w, ∃ ψ ∈ B, ∀ v, ValidC v → ValidC (applyWF e fuel v w) ∧
      decV (applyWF e fuel v w) = ψ (decV v)
  | 0, _ => ⟨1, B.one_mem, fun _ hv => ⟨hv, rfl⟩⟩
  | fuel + 1, w => by
    by_cases hw : w = 0
    · refine ⟨1, B.one_mem, fun v hv => ?_⟩
      have e1 : applyWF e (fuel + 1) v w = v := by
        subst hw
        rfl
      rw [e1]
      exact ⟨hv, rfl⟩
    · obtain ⟨ψ, hψ, hψv⟩ := applyWF_spec hg fuel (Nat.div w 16)
      obtain ⟨⟨hR, -⟩, ρs, hρs, es⟩ := hg (Nat.sub (Nat.mod w 16) 1)
      refine ⟨ψ * ρs, B.mul_mem hψ hρs, fun v hv => ?_⟩
      have e1 : applyWF e (fuel + 1) v w =
          applyWF e fuel (applyR (genE e (Nat.sub (Nat.mod w 16) 1)) v) (Nat.div w 16) := by
        change ifN (Nat.beq w 0) v (letN (applyR (genE e (Nat.sub (Nat.mod w 16) 1)) v)
          fun v' => applyWF e fuel v' (Nat.div w 16)) = _
        rw [ifN_eq, letN_eq, if_neg (by simpa [Nat.beq_eq] using hw)]
      have hA := applyR_spec hR hv
      obtain ⟨h1, h2⟩ := hψv _ hA.1
      rw [e1]
      refine ⟨h1, ?_⟩
      rw [h2, hA.2, ← es]
      rfl

theorem anyN_exists {f : ℕ → Bool} : ∀ {n : ℕ}, anyN n f = true → ∃ i < n, f i = true
  | 0, h => Bool.noConfusion h
  | n + 1, h => by
    change orB (f n) (anyN n f) = true at h
    rw [orB_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨n, by omega, h⟩
    · obtain ⟨i, hi, hf⟩ := anyN_exists h
      exact ⟨i, by omega, hf⟩

theorem inSpan_spec {p q v : ℕ} (hp : ValidC p) (hq : ValidC q) (h : inSpan p q v = true) :
    decV v ∈ Submodule.span (ZMod 3) {decV p, decV q} := by
  obtain ⟨c, hc, hb⟩ := anyN_exists h
  rw [Nat.beq_eq] at hb
  have s1 := scaleV_spec hp (by omega : c / 3 < 3)
  have s2 := scaleV_spec hq (by omega : c % 3 < 3)
  rw [hb]
  change decV (addV (scaleV (c / 3) p) (scaleV (c % 3) q)) ∈ _
  rw [decV_addV s1.1 s2.1, s1.2, s2.2]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))

theorem planeK_spec {B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} {e : ℕ → ℕ} (hg : ∀ i, InN B (genE e i))
    {k w : ℕ} (h : planeK e k w = true) : PlaneFact B k := by
  unfold planeK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨ψ, hψ, hψv⟩ := applyWF_spec hg 30 w
  obtain ⟨d1, d16, v1, v16⟩ := decV_consts
  have p := twV_spec v1 k
  have q := twV_spec v16 k
  have s1 := inSpan_spec p.1 q.1 h.1
  have s2 := inSpan_spec p.1 q.1 h.2
  rw [(hψv 1 v1).2, p.2, q.2, d1, d16] at s1
  rw [(hψv 16128 v16).2, p.2, q.2, d1, d16] at s2
  exact ⟨ψ, hψ, s1, s2⟩

end CovS

open CovS in
theorem covK_sound {y : Nat} {F : Nat → Nat} {N : Nat} (h : covK y F N = true)
    (hc ac : Fin 7 → ZMod 3) (ha0 : ac 0 = 1)
    (hsort : Monotone fun k : Fin 6 => 3 * (hc k.succ).val + (ac k.succ).val)
    (hah : ∑ j, ac j * hc j = 2) (hay : ∑ j, ac j * cd y j = 0) :
    ∃ i < N, cd (hK (F i)) = hc ∧ cd (aK (F i)) = ac := by
  have hfold : foldUpN 3 (fun h₀ s => covF (keepL y) F N 6 1 0 (cbitK h₀ 0) (cbitK 1 0) s) 0 = N :=
    Nat.eq_of_beq_eq_true h
  exact cov_main (hd := id) (ha := fun _ => 1) (fun _ => rfl) hfold (ZMod.val_lt (hc 0)) hc ac rfl
    (by rw [ha0]; rfl) hsort (keepL_code7 hah hay)

open CovS in
theorem covT_sound {F : Nat → Nat} {N : Nat} (h : covT F N = true)
    (hc ac : Fin 7 → ZMod 3)
    (hhead : (hc 0, ac 0) ∈ [((0 : ZMod 3), (0 : ZMod 3)), (0, 1), (1, 0), (1, 1), (1, 2)])
    (hsort : Monotone fun k : Fin 6 => 3 * (hc k.succ).val + (ac k.succ).val)
    (hah : ∑ j, ac j * hc j = 2) (hay : ∑ j, ac j * cd 16128 j = 0)
    (htau : ¬ (hc = cd 1 ∧ ac = cd 128)) (htr : ¬ (hc = cd 8224 ∧ ac = cd 8224)) :
    ∃ i < N, cd (hK (F i)) = hc ∧ cd (aK (F i)) = ac := by
  have hval : ∀ z : ZMod 3, z.val < 3 := fun z => ZMod.val_lt z
  have eH : cd (code7 fun j => (hc j).val) = hc := by
    rw [cd_code7 fun j => hval _]
    funext j
    simp
  have eA : cd (code7 fun j => (ac j).val) = ac := by
    rw [cd_code7 fun j => hval _]
    funext j
    simp
  have hne : ∀ h₁ a₁, h₁ < 2 ^ 14 → a₁ < 2 ^ 14 → ¬(hc = cd h₁ ∧ ac = cd a₁) →
      Nat.beq (mkR (code7 fun j => (hc j).val) (code7 fun j => (ac j).val)) (mkR h₁ a₁) = false := by
    intro h₁ a₁ hh ha ht
    cases hb : Nat.beq (mkR (code7 fun j => (hc j).val) (code7 fun j => (ac j).val)) (mkR h₁ a₁)
    · rfl
    · exfalso
      rw [Nat.beq_eq] at hb
      have e1 := congrArg hK hb
      have e2 := congrArg aK hb
      rw [hK_mkR (code7_lt _), hK_mkR hh] at e1
      rw [aK_mkR (code7_lt _) (code7_lt _), aK_mkR hh ha] at e2
      exact ht ⟨by rw [← e1, eH], by rw [← e2, eA]⟩
  have hkeep : keepT (code7 fun j => (hc j).val) (code7 fun j => (ac j).val) = true := by
    unfold keepT
    rw [andB_eq, andB_eq, notB_eq, notB_eq, keepL_code7 hah hay]
    unfold tauC trC
    rw [hne 1 128 (by norm_num) (by norm_num) htau, hne 8224 8224 (by norm_num) (by norm_num) htr]
    rfl
  have hfold : foldUpN 5 (fun q s => covF keepT F N 6 1 0 (cbitK (headH q) 0)
      (cbitK (headA q) 0) s) 0 = N := Nat.eq_of_beq_eq_true h
  have key : ∀ q0 < 5, headH q0 = (hc 0).val → headA q0 = (ac 0).val →
      ∃ i < N, cd (hK (F i)) = hc ∧ cd (aK (F i)) = ac := fun q0 hq h1 h2 =>
    cov_main (hd := headH) (ha := headA) (fun _ => rfl) hfold hq hc ac h1 h2 hsort hkeep
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hhead
  rcases hhead with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact key 0 (by omega) (by rw [e1]; rfl) (by rw [e2]; rfl)
  · exact key 1 (by omega) (by rw [e1]; rfl) (by rw [e2]; rfl)
  · exact key 2 (by omega) (by rw [e1]; rfl) (by rw [e2]; rfl)
  · exact key 3 (by omega) (by rw [e1]; rfl) (by rw [e2]; rfl)
  · exact key 4 (by omega) (by rw [e1]; rfl) (by rw [e2]; rfl)

open CovS in
theorem rowK_sound {y : Nat} {F : Nat → Nat} {S : List Nat} {i kind g₁ w₁ g₂ w₂ : Nat}
    (h : rowK y F S i kind g₁ w₁ g₂ w₂ = true) :
    ∑ j, cd (aK (F i)) j * cd (hK (F i)) j = 2 ∧ ∑ j, cd (aK (F i)) j * cd y j = 0 ∧
      cd (aK (F i)) 0 = 1 ∧
      ∀ ρ : V7 ≃ₗ[ZMod 3] V7, (ρ : V7 →ₗ[ZMod 3] V7) = decL (F i) →
        TVFact (cl {ρ}) ∨ HLFact (cl {ρ}) ∨ i ∈ S := by
  unfold rowK at h
  simp only [letB_eq, andB_eq, ifB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hvh, hva, hah, hay, h129, hk⟩ := h
  obtain ⟨e2, hN, hL⟩ := prefix_spec hf hvh hva hah
  have va := validC_of_validV hva
  refine ⟨e2, ?_, (cd0_of_land va).2.1 h129, fun ρ hρ => ?_⟩
  · have e := dotK_cast (validC_land va) (v := y)
    rw [hay, Nat.cast_zero] at e
    exact e.symm
  · have hrL : ∃ ρ' ∈ ({ρ} : Set (V7 ≃ₗ[ZMod 3] V7)),
        (ρ' : V7 →ₗ[ZMod 3] V7) = decL (normR (F i)) := ⟨ρ, rfl, by rw [hρ, hL]⟩
    split_ifs at hk
    · exact Or.inl (tvFact_of_tvK (inN_wordK hN hrL g₁ w₁) (inN_wordK hN hrL g₂ w₂) hk)
    · exact Or.inr (Or.inl (hlFact_of_hlK (inN_wordK hN hrL g₁ w₁) hk))
    · rw [Bool.and_eq_true] at hk
      exact Or.inr (Or.inr (memL_mem hk.2))

open CovS in
theorem rowT_sound {F : Nat → Nat} {S : List Nat} {i kind g₁ w₁ g₂ w₂ : Nat}
    (h : rowT F S i kind g₁ w₁ g₂ w₂ = true) :
    ∑ j, cd (aK (F i)) j * cd (hK (F i)) j = 2 ∧
      ∀ T ρ : V7 ≃ₗ[ZMod 3] V7, (T : V7 →ₗ[ZMod 3] V7) = decL tauC →
        (ρ : V7 →ₗ[ZMod 3] V7) = decL (F i) →
        TVFact (cl {T, ρ}) ∨ HLFact (cl {T, ρ}) ∨ i ∈ S := by
  unfold rowT at h
  simp only [letB_eq, andB_eq, ifB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hvh, hva, hah, hk⟩ := h
  obtain ⟨e2, hN, hL⟩ := prefix_spec hf hvh hva hah
  refine ⟨e2, fun T ρ hT hρ => ?_⟩
  split_ifs at hk
  · exact Or.inr (Or.inr (memL_mem hk))
  · refine (wit_spec (fun k => ?_) hk).elim Or.inl (fun h => Or.inr (Or.inl h))
    by_cases hk6 : k < 6
    · rw [genE_lt _ _ hk6]
      exact inN_simp _ k hk6
    · rw [genE_ge _ _ (by omega), ext2_eq]
      split_ifs
      · exact ⟨tauC_normal, T, Subgroup.subset_closure (Or.inr (Or.inl rfl)), hT⟩
      · exact ⟨hN, ρ, Subgroup.subset_closure (Or.inr (Or.inr rfl)), by rw [hρ, hL]⟩

theorem rowK_prefix {y : Nat} {F : Nat → Nat} {S : List Nat} {i kind g₁ w₁ g₂ w₂ : Nat}
    (h : rowK y F S i kind g₁ w₁ g₂ w₂ = true) :
    F i < 268435456 ∧ validV (hK (F i)) = true ∧ validV (aK (F i)) = true ∧
      dotK (aK (F i)) (hK (F i)) = 2 := by
  unfold rowK at h
  simp only [CovS.letB_eq, CovS.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem rowT_prefix {F : Nat → Nat} {S : List Nat} {i kind g₁ w₁ g₂ w₂ : Nat}
    (h : rowT F S i kind g₁ w₁ g₂ w₂ = true) :
    F i < 268435456 ∧ validV (hK (F i)) = true ∧ validV (aK (F i)) = true ∧
      dotK (aK (F i)) (hK (F i)) = 2 := by
  unfold rowT at h
  simp only [CovS.letB_eq, CovS.andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

open CovS in
theorem twRowK_sound (hσ : sigInvK = true) {tauOk : Bool} {F : Nat → Nat} {S : List Nat}
    {j kind g₁ w₁ g₂ w₂ : Nat} (h : twRowK tauOk F S j kind g₁ w₁ g₂ w₂ = true)
    (hv : F (nthL S (j / 4)) < 268435456 ∧ validV (hK (F (nthL S (j / 4)))) = true ∧
      validV (aK (F (nthL S (j / 4)))) = true ∧
      dotK (aK (F (nthL S (j / 4)))) (hK (F (nthL S (j / 4)))) = 2)
    (ρ G : V7 ≃ₗ[ZMod 3] V7) (hρ : (ρ : V7 →ₗ[ZMod 3] V7) = decL (F (nthL S (j / 4))))
    (hG : (G : V7 →ₗ[ZMod 3] V7) = twL (j % 4)) :
    TVFact (cl {ρ, G}) ∨ HLFact (cl {ρ, G}) ∨ PlaneFact (cl {ρ}) (j % 4) ∨
      (tauOk = true ∧ decL (F (nthL S (j / 4))) = decL tauC) := by
  obtain ⟨hf, hvh, hva, hah⟩ := hv
  obtain ⟨-, hN, hL⟩ := prefix_spec hf hvh hva hah
  have hρr : (ρ : V7 →ₗ[ZMod 3] V7) = decL (normR (F (nthL S (j / 4)))) := by rw [hρ, hL]
  unfold twRowK at h
  rw [show Nat.div j 4 = j / 4 from rfl, show Nat.mod j 4 = j % 4 from rfl] at h
  simp only [letB_eq, ifB_eq] at h
  split_ifs at h
  · refine Or.inr (Or.inr (Or.inl (planeK_spec (fun i => ?_) h)))
    by_cases hi : i < 6
    · rw [genE_lt _ _ hi]
      exact inN_simp _ i hi
    · rw [genE_ge _ _ (by omega)]
      exact ⟨hN, ρ, Subgroup.subset_closure (Or.inr rfl), hρr⟩
  · rw [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    exact Or.inr (Or.inr (Or.inr ⟨h.1, by rw [← hL, h.2]⟩))
  · obtain ⟨hTN, hTL⟩ := twR_spec hσ hN.1 (j % 4)
    have hGm : G ∈ cl {ρ, G} := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    have hρm : ρ ∈ cl {ρ, G} := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    refine (wit_spec (fun i => ?_) h).elim Or.inl (fun h => Or.inr (Or.inl h))
    by_cases hi : i < 6
    · rw [genE_lt _ _ hi]
      exact inN_simp _ i hi
    · rw [genE_ge _ _ (by omega), ext2_eq]
      split_ifs
      · exact ⟨hN, ρ, hρm, hρr⟩
      · refine ⟨hTN, G * ρ * G, (cl _).mul_mem ((cl _).mul_mem hGm hρm) hGm, ?_⟩
        rw [hTL, ← hG, ← hρr]
        rfl

open CovS in
theorem twRowT_sound (hσ : sigInvK = true) {F : Nat → Nat} {S : List Nat}
    {j kind g₁ w₁ g₂ w₂ : Nat} (h : twRowT F S j kind g₁ w₁ g₂ w₂ = true)
    (hv : F (nthL S (j / 4)) < 268435456 ∧ validV (hK (F (nthL S (j / 4)))) = true ∧
      validV (aK (F (nthL S (j / 4)))) = true ∧
      dotK (aK (F (nthL S (j / 4)))) (hK (F (nthL S (j / 4)))) = 2)
    (T ρ G : V7 ≃ₗ[ZMod 3] V7) (hT : (T : V7 →ₗ[ZMod 3] V7) = decL tauC)
    (hρ : (ρ : V7 →ₗ[ZMod 3] V7) = decL (F (nthL S (j / 4))))
    (hG : (G : V7 →ₗ[ZMod 3] V7) = twL (j % 4)) :
    TVFact (cl {T, ρ, G}) ∨ HLFact (cl {T, ρ, G}) ∨ PlaneFact (cl {T, ρ}) (j % 4) := by
  obtain ⟨hf, hvh, hva, hah⟩ := hv
  obtain ⟨-, hN, hL⟩ := prefix_spec hf hvh hva hah
  have hρr : (ρ : V7 →ₗ[ZMod 3] V7) = decL (normR (F (nthL S (j / 4)))) := by rw [hρ, hL]
  unfold twRowT at h
  rw [show Nat.div j 4 = j / 4 from rfl, show Nat.mod j 4 = j % 4 from rfl] at h
  simp only [letB_eq, ifB_eq] at h
  split_ifs at h
  · refine Or.inr (Or.inr (planeK_spec (fun i => ?_) h))
    by_cases hi : i < 6
    · rw [genE_lt _ _ hi]
      exact inN_simp _ i hi
    · rw [genE_ge _ _ (by omega), ext2_eq]
      split_ifs
      · exact ⟨tauC_normal, T, Subgroup.subset_closure (Or.inr (Or.inl rfl)), hT⟩
      · exact ⟨hN, ρ, Subgroup.subset_closure (Or.inr (Or.inr rfl)), hρr⟩
  · obtain ⟨hTN, hTL⟩ := twR_spec hσ hN.1 (j % 4)
    have hTm : T ∈ cl {T, ρ, G} := Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have hρm : ρ ∈ cl {T, ρ, G} := Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
    have hGm : G ∈ cl {T, ρ, G} := Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl)))
    refine (wit_spec (fun i => ?_) h).elim Or.inl (fun h => Or.inr (Or.inl h))
    by_cases hi : i < 6
    · rw [genE_lt _ _ hi]
      exact inN_simp _ i hi
    · rw [genE_ge _ _ (by omega), ext3_eq]
      split_ifs
      · exact ⟨tauC_normal, T, hTm, hT⟩
      · exact ⟨hN, ρ, hρm, hρr⟩
      · refine ⟨hTN, G * ρ * G, (cl _).mul_mem ((cl _).mul_mem hGm hρm) hGm, ?_⟩
        rw [hTL, ← hG, ← hρr]
        rfl

end CFSG.StandardType.QTwoD6.K

end
