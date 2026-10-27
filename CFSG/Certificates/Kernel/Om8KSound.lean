module

public import Certificates.Data.Kernel.Om8K.Defs

public section

namespace CFSG.KC.Om8K

open CFSG.CGT.Harada80 CFSG.CGT.Harada80.OmegaEight CFSG.Quasithin.SteinbergCB.G2Two
  CFSG.Quasithin.SteinbergCB.I16

theorem cond_beq {α : Type*} (a b : ℕ) (x y : α) :
    cond (Nat.beq a b) x y = if a = b then x else y := by
  by_cases h : a = b
  · subst h
    simp [Nat.beq_refl]
  · have h' : Nat.beq a b = false := Bool.eq_false_iff.2 fun h2 => h (Nat.eq_of_beq_eq_true h2)
    simp [h, h']

theorem mAppK_eq (M : List ℕ) (x : ℕ) : mAppK M x = mApp M x := by
  induction M generalizing x with
  | nil => rfl
  | cons c cs ih =>
    change cond (Nat.beq (x &&& 1) 1) c 0 ^^^ mAppK cs (x >>> 1) = mApp (c :: cs) x
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one, ih, cond_beq]
    simp only [mApp]

theorem bK_eq (x i : ℕ) : bK x i = x / 2 ^ i % 2 := by
  unfold bK
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem bK_le (x i : ℕ) : bK x i = 0 ∨ bK x i = 1 := by
  rw [bK_eq]
  exact Nat.mod_two_eq_zero_or_one _

theorem bK_eq_ite (x i : ℕ) : bK x i = if x.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, bK_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem bK_one_iff (x i : ℕ) : bK x i = 1 ↔ x.testBit i = true := by
  rw [bK_eq_ite]
  cases x.testBit i <;> simp

theorem toV_bK (x k : ℕ) : (if x.testBit k then (1 : ZMod 2) else 0) = (bK x k : ZMod 2) := by
  rw [bK_eq_ite]
  cases x.testBit k <;> simp

theorem bK_xor (a b i : ℕ) : bK (a ^^^ b) i = (bK a i + bK b i) % 2 := by
  rw [bK_eq, bK_eq, bK_eq, Nat.xor_div_two_pow, Nat.xor_mod_two_eq, Nat.add_mod]

theorem bK_xor_cast (a b i : ℕ) :
    ((bK (a ^^^ b) i : ℕ) : ZMod 2) = (bK a i : ZMod 2) + (bK b i : ZMod 2) := by
  rw [bK_xor, ZMod.natCast_mod, Nat.cast_add]

theorem bK_sq (x i : ℕ) : ((bK x i : ℕ) : ZMod 2) ^ 2 = (bK x i : ZMod 2) := by
  rcases bK_le x i with h | h <;> simp [h]

theorem vec_bK (x : ℕ) (a : Fin 3 ⊕ Fin 3 ⊕ Fin 2) :
    vec 3 x a = (bK x (codeIdx 3 a : ℕ) : ZMod 2) := by
  simp only [vec, Function.comp_apply, toV]
  exact toV_bK _ _

theorem codeIdx_vals :
    ((codeIdx 3 (Sum.inl 0) : ℕ) = 0) ∧ ((codeIdx 3 (Sum.inl 1) : ℕ) = 1) ∧
    ((codeIdx 3 (Sum.inl 2) : ℕ) = 2) ∧ ((codeIdx 3 (Sum.inr (Sum.inl 0)) : ℕ) = 3) ∧
    ((codeIdx 3 (Sum.inr (Sum.inl 1)) : ℕ) = 4) ∧ ((codeIdx 3 (Sum.inr (Sum.inl 2)) : ℕ) = 5) ∧
    ((codeIdx 3 (Sum.inr (Sum.inr 0)) : ℕ) = 6) ∧ ((codeIdx 3 (Sum.inr (Sum.inr 1)) : ℕ) = 7) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem polar_eq (x u : ℕ) : polarCode 3 x u = (polS x u : ZMod 2) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := codeIdx_vals
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [polarCode, CFSG.PGLModel.minusQuadForm, CFSG.MatrixModel.minusQuadCore,
    Fin.sum_univ_three, Pi.add_apply, vec_bK, e0, e1, e2, e3, e4, e5, e6, e7]
  push_cast [polS]
  linear_combination ((bK x 6 : ZMod 2) * (bK u 6 : ZMod 2) +
    (bK x 7 : ZMod 2) * (bK u 7 : ZMod 2)) * h2

theorem quad_eq (c : ℕ) : CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) = (qS c : ZMod 2) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := codeIdx_vals
  simp only [CFSG.PGLModel.minusQuadForm, CFSG.MatrixModel.minusQuadCore,
    Fin.sum_univ_three, vec_bK, e0, e1, e2, e3, e4, e5, e6, e7, bK_sq]
  push_cast [qS]
  ring

theorem q_iff (c : ℕ) :
    CFSG.PGLModel.minusQuadForm 3 (1 : ZMod 2) 1 (vec 3 c) ≠ 0 ↔ qS c % 2 = 1 := by
  rw [quad_eq, ← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one (qS c) with h | h <;> simp [h]

theorem reflK_lt {u x : ℕ} (hu : u < 256) (hx : x < 256) : reflK u x < 256 := by
  unfold reflK
  cases Nat.beq (Nat.mod (polS x u) 2) 1
  · exact hx
  · exact Nat.xor_lt_two_pow (n := 8) hx hu

theorem reflK_eq {u x : ℕ} (hu : u < 256) (hx : x < 256) : reflCode 3 u x = reflK u x := by
  have h256 : (256 : ℕ) = 2 ^ (3 + (3 + 2)) := by norm_num
  apply vec_inj (reflCode_lt 3 u x) (h256 ▸ reflK_lt hu hx)
  rw [vec_reflCode, polar_eq]
  unfold reflK
  rw [cond_beq]
  change _ = vec 3 (if polS x u % 2 = 1 then x ^^^ u else x)
  split_ifs with h
  · have : (polS x u : ZMod 2) = 1 := by rw [← ZMod.natCast_mod, h, Nat.cast_one]
    rw [this, one_smul, vec_xor]
  · have h0 : polS x u % 2 = 0 := by omega
    have : (polS x u : ZMod 2) = 0 := by rw [← ZMod.natCast_mod, h0, Nat.cast_zero]
    rw [this, zero_smul, add_zero]

theorem polS_xor (a b u : ℕ) : polS (a ^^^ b) u % 2 = (polS a u + polS b u) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast [polS, bK_xor_cast]
  ring

theorem xorN (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

theorem reflK_xor (u a b : ℕ): reflK u (a ^^^ b) = reflK u a ^^^ reflK u b := by
  unfold reflK
  rw [cond_beq, cond_beq, cond_beq]
  change (if polS (a ^^^ b) u % 2 = 1 then _ else _) =
    (if polS a u % 2 = 1 then _ else _) ^^^ (if polS b u % 2 = 1 then _ else _)
  have hab := polS_xor a b u
  rcases Nat.mod_two_eq_zero_or_one (polS a u) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (polS b u) with hb | hb <;>
    · have hab' : polS (a ^^^ b) u % 2 = (polS a u % 2 + polS b u % 2) % 2 := by omega
      rw [ha, hb] at hab'
      norm_num at hab'
      simp only [ha, hb, hab', xorN, if_true, if_false, zero_ne_one, one_ne_zero]
      all_goals
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_xor]
        cases a.testBit i <;> cases b.testBit i <;> cases u.testBit i <;> rfl

theorem maskL_bit (L : List ℕ) (k : ℕ) :
    (List.rec (motive := fun _ => ℕ) 0 (fun c _ ih => Nat.lor (Nat.shiftLeft 1 c) ih) L).testBit k =
      decide (k ∈ L) := by
  induction L with
  | nil => simp
  | cons c cs ih =>
    change ((1 <<< c) ||| _).testBit k = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : c = k
    · subst h
      simp
    · have h' : k ≠ c := fun e => h e.symm
      simp [h, h']

theorem nsMask_bit (c : ℕ) : bK nsMask c = if c ∈ nsCodes then 1 else 0 := by
  rw [bK_eq_ite]
  have := maskL_bit nsCodes c
  change (List.rec (motive := fun _ => ℕ) 0 (fun c _ ih => Nat.lor (Nat.shiftLeft 1 c) ih)
    nsCodes).testBit c = _ at this
  rw [show nsMask = List.rec (motive := fun _ => ℕ) 0
    (fun c _ ih => Nat.lor (Nat.shiftLeft 1 c) ih) nsCodes from rfl, this]
  by_cases h : c ∈ nsCodes <;> simp [h]

theorem keyL_bit (key : ℕ → ℕ) (L : List ℕ) (k : ℕ)
    (h : (List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.lor ih (Nat.shiftLeft 1 (key x)))
      L).testBit k = true) : ∃ x ∈ L, k = key x := by
  induction L with
  | nil => simp at h
  | cons x xs ih =>
    change (_ ||| (1 <<< key x)).testBit k = true at h
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨y, hy, rfl⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩
    · exact ⟨x, List.mem_cons_self .., (of_decide_eq_true h).symm⟩

theorem bmap_bit {k : ℕ} (h : bK bmap k = 1) :
    ∃ x < 256, k = (mApp (sCols.getD 0 []) x ^^^ x) * 256 + (mApp (sCols.getD 1 []) x ^^^ x) := by
  rw [bK_one_iff] at h
  obtain ⟨x, hx, hk⟩ := keyL_bit (fun x => Nat.add (Nat.mul (Nat.xor (mAppK (sCols.getD 0 []) x) x)
    256) (Nat.xor (mAppK (sCols.getD 1 []) x) x)) (List.range 256) k h
  refine ⟨x, List.mem_range.1 hx, ?_⟩
  rw [hk]
  change (mAppK (sCols.getD 0 []) x ^^^ x) * 256 + (mAppK (sCols.getD 1 []) x ^^^ x) = _
  rw [mAppK_eq, mAppK_eq]

theorem fox0 (v₀ v₁ : ℕ) : foxCode sCols [v₀, v₁] [(0 : Fin 2), 0, 0, 0, 0] = foxK 0 v₀ := by
  have e : foxK 0 v₀ = v₀ ^^^ mAppK (sCols.getD 0 []) (v₀ ^^^ mAppK (sCols.getD 0 [])
      (v₀ ^^^ mAppK (sCols.getD 0 []) (v₀ ^^^ mAppK (sCols.getD 0 [])
      (v₀ ^^^ mAppK (sCols.getD 0 []) 0)))) := rfl
  rw [e]
  simp [foxCode, mAppK_eq]

theorem fox1 (v₀ v₁ : ℕ) : foxCode sCols [v₀, v₁] [(1 : Fin 2), 1, 1, 1, 1] = foxK 1 v₁ := by
  have e : foxK 1 v₁ = v₁ ^^^ mAppK (sCols.getD 1 []) (v₁ ^^^ mAppK (sCols.getD 1 [])
      (v₁ ^^^ mAppK (sCols.getD 1 []) (v₁ ^^^ mAppK (sCols.getD 1 [])
      (v₁ ^^^ mAppK (sCols.getD 1 []) 0)))) := rfl
  rw [e]
  simp [foxCode, mAppK_eq]

@[expose] def lane (X j : ℕ) : ℕ := X / 256 ^ j % 256

theorem lane_xor (A B j : ℕ) : lane (A ^^^ B) j = lane A j ^^^ lane B j := by
  unfold lane
  have h1 : (256 : ℕ) ^ j = 2 ^ (8 * j) := by rw [pow_mul]; norm_num
  rw [h1, Nat.xor_div_two_pow, show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.xor_mod_two_pow]

@[expose] def LMn : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 256 * LMn n

theorem LM_eq : LM = LMn 8 := rfl

theorem and_LMn_succ (X n : ℕ) : X &&& LMn (n + 1) = X % 2 + 256 * ((X / 256) &&& LMn n) := by
  have hY := Nat.mod_add_div (X &&& LMn (n + 1)) 256
  have hm : (X &&& LMn (n + 1)) % 256 = X % 2 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.and_mod_two_pow]
    have : LMn (n + 1) % 2 ^ 8 = 1 := by simp only [LMn]; omega
    rw [this, Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 8)]
  have hd : (X &&& LMn (n + 1)) / 256 = (X / 256) &&& LMn n := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow (LMn (n + 1))]
    have : LMn (n + 1) / 2 ^ 8 = LMn n := by simp only [LMn]; omega
    rw [this]
  rw [← hY, hm, hd]

theorem lane_maskn (n : ℕ) : ∀ (X c : ℕ), c < 256 → ∀ j < n,
    (X &&& LMn n) * c / 256 ^ j % 256 = X / 256 ^ j % 2 * c := by
  induction n with
  | zero => intro X c _ j hj; omega
  | succ n ih =>
    intro X c hc j hj
    have hb : X % 2 * c < 256 := by
      rcases Nat.mod_two_eq_zero_or_one X with h | h <;> simp [h] <;> omega
    rw [and_LMn_succ, add_mul, mul_assoc]
    cases j with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    | succ j =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num : 0 < 256),
        Nat.div_eq_of_lt hb, zero_add, ih (X / 256) c hc j (by omega), Nat.div_div_eq_div_mul]

theorem lane_LM (X c : ℕ) (hc : c < 256) {j : ℕ} (hj : j < 8) :
    lane ((X &&& LM) * c) j = lane X j % 2 * c := by
  unfold lane
  rw [LM_eq, lane_maskn 8 X c hc j hj, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 256)]

theorem mApp_mod (M : List ℕ) (y : ℕ) : mApp M y = mApp M (y % 2 ^ M.length) := by
  induction M generalizing y with
  | nil => rfl
  | cons c cs ih =>
    simp only [mApp, List.length_cons]
    have h1 : y % 2 ^ (cs.length + 1) % 2 = y % 2 :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (Nat.succ_ne_zero _))
    have h2 : y % 2 ^ (cs.length + 1) / 2 = y / 2 % 2 ^ cs.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    rw [h2, ← ih]
    simp only [h1]

theorem lane_shr (X j k : ℕ) (hk : k ≤ 7) : lane (X >>> 1) j % 2 ^ k = lane X j / 2 % 2 ^ k := by
  unfold lane
  rw [Nat.shiftRight_eq_div_pow, pow_one,
    Nat.mod_mod_of_dvd _ (by rw [show (256 : ℕ) = 2 ^ 8 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)),
    show (256 : ℕ) = 2 * 128 by norm_num, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (by rw [show (128 : ℕ) = 2 ^ 7 by norm_num]; exact Nat.pow_dvd_pow 2 hk),
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

theorem laneApp_lane (M : List ℕ) (hM : ∀ c ∈ M, c < 256) (hl : M.length ≤ 8) :
    ∀ X, ∀ j < 8, lane (laneApp M X) j = mApp M (lane X j) := by
  induction M with
  | nil =>
    intro X j _
    change lane 0 j = 0
    simp [lane]
  | cons c cs ih =>
    intro X j hj
    have e : laneApp (c :: cs) X = ((X &&& LM) * c) ^^^ laneApp cs (X >>> 1) := rfl
    have hcs : cs.length ≤ 7 := by simp at hl; omega
    rw [e, lane_xor, lane_LM X c (hM c List.mem_cons_self) hj,
      ih (fun d hd => hM d (List.mem_cons_of_mem _ hd)) (by omega) (X >>> 1) j hj]
    have e2 : mApp (c :: cs) (lane X j) =
        (if lane X j % 2 = 1 then c else 0) ^^^ mApp cs (lane X j / 2) := by
      simp only [mApp]
    rw [e2]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one (lane X j) with h | h <;> simp [h]
    · rw [mApp_mod cs, lane_shr X j _ hcs, ← mApp_mod]

theorem cols_ok : ∀ b : Bool, (∀ d ∈ cond b (sCols.getD 1 []) (sCols.getD 0 []), d < 256) ∧
    (cond b (sCols.getD 1 []) (sCols.getD 0 [])).length ≤ 8 := by
  decide

theorem wordLanes_lane (cs : List Char) {j : ℕ} (hj : j < 8) :
    lane (wordLanes cs) j =
      mApp (wordCols 8 sCols (cs.map fun c => if c = '1' then (1 : Fin 2) else 0)) (2 ^ j) := by
  induction cs with
  | nil =>
    simp only [List.map_nil, wordCols]
    rw [mApp_range_pow (Nat.pow_lt_pow_right (by norm_num) hj)]
    change lane 9241421688590303745 j = 2 ^ j
    interval_cases j <;> norm_num [lane]
  | cons ch cs ih =>
    have e : wordLanes (ch :: cs) =
        laneApp (cond (Nat.beq ch.toNat 49) (sCols.getD 1 []) (sCols.getD 0 [])) (wordLanes cs) := rfl
    obtain ⟨hM, hl⟩ := cols_ok (Nat.beq ch.toNat 49)
    rw [e, laneApp_lane _ hM hl _ j hj, ih, List.map_cons, mApp_wordCols_cons]
    congr 1
    rw [cond_beq]
    by_cases h : ch.toNat = 49
    · have hc : ch = '1' := by rw [← Char.ofNat_toNat ch, h]
      rw [if_pos h, hc]
      simp
    · have hc : ch ≠ '1' := by rintro rfl; exact h rfl
      rw [if_neg h]
      simp [hc]

theorem lanesOf_lane (g : ℕ → ℕ) (L : List ℕ) (hg : ∀ j ∈ L, g j < 256) :
    ∀ k (hk : k < L.length), lane (lanesOf g L) k = g L[k] := by
  induction L with
  | nil => intro k hk; simp at hk
  | cons a L ih =>
    intro k hk
    have e : lanesOf g (a :: L) = g a + 256 * lanesOf g L := rfl
    have ha := hg a List.mem_cons_self
    rw [e]
    cases k with
    | zero =>
      simp only [lane, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
        List.getElem_cons_zero]
    | succ k =>
      have := ih (fun j hj => hg j (List.mem_cons_of_mem _ hj)) k (by simp at hk; omega)
      simp only [List.getElem_cons_succ, ← this, lane]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num : 0 < 256),
        Nat.div_eq_of_lt ha, zero_add]

theorem target_lane {u : ℕ} (hu : u < 256) {j : ℕ} (hj : j < 8) :
    lane (target u) j = reflK u (reflK v0Code (2 ^ j)) := by
  have hv : v0Code < 256 := by decide
  unfold target
  have shl1 : ∀ i, Nat.shiftLeft 1 i = 2 ^ i := fun i => Nat.one_shiftLeft i
  rw [lanesOf_lane _ _ _ j (by simpa using hj), List.getElem_range, shl1]
  intro i hi
  rw [shl1]
  have h2 : 2 ^ i < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) (by simpa using hi)
  exact reflK_lt hu (reflK_lt hv h2)

theorem two_pow_xor {n r : ℕ} (hr : r < 2 ^ n) : 2 ^ n ^^^ r = 2 ^ n + r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i n with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h]
    simp [Nat.ne_of_gt h]
  · subst h
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
    simp
  · have h1 : 2 ^ n + r < 2 ^ i := by
      have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at this
      omega
    have h2 : r < 2 ^ i := by omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [Nat.ne_of_lt h]

theorem lin_eq {f g : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) (h : ∀ j < 8, f (2 ^ j) = g (2 ^ j)) :
    ∀ x < 256, f x = g x := by
  have f0 : f 0 = 0 := by have := hf 0 0; rwa [Nat.xor_self, Nat.xor_self] at this
  have g0 : g 0 = 0 := by have := hg 0 0; rwa [Nat.xor_self, Nat.xor_self] at this
  suffices H : ∀ n ≤ 8, ∀ x < 2 ^ n, f x = g x by
    intro x hx
    exact H 8 le_rfl x (by norm_num; exact hx)
  intro n
  induction n with
  | zero =>
    intro _ x hx
    have : x = 0 := by simpa using hx
    rw [this, f0, g0]
  | succ n ih =>
    intro hn x hx
    by_cases hx' : x < 2 ^ n
    · exact ih (by omega) x hx'
    · have hr : x - 2 ^ n < 2 ^ n := by rw [pow_succ] at hx; omega
      have hx2 : x = 2 ^ n ^^^ (x - 2 ^ n) := by rw [two_pow_xor hr]; omega
      rw [hx2, hf, hg, h n (by omega), ih (by omega) _ hr]

end CFSG.KC.Om8K

end
