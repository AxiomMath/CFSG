module

public import CFSG.LieType.Universal.Unitary.Roots.Generation

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.Universal.SpecialLinear

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

@[expose] def lowIdx {n : ℕ} (a : Fin (n / 2)) : Fin n := ⟨a.val, by omega⟩

theorem val_lowIdx (a : Fin (n / 2)) : (lowIdx (n := n) a).val = a.val := rfl

theorem lowIdx_ne_rev {n : ℕ} (a b : Fin (n / 2)) : lowIdx a ≠ Fin.rev (lowIdx b) :=
  Fin.ne_of_val_ne (by simp [lowIdx]; omega)

theorem lowIdx_ne_succ {k : Fin (n / 2)} (h : k.val + 1 < n / 2) :
    lowIdx k ≠ lowIdx (n := n) ⟨k.val + 1, h⟩ :=
  Fin.ne_of_val_ne (by simp [lowIdx])

theorem exists_lowIdx {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    ∃ a : Fin (n / 2), i = lowIdx a ∨ i = Fin.rev (lowIdx a) := by
  have hv : i.val ≠ n - 1 - i.val := fun h => hi (Fin.ext (by simp; omega))
  by_cases h : i.val < n / 2
  · exact ⟨⟨i.val, h⟩, Or.inl (Fin.ext rfl)⟩
  · refine ⟨⟨n - 1 - i.val, by omega⟩, Or.inr (Fin.ext ?_)⟩
    simp [lowIdx]
    omega

theorem val_swap_apply {n : ℕ} (x y z : Fin n) :
    (Equiv.swap x y z).val = if z.val = x.val then y.val else if z.val = y.val then x.val
      else z.val := by
  rw [Equiv.swap_apply_def]
  simp only [Fin.ext_iff]
  split_ifs <;> rfl

@[expose] def levelPerm {n : ℕ} (k : Fin (n / 2)) : Equiv.Perm (Fin n) :=
  if h : k.val + 1 < n / 2 then
    Equiv.swap (lowIdx k) (lowIdx ⟨k.val + 1, h⟩) *
      Equiv.swap (Fin.rev (lowIdx k)) (Fin.rev (lowIdx ⟨k.val + 1, h⟩))
  else Equiv.swap (lowIdx k) (Fin.rev (lowIdx k))

theorem levelPerm_rev {n : ℕ} (k : Fin (n / 2)) (s : Fin n) :
    levelPerm k (Fin.rev s) = Fin.rev (levelPerm k s) := by
  by_cases h : k.val + 1 < n / 2
  · rw [levelPerm, dite_eq_left h]
    exact swap_mul_swap_rev_comm (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) s
  · rw [levelPerm, dite_eq_right h]
    exact swap_rev_comm _ s

omit hσ in
theorem levelPerm_mul_self (k : Fin (n / 2)) : levelPerm (n := n) k * levelPerm k = 1 := by
  unfold levelPerm
  by_cases h : k.val + 1 < n / 2
  · rw [dite_eq_left h]
    exact swap_mul_swap_rev_mul_self (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
  · rw [dite_eq_right h]
    exact Equiv.swap_mul_self _ _

omit hσ in
theorem levelPerm_symm (k : Fin (n / 2)) : (levelPerm (n := n) k).symm = levelPerm k :=
  (inv_eq_of_mul_eq_one_right (levelPerm_mul_self k))

@[expose] def levelSupp (k : Fin (n / 2)) (s : Fin n) : Prop :=
  s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨ s.val = n - 2 - k.val

@[expose] noncomputable def levelWeyl (ζ : traceZero σ) (k : Fin (n / 2)) : SU σ n :=
  if h : k.val + 1 < n / 2 then
    shortWeyl σ hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) 1
  else longWeyl σ (lowIdx_ne_rev k k) ζ

variable (σ) in
@[expose] def levelSign (ζ : F) (k : Fin (n / 2)) : Fin n → F :=
  if h : k.val + 1 < n / 2 then shortSign σ (lowIdx k) (lowIdx ⟨k.val + 1, h⟩) 1
  else longSign (lowIdx k) ζ

theorem coe_levelWeyl {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (k : Fin (n / 2)) :
    ((levelWeyl hσ ζ k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      signedPerm (levelPerm k) (levelSign σ (ζ : F) k) := by
  unfold levelWeyl levelSign levelPerm
  by_cases h : k.val + 1 < n / 2
  · simp only [h, dite_true]
    exact coe_shortWeyl σ hσ _ _ _ (lowIdx_ne_rev _ _) one_ne_zero
  · simp only [h, dite_false]
    exact coe_longWeyl σ _ hζ

omit hσ in
theorem levelSign_unitary (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (k : Fin (n / 2)) (s : Fin n) :
    σ (levelSign σ (ζ : F) k s) * levelSign σ (ζ : F) k (Fin.rev s) = 1 := by
  unfold levelSign
  by_cases h : k.val + 1 < n / 2
  · simp only [h, dite_true]
    exact shortSign_unitary hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) one_ne_zero s
  · simp only [h, dite_false]
    exact longSign_unitary (lowIdx_ne_rev k k) ((mem_traceZero σ).mp ζ.2) hζ s

local macro "wsimp" : tactic => `(tactic| simp (disch := omega) only [levelPerm, levelSign,
  Equiv.Perm.mul_apply, Equiv.swap_apply_def, shortSign, longSign, Fin.ext_iff, Fin.val_rev,
  val_lowIdx, Fin.val_mk, ite_eq_left, ite_eq_right, dite_eq_left, dite_eq_right, map_one, map_neg,
  inv_one, neg_neg, mul_one, one_mul, mul_neg, neg_mul, ite_true, ite_false, dite_true,
  dite_false, true_or, or_true])

theorem eq_of_not_levelSupp (z : F) {k : Fin (n / 2)} {s : Fin n}
    (hs : ¬levelSupp k s) : levelPerm k s = s ∧ levelSign σ z k s = 1 := by
  simp only [levelSupp, not_or] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have := k.isLt
  constructor
  · by_cases h : k.val + 1 < n / 2 <;> wsimp
  · by_cases h : k.val + 1 < n / 2 <;> wsimp

theorem levelSupp_levelPerm {k : Fin (n / 2)} {s : Fin n} (hs : levelSupp k s) :
    levelSupp k (levelPerm k s) := by
  have := k.isLt
  have := s.isLt
  unfold levelSupp at hs ⊢
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
  rcases hs with h | h | h | h <;> by_cases hk : k.val + 1 < n / 2 <;> wsimp <;> omega

theorem levelSign_braid_short (z : F) {k k' : Fin (n / 2)} (hk : k.val + 1 = k'.val)
    (hk' : k'.val + 1 < n / 2) :
    signedPerm (levelPerm k') (levelSign σ z k') *
        (signedPerm (levelPerm k) (levelSign σ z k) *
          signedPerm (levelPerm k') (levelSign σ z k')) =
      signedPerm (levelPerm k) (levelSign σ z k) *
        (signedPerm (levelPerm k') (levelSign σ z k') *
          signedPerm (levelPerm k) (levelSign σ z k)) := by
  simp only [signedPerm_mul_signedPerm]
  refine signedPerm_congr (fun s => ?_) (fun s => ?_)
  all_goals
    simp only [Equiv.Perm.mul_apply]
    have := s.isLt
    have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = k.val + 2 ∨ s.val = n - 1 - k.val ∨
        s.val = n - 2 - k.val ∨ s.val = n - 3 - k.val ∨
        (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ k.val + 2 ∧ s.val ≠ n - 1 - k.val ∧
          s.val ≠ n - 2 - k.val ∧ s.val ≠ n - 3 - k.val) := by omega
    rcases hc with h | h | h | h | h | h | ⟨h1, h2, h3, h4, h5, h6⟩ <;> wsimp <;> omega

theorem levelSign_braid_long (z : F) {k k' : Fin (n / 2)}
    (hk : k.val + 1 = k'.val) (hk' : k'.val + 1 = n / 2) :
    signedPerm (levelPerm k) (levelSign σ z k) * (signedPerm (levelPerm k') (levelSign σ z k') *
        (signedPerm (levelPerm k) (levelSign σ z k) *
          signedPerm (levelPerm k') (levelSign σ z k'))) =
      signedPerm (levelPerm k') (levelSign σ z k') * (signedPerm (levelPerm k) (levelSign σ z k) *
        (signedPerm (levelPerm k') (levelSign σ z k') *
          signedPerm (levelPerm k) (levelSign σ z k))) := by
  simp only [signedPerm_mul_signedPerm]
  refine signedPerm_congr (fun s => ?_) (fun s => ?_)
  all_goals
    simp only [Equiv.Perm.mul_apply]
    have := s.isLt
    have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
        s.val = n - 2 - k.val ∨
        (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ n - 1 - k.val ∧ s.val ≠ n - 2 - k.val) := by
      omega
    rcases hc with h | h | h | h | ⟨h1, h2, h3, h4⟩ <;> wsimp <;> omega

theorem coe_prod_levelWeyl {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (l : List (Fin (n / 2))) :
    ((((l.map (levelWeyl hσ ζ)).prod : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (l.map fun k => signedPerm (levelPerm k) (levelSign σ (ζ : F) k)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul, ih,
      coe_levelWeyl hσ hζ]

variable (σ) in
@[expose] def heisTorusFun (b : Fin n) (t : F) (s : Fin n) : F :=
  if s = b then t else if s = Fin.rev b then (σ t)⁻¹ else if Fin.rev s = s then σ t / t else 1

variable (σ) in
@[expose] noncomputable def levelTorus (k : Fin (n / 2)) : Subgroup (SU σ n) :=
  if h : k.val + 1 < n / 2 then
    Subgroup.closure {g | ∃ c : Fˣ, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, h⟩) (c : F))}
  else if Even n then Subgroup.closure {g | ∃ e : Fˣ, σ (e : F) = e ∧
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (longTorusFun (lowIdx k) (e : F))}
  else Subgroup.closure {g | ∃ t : Fˣ, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    diagonal (heisTorusFun σ (lowIdx k) (t : F))}

theorem shortTorus_mem_levelTorus {k : Fin (n / 2)} (h : k.val + 1 < n / 2) (c : Fˣ) :
    shortTorus σ hσ (lowIdx_ne_succ h) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (c : F) ∈
      levelTorus σ k := by
  unfold levelTorus
  rw [dite_eq_left h]
  exact Subgroup.subset_closure ⟨c, coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero⟩

omit hσ in
theorem longTorusFun_eq_heisTorusFun {b : Fin n} (hb : b ≠ Fin.rev b) {e : F} (he : σ e = e)
    (he0 : e ≠ 0) : longTorusFun b e = heisTorusFun σ b e := by
  funext s
  have hb' := hb.symm
  simp only [longTorusFun, heisTorusFun, he]
  by_cases h1 : s = b
  · simp [h1]
  by_cases h2 : s = Fin.rev b
  · simp [h2, hb']
  by_cases h3 : Fin.rev s = s
  · simp [h1, h2, h3, he0]
  · simp [h1, h2, h3]

theorem longGen_mem_levelTorus {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (e : Fˣ)
    (he : σ (e : F) = e) {g : SU σ n} (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (longTorusFun (lowIdx k) (e : F))) : g ∈ levelTorus σ k := by
  unfold levelTorus
  rw [dite_eq_right hk]
  split_ifs with hn
  · exact Subgroup.subset_closure ⟨e, he, hg⟩
  · exact Subgroup.subset_closure ⟨e, by
      rw [hg, longTorusFun_eq_heisTorusFun (lowIdx_ne_rev k k) he e.ne_zero]⟩

theorem heisGen_mem_levelTorus {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (hn : ¬Even n)
    (t : Fˣ) {g : SU σ n} (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (heisTorusFun σ (lowIdx k) (t : F))) : g ∈ levelTorus σ k := by
  unfold levelTorus
  rw [dite_eq_right hk, ite_eq_right hn]
  exact Subgroup.subset_closure ⟨t, hg⟩

theorem longTorus_mem_levelTorus {k : Fin (n / 2)} (h : ¬k.val + 1 < n / 2) {ζ : traceZero σ}
    (hζ : (ζ : F) ≠ 0) (e : Fˣ) (he : σ (e : F) = e) :
    longTorus σ (lowIdx_ne_rev k k) ζ he ∈ levelTorus σ k :=
  longGen_mem_levelTorus h e he (coe_longTorus σ _ hζ he e.ne_zero)

local macro "tsimp" : tactic => `(tactic| simp (disch := omega) only [levelPerm, levelSign,
  Equiv.Perm.mul_apply, Equiv.swap_apply_def, shortSign, longSign, shortTorusFun, longTorusFun,
  heisTorusFun, Fin.ext_iff, Fin.val_rev, val_lowIdx, Fin.val_mk, ite_eq_left, ite_eq_right,
  dite_eq_left, dite_eq_right, map_one, map_neg, map_inv₀, inv_inv, inv_one, neg_neg, mul_one,
  one_mul, mul_neg, neg_mul, ite_true, ite_false, dite_true, dite_false, true_or, or_true,
  Pi.mul_apply, Units.val_neg, Units.val_one, inv_neg, Units.val_inv_eq_inv_val, Units.val_mk0])

theorem levelWeyl_sq_mem {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (k : Fin (n / 2)) :
    levelWeyl hσ ζ k ^ 2 ∈ levelTorus σ k := by
  have hsq : (((levelWeyl hσ ζ k ^ 2 : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun s => levelSign σ (ζ : F) k (levelPerm k s) * levelSign σ (ζ : F) k s := by
    rw [pow_two, Subgroup.coe_mul, Units.val_mul, coe_levelWeyl hσ hζ, signedPerm_mul_signedPerm,
      levelPerm_mul_self, signedPerm_one]
  have := k.isLt
  by_cases h : k.val + 1 < n / 2
  · unfold levelTorus
    rw [dite_eq_left h]
    refine Subgroup.subset_closure ⟨-1, ?_⟩
    rw [hsq]
    congr 1
    funext s
    have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
        s.val = n - 2 - k.val ∨
        (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ n - 1 - k.val ∧ s.val ≠ n - 2 - k.val) := by
      omega
    rcases hc with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩ <;> tsimp
  · refine longGen_mem_levelTorus h (-1) (by simp) ?_
    rw [hsq]
    congr 1
    funext s
    have hζ' : (σ (ζ : F)) = -ζ := by
      have := (mem_traceZero σ).mp ζ.2
      linear_combination this
    rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
    · have hc : s.val = k.val ∨ s.val = n - 1 - k.val ∨
          (s.val ≠ k.val ∧ s.val ≠ n - 1 - k.val) := by omega
      rcases hc with h1 | h1 | ⟨h1, h2⟩ <;> tsimp <;> field_simp

variable (σ) in
@[expose] def diagSubgroup (n : ℕ) : Subgroup (SU σ n) where
  carrier := {g | ∃ t, ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [Subgroup.coe_mul, Units.val_mul, ha, hb, diagonal_mul_diagonal]; rfl⟩
  one_mem' := ⟨fun _ => 1, by rw [diagonal_one]; rfl⟩
  inv_mem' := by
    rintro g ⟨t, ht⟩
    have h0 := ne_zero_of_unitary (unitary_of_coe_eq_diagonal ht)
    refine ⟨t⁻¹, ?_⟩
    have hinv : ((g⁻¹ : SU σ n) : GL (Fin n) F) = (g : GL (Fin n) F)⁻¹ := rfl
    rw [hinv, Matrix.coe_units_inv, ht]
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one (n := Fin n) (α := F) using 2
    funext i
    exact mul_inv_cancel₀ (h0 i)

omit hσ in
theorem levelTorus_le_diagSubgroup (k : Fin (n / 2)) : levelTorus σ k ≤ diagSubgroup σ n := by
  unfold levelTorus
  split_ifs
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    exact ⟨_, hc⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨e, -, hg⟩
    exact ⟨_, hg⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨t, hg⟩
    exact ⟨_, hg⟩

omit hσ in
theorem coe_conj_diagonal {W g : SU σ n} {π : Equiv.Perm (Fin n)} {d t : Fin n → F}
    (hW : ((W : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = signedPerm π d)
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t) :
    (((W * g * W⁻¹ : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun r => t (π.symm r) := by
  have h1 : (((W * g : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (diagonal fun r => t (π.symm r)) * ((W : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Subgroup.coe_mul, Units.val_mul, hW, hg, signedPerm_mul_diagonal]
  rw [Subgroup.coe_mul, Units.val_mul, h1, Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul,
    mul_inv_cancel]
  simp

omit hσ in
theorem shortTorusFun_of_not_levelSupp {k : Fin (n / 2)} (h : k.val + 1 < n / 2) (c : F)
    {s : Fin n} (hs : ¬levelSupp k s) :
    shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, h⟩) c s = 1 := by
  simp only [levelSupp, not_or] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  tsimp

omit hσ in
theorem longTorusFun_of_not_levelSupp {k : Fin (n / 2)} (e : F) {s : Fin n}
    (hs : ¬levelSupp k s) : longTorusFun (lowIdx k) e s = 1 := by
  simp only [levelSupp, not_or] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  tsimp

theorem levelWeyl_conj_far {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) {j k : Fin (n / 2)}
    (hjk : j ≠ k) (hfar : ¬(j.val + 1 = k.val ∨ k.val + 1 = j.val)) {g : SU σ n} {t : Fin n → F}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t)
    (ht : ∀ s, ¬levelSupp k s → t s = 1) : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ = g := by
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ j) hg
  rw [levelPerm_symm] at hconj
  refine Subtype.ext (Units.ext ?_)
  rw [hconj, hg]
  congr 1
  funext s
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have := j.isLt
  have := k.isLt
  by_cases hs : levelSupp j s
  · have hs' := levelSupp_levelPerm hs
    rw [ht _ (fun h => by unfold levelSupp at h hs'; omega),
      ht _ (fun h => by unfold levelSupp at h hs; omega)]
  · rw [(eq_of_not_levelSupp (σ := σ) 0 hs).1]

theorem shortGen_mem_levelTorus {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : Fˣ)
    {g : SU σ n} (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F))) :
    g ∈ levelTorus σ k := by
  unfold levelTorus
  rw [dite_eq_left hk]
  exact Subgroup.subset_closure ⟨c, hg⟩

omit hσ in
theorem heisTorusFun_of_not_levelSupp {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (t : F)
    {s : Fin n} (hs : ¬levelSupp k s) : heisTorusFun σ (lowIdx k) t s = 1 := by
  simp only [levelSupp, not_or] at hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have := k.isLt
  have := s.isLt
  tsimp

include hσ in
theorem heisTorusFun_levelPerm_self {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) {t : F}
    (ht : t ≠ 0) (s : Fin n) :
    heisTorusFun σ (lowIdx k) t (levelPerm k s) = heisTorusFun σ (lowIdx k) (σ t)⁻¹ s := by
  have := k.isLt
  have := s.isLt
  have hσt : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
  · have hc : s.val = k.val ∨ s.val = n - 1 - k.val ∨ s.val = k.val + 1 ∨
        (s.val ≠ k.val ∧ s.val ≠ n - 1 - k.val ∧ s.val ≠ k.val + 1) := by omega
    rcases hc with h1 | h1 | h1 | ⟨h1, h2, h3⟩ <;> tsimp <;> (try simp only [hσ]) <;>
      (try field_simp)

omit hσ in
theorem heisTorusFun_levelPerm_succ {j k : Fin (n / 2)} (hj : j.val + 1 < n / 2)
    (hk : ¬k.val + 1 < n / 2) (hjk : j.val + 1 = k.val) (t : Fˣ) (s : Fin n) :
    heisTorusFun σ (lowIdx k) (t : F) (levelPerm j s) =
      shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (t : F) s *
        heisTorusFun σ (lowIdx k) (t : F) s := by
  have := j.isLt
  have := s.isLt
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  have hσt : σ (t : F) ≠ 0 := (map_ne_zero σ).mpr ht0
  have hc : s.val = j.val ∨ s.val = j.val + 1 ∨ s.val = j.val + 2 ∨ s.val = n - 2 - j.val ∨
      s.val = n - 1 - j.val ∨
      (s.val ≠ j.val ∧ s.val ≠ j.val + 1 ∧ s.val ≠ j.val + 2 ∧ s.val ≠ n - 2 - j.val ∧
        s.val ≠ n - 1 - j.val) := by omega
  rcases hc with h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4, h5⟩
  · tsimp
  · tsimp
    field_simp
  · rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
    · tsimp
      field_simp
    · tsimp
  · tsimp
    field_simp
  · tsimp
  · tsimp

omit hσ in
theorem shortTorusFun_levelPerm_self {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : Fˣ)
    (s : Fin n) :
    shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) (levelPerm k s) =
      shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) ((c⁻¹ : Fˣ) : F) s := by
  have := k.isLt
  have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
      s.val = n - 2 - k.val ∨
      (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ n - 1 - k.val ∧ s.val ≠ n - 2 - k.val) := by
    omega
  rcases hc with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩ <;> tsimp

omit hσ in
theorem shortTorusFun_levelPerm_succ {j k : Fin (n / 2)} (hj : j.val + 1 < n / 2)
    (hk : k.val + 1 < n / 2) (hjk : j.val + 1 = k.val) (c : Fˣ) (s : Fin n) :
    shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) (levelPerm j s) =
      shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (c : F) s *
        shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) s := by
  have := j.isLt
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hσc : σ (c : F) ≠ 0 := (map_ne_zero σ).mpr hc0
  have hc : s.val = j.val ∨ s.val = j.val + 1 ∨ s.val = j.val + 2 ∨ s.val = n - 1 - j.val ∨
      s.val = n - 2 - j.val ∨ s.val = n - 3 - j.val ∨
      (s.val ≠ j.val ∧ s.val ≠ j.val + 1 ∧ s.val ≠ j.val + 2 ∧ s.val ≠ n - 1 - j.val ∧
        s.val ≠ n - 2 - j.val ∧ s.val ≠ n - 3 - j.val) := by omega
  rcases hc with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4, h5, h6⟩ <;> tsimp <;> field_simp

omit hσ in
theorem shortTorusFun_levelPerm_pred {j k : Fin (n / 2)} (hj : j.val + 1 < n / 2)
    (hk : k.val + 1 < n / 2) (hkj : k.val + 1 = j.val) (c : Fˣ) (s : Fin n) :
    shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) (levelPerm j s) =
      shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) s *
        shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (c : F) s := by
  have := j.isLt
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hσc : σ (c : F) ≠ 0 := (map_ne_zero σ).mpr hc0
  have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = k.val + 2 ∨ s.val = n - 1 - k.val ∨
      s.val = n - 2 - k.val ∨ s.val = n - 3 - k.val ∨
      (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ k.val + 2 ∧ s.val ≠ n - 1 - k.val ∧
        s.val ≠ n - 2 - k.val ∧ s.val ≠ n - 3 - k.val) := by omega
  rcases hc with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4, h5, h6⟩ <;> tsimp <;> field_simp

omit hσ in
theorem shortTorusFun_levelPerm_last {j k : Fin (n / 2)} (hj : ¬j.val + 1 < n / 2)
    (hk : k.val + 1 < n / 2) (hkj : k.val + 1 = j.val) (c : Fˣ) (s : Fin n) :
    shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) (levelPerm j s) =
      shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F) s *
        longTorusFun (lowIdx j) ((c : F) * σ c) s := by
  have := j.isLt
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hσc : σ (c : F) ≠ 0 := (map_ne_zero σ).mpr hc0
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
  · have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
        s.val = n - 2 - k.val ∨
        (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ n - 1 - k.val ∧
          s.val ≠ n - 2 - k.val) := by omega
    rcases hc with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩ <;> tsimp <;> field_simp

omit hσ in
theorem longTorusFun_levelPerm_self {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (e : Fˣ)
    (s : Fin n) :
    longTorusFun (lowIdx k) (e : F) (levelPerm k s) =
      longTorusFun (lowIdx k) ((e⁻¹ : Fˣ) : F) s := by
  have := k.isLt
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
  · have hc : s.val = k.val ∨ s.val = n - 1 - k.val ∨
        (s.val ≠ k.val ∧ s.val ≠ n - 1 - k.val) := by omega
    rcases hc with h1 | h1 | ⟨h1, h2⟩ <;> tsimp

omit hσ in
theorem longTorusFun_levelPerm_succ {j k : Fin (n / 2)} (hj : j.val + 1 < n / 2)
    (hk : ¬k.val + 1 < n / 2) (hjk : j.val + 1 = k.val) (e : Fˣ) (he : σ (e : F) = e)
    (s : Fin n) :
    longTorusFun (lowIdx k) (e : F) (levelPerm j s) =
      shortTorusFun σ (lowIdx j) (lowIdx ⟨j.val + 1, hj⟩) (e : F) s *
        longTorusFun (lowIdx k) (e : F) s := by
  have := j.isLt
  have he0 : (e : F) ≠ 0 := e.ne_zero
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩ <;>
  · have hc : s.val = j.val ∨ s.val = j.val + 1 ∨ s.val = n - 1 - j.val ∨
        s.val = n - 2 - j.val ∨
        (s.val ≠ j.val ∧ s.val ≠ j.val + 1 ∧ s.val ≠ n - 1 - j.val ∧
          s.val ≠ n - 2 - j.val) := by omega
    rcases hc with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩ <;> tsimp <;> (try simp only [he]) <;>
      field_simp

theorem levelWeyl_conj_shortGen {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (j : Fin (n / 2))
    {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : Fˣ) {g : SU σ n}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (shortTorusFun σ (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (c : F))) :
    levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ ∈ levelTorus σ j ⊔ levelTorus σ k := by
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ j) hg
  rw [levelPerm_symm] at hconj
  have hσc : σ (c : F) ≠ 0 := (map_ne_zero σ).mpr c.ne_zero
  by_cases hjk : j = k
  · subst hjk
    have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
        shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)
          ((c⁻¹ : Fˣ) : F) := by
      refine Subtype.ext (Units.ext ?_)
      rw [hconj, coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) (c⁻¹ : Fˣ).ne_zero]
      exact congrArg diagonal (funext (shortTorusFun_levelPerm_self hk c))
    rw [heq]
    exact Subgroup.mem_sup_right (shortTorus_mem_levelTorus hσ hk c⁻¹)
  by_cases hjk1 : j.val + 1 = k.val
  · have hj : j.val + 1 < n / 2 := by omega
    have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
        shortTorus σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) (c : F) *
          shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (c : F) := by
      refine Subtype.ext (Units.ext ?_)
      rw [hconj, Subgroup.coe_mul, Units.val_mul,
        coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero,
        coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero, diagonal_mul_diagonal]
      exact congrArg diagonal (funext (shortTorusFun_levelPerm_succ hj hk hjk1 c))
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (shortTorus_mem_levelTorus hσ hj c))
      (Subgroup.mem_sup_right (shortTorus_mem_levelTorus hσ hk c))
  by_cases hkj1 : k.val + 1 = j.val
  · by_cases hj : j.val + 1 < n / 2
    · have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
          shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (c : F) *
            shortTorus σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _)
              (c : F) := by
        refine Subtype.ext (Units.ext ?_)
        rw [hconj, Subgroup.coe_mul, Units.val_mul,
          coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero,
          coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero, diagonal_mul_diagonal]
        exact congrArg diagonal (funext (shortTorusFun_levelPerm_pred hj hk hkj1 c))
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_right (shortTorus_mem_levelTorus hσ hk c))
        (Subgroup.mem_sup_left (shortTorus_mem_levelTorus hσ hj c))
    · obtain ⟨e, he_def⟩ : ∃ e : Fˣ, (e : F) = c * σ c :=
        ⟨Units.mk0 _ (mul_ne_zero c.ne_zero hσc), rfl⟩
      have he : σ (e : F) = e := by
        rw [he_def, map_mul, hσ, mul_comm]
      have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
          shortTorus σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _) (c : F) *
            longTorus σ (lowIdx_ne_rev j j) ζ he := by
        refine Subtype.ext (Units.ext ?_)
        rw [hconj, Subgroup.coe_mul, Units.val_mul,
          coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero,
          coe_longTorus σ _ hζ he e.ne_zero, diagonal_mul_diagonal, he_def]
        exact congrArg diagonal (funext (shortTorusFun_levelPerm_last hj hk hkj1 c))
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_right (shortTorus_mem_levelTorus hσ hk c))
        (Subgroup.mem_sup_left (longTorus_mem_levelTorus hj hζ e he))
  · rw [levelWeyl_conj_far hσ hζ hjk (by tauto) hg fun s hs =>
      shortTorusFun_of_not_levelSupp hk _ hs]
    exact Subgroup.mem_sup_right (shortGen_mem_levelTorus hk c hg)

theorem levelWeyl_conj_longGen {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (j : Fin (n / 2))
    {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (e : Fˣ) (he : σ (e : F) = e) {g : SU σ n}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (longTorusFun (lowIdx k) (e : F))) :
    levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ ∈ levelTorus σ j ⊔ levelTorus σ k := by
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ j) hg
  rw [levelPerm_symm] at hconj
  have := j.isLt
  have := k.isLt
  by_cases hjk : j = k
  · subst hjk
    have he' : σ ((e⁻¹ : Fˣ) : F) = (e⁻¹ : Fˣ) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, he]
    have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
        longTorus σ (lowIdx_ne_rev j j) ζ he' := by
      refine Subtype.ext (Units.ext ?_)
      rw [hconj, coe_longTorus σ _ hζ he' (e⁻¹ : Fˣ).ne_zero]
      exact congrArg diagonal (funext (longTorusFun_levelPerm_self hk e))
    rw [heq]
    exact Subgroup.mem_sup_right (longTorus_mem_levelTorus hk hζ _ he')
  by_cases hjk1 : j.val + 1 = k.val
  · have hj : j.val + 1 < n / 2 := by omega
    have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
        shortTorus σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) (e : F) *
          longTorus σ (lowIdx_ne_rev k k) ζ he := by
      refine Subtype.ext (Units.ext ?_)
      rw [hconj, Subgroup.coe_mul, Units.val_mul,
        coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) e.ne_zero,
        coe_longTorus σ _ hζ he e.ne_zero, diagonal_mul_diagonal]
      exact congrArg diagonal (funext (longTorusFun_levelPerm_succ hj hk hjk1 e he))
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (shortTorus_mem_levelTorus hσ hj e))
      (Subgroup.mem_sup_right (longTorus_mem_levelTorus hk hζ e he))
  · have hfar : ¬(j.val + 1 = k.val ∨ k.val + 1 = j.val) := by omega
    rw [levelWeyl_conj_far hσ hζ hjk hfar hg fun s hs => longTorusFun_of_not_levelSupp _ hs]
    exact Subgroup.mem_sup_right (longGen_mem_levelTorus hk e he hg)

theorem levelWeyl_conj_heisGen {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (j : Fin (n / 2))
    {k : Fin (n / 2)} (hk : ¬k.val + 1 < n / 2) (hn : ¬Even n) (t : Fˣ) {g : SU σ n}
    (hg : ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal (heisTorusFun σ (lowIdx k) (t : F))) :
    levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ ∈ levelTorus σ j ⊔ levelTorus σ k := by
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ j) hg
  rw [levelPerm_symm] at hconj
  have := j.isLt
  have := k.isLt
  by_cases hjk : j = k
  · subst hjk
    have ht' : (σ (t : F))⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr t.ne_zero)
    refine Subgroup.mem_sup_right (heisGen_mem_levelTorus hk hn (Units.mk0 _ ht') ?_)
    rw [hconj, Units.val_mk0]
    exact congrArg diagonal (funext (heisTorusFun_levelPerm_self hσ hk t.ne_zero))
  by_cases hjk1 : j.val + 1 = k.val
  · have hj : j.val + 1 < n / 2 := by omega
    have heq : levelWeyl hσ ζ j * g * (levelWeyl hσ ζ j)⁻¹ =
        shortTorus σ hσ (lowIdx_ne_succ hj) (lowIdx_ne_rev j j) (lowIdx_ne_rev _ _) (t : F) *
          g := by
      refine Subtype.ext (Units.ext ?_)
      rw [hconj, Subgroup.coe_mul, Units.val_mul,
        coe_shortTorus σ hσ _ _ _ (lowIdx_ne_rev _ _) t.ne_zero, hg, diagonal_mul_diagonal]
      exact congrArg diagonal (funext (heisTorusFun_levelPerm_succ hj hk hjk1 t))
    rw [heq]
    exact mul_mem (Subgroup.mem_sup_left (shortTorus_mem_levelTorus hσ hj t))
      (Subgroup.mem_sup_right (heisGen_mem_levelTorus hk hn t hg))
  · have hfar : ¬(j.val + 1 = k.val ∨ k.val + 1 = j.val) := by omega
    rw [levelWeyl_conj_far hσ hζ hjk hfar hg fun s hs => heisTorusFun_of_not_levelSupp hk _ hs]
    exact Subgroup.mem_sup_right (heisGen_mem_levelTorus hk hn t hg)

theorem levelWeyl_conj_levelTorus {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0) (j k : Fin (n / 2))
    (h : SU σ n) (hh : h ∈ levelTorus σ k) :
    levelWeyl hσ ζ j * h * (levelWeyl hσ ζ j)⁻¹ ∈ levelTorus σ j ⊔ levelTorus σ k := by
  suffices hle : levelTorus σ k ≤ (levelTorus σ j ⊔ levelTorus σ k).comap
      (MulAut.conj (levelWeyl hσ ζ j)).toMonoidHom from hle hh
  have hdef : levelTorus σ k = levelTorus σ k := rfl
  conv_lhs => rw [hdef]; unfold levelTorus
  by_cases hk : k.val + 1 < n / 2
  · rw [dite_eq_left hk, Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    exact levelWeyl_conj_shortGen hσ hζ j hk c hc
  · rw [dite_eq_right hk]
    by_cases hn : Even n
    · rw [ite_eq_left hn, Subgroup.closure_le]
      rintro g ⟨e, he, hg⟩
      exact levelWeyl_conj_longGen hσ hζ j hk e he hg
    · rw [ite_eq_right hn, Subgroup.closure_le]
      rintro g ⟨t, hg⟩
      exact levelWeyl_conj_heisGen hσ hζ j hk hn t hg

end CFSG.LieType.Universal.Unitary
