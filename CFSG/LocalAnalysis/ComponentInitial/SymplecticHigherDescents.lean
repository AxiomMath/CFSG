module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRoots

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open SymplecticFlag SymplecticTorusWeyl

variable {r : ℕ}

theorem epsAct_add (σ : Equiv.Perm (Fin r ⊕ Fin r)) (e e' : Fin r → ℤ) :
    epsAct σ (e + e') = epsAct σ e + epsAct σ e' := by
  funext j
  exact lineVal_add e e' _

theorem epsAct_sub (σ : Equiv.Perm (Fin r ⊕ Fin r)) (e e' : Fin r → ℤ) :
    epsAct σ (e - e') = epsAct σ e - epsAct σ e' := by
  funext j
  exact lineVal_sub e e' _

theorem epsAct_neg (σ : Equiv.Perm (Fin r ⊕ Fin r)) (e : Fin r → ℤ) :
    epsAct σ (-e) = -epsAct σ e := by
  rw [← zero_sub, epsAct_sub, ← zero_sub]
  congr 1
  funext j
  exact (lineVal_sub 0 0 _).trans (by simp [lineVal])

theorem epsAct_lineVec {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    (x : Fin r ⊕ Fin r) : epsAct w (lineVec r x) = lineVec r (w x) := by
  funext j
  change lineVal (lineVec r x) (w.symm (Sum.inl j)) = _
  rw [lineVal_lineVec]
  have h1 : (w.symm (Sum.inl j) = x) ↔ (Sum.inl j = w x) := Equiv.symm_apply_eq w
  have h2 : (w.symm (Sum.inl j) = x.swap) ↔ (Sum.inl j = (w x).swap) := by
    rw [Equiv.symm_apply_eq, hw x]
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl]
  generalize w x = y
  rcases y with i | i <;> simp [lineVec, Pi.single_apply]

theorem epsAct_rootVec {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    (a b : Fin r ⊕ Fin r) : epsAct w (rootVec a b) = rootVec (w a) (w b) := by
  rw [rootVec, epsAct_sub, epsAct_lineVec hw, epsAct_lineVec hw, rootVec]

theorem epsAct_inv_epsAct {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    (e : Fin r → ℤ) : epsAct w⁻¹ (epsAct w e) = e := by
  rw [← epsAct_mul hw, inv_mul_cancel, epsAct_one]

theorem epsAct_epsAct_inv {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    (e : Fin r → ℤ) : epsAct w (epsAct w⁻¹ e) = e := by
  rw [← epsAct_mul (inv_mem hw), mul_inv_cancel, epsAct_one]

theorem epsAct_mem_posRoots_or {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    {α : Fin r → ℤ} (hα : α ∈ posRoots r ∨ α ∈ negRoots r) :
    epsAct w α ∈ posRoots r ∨ epsAct w α ∈ negRoots r := by
  have key : ∀ β ∈ posRoots r, epsAct w β ∈ posRoots r ∨ epsAct w β ∈ negRoots r := by
    intro β hβ
    obtain ⟨a, b, hab, rfl⟩ := exists_rootVec_of_mem_posRoots hβ
    rw [epsAct_rootVec hw]
    exact rootVec_mem_posRoots_or (w.injective.ne (fun h : a = b => by
      rw [h] at hab; exact lt_irrefl _ hab))
  rcases hα with hα | hα
  · exact key α hα
  · have h := key (-α) (mem_negRoots.mp hα)
    rw [epsAct_neg] at h
    rcases h with h | h
    · exact Or.inr (mem_negRoots.mpr h)
    · exact Or.inl (by simpa using mem_negRoots.mp h)

theorem flagOrder_swap (x : Fin r ⊕ Fin r) :
    (flagOrder r x.swap : ℕ) + flagOrder r x + 1 = 2 * r := by
  rcases x with i | i <;> simp only [Sum.swap_inl, Sum.swap_inr, flagOrder_inl, flagOrder_inr] <;>
    have := i.2 <;> omega

theorem simpleRefl_inl (k : Fin r) : simpleRefl r k (Sum.inl k) = simpleSnd k := by
  unfold simpleRefl simpleSnd
  split_ifs with h
  · simp
  · exact Equiv.swap_apply_left _ _

theorem simpleRefl_simpleSnd (k : Fin r) : simpleRefl r k (simpleSnd k) = Sum.inl k := by
  rw [← simpleRefl_inl k, ← Equiv.Perm.mul_apply, simpleRefl_mul_self, Equiv.Perm.one_apply]

theorem epsAct_simpleRefl_simpleRootVec (k : Fin r) :
    epsAct (simpleRefl r k) (simpleRootVec r k) = -simpleRootVec r k := by
  rw [← rootVec_simpleSnd, epsAct_rootVec (simpleRefl_mem k), simpleRefl_inl,
    simpleRefl_simpleSnd, neg_rootVec]

theorem simpleRootVec_mem_posRoots (k : Fin r) : simpleRootVec r k ∈ posRoots r := by
  rw [← rootVec_simpleSnd]
  refine rootVec_mem_posRoots ?_
  unfold simpleSnd
  split_ifs with h
  · simp [flagOrder_inl]
  · rw [flagOrder_inl, flagOrder_inr]
    have := k.2
    omega

theorem swap_adjacent_of_lt {k : Fin r} (h : (k : ℕ) + 1 < r) {i j : Fin r} (hij : i < j)
    (hτ : Equiv.swap k ⟨k + 1, h⟩ j < Equiv.swap k ⟨k + 1, h⟩ i) :
    i = k ∧ j = ⟨k + 1, h⟩ := by
  have key : ∀ x : Fin r, ((Equiv.swap k ⟨k + 1, h⟩ x : Fin r) : ℕ) =
      if (x : ℕ) = (k : ℕ) then (k : ℕ) + 1 else if (x : ℕ) = (k : ℕ) + 1 then (k : ℕ)
        else (x : ℕ) := by
    intro x
    rw [Equiv.swap_apply_def]
    have hne : (⟨k + 1, h⟩ : Fin r) ≠ k := fun e => by
      have := congrArg Fin.val e
      simp at this
    by_cases h1 : x = k
    · simp [h1]
    · by_cases h2 : x = ⟨k + 1, h⟩
      · simp [h2, hne]
      · have h1' : (x : ℕ) ≠ k := fun e => h1 (Fin.ext e)
        have h2' : (x : ℕ) ≠ k + 1 := fun e => h2 (Fin.ext e)
        simp [h1, h2, h1', h2']
  rw [Fin.lt_def, key, key] at hτ
  rw [Fin.lt_def] at hij
  refine ⟨Fin.ext ?_, Fin.ext (show (j : ℕ) = (k : ℕ) + 1 from ?_)⟩ <;> split_ifs at hτ <;>
    omega

theorem rootVec_eq_simpleRootVec_of_lt (k : Fin r) {a b : Fin r ⊕ Fin r}
    (hab : (flagOrder r a : ℕ) < flagOrder r b)
    (hs : (flagOrder r (simpleRefl r k b) : ℕ) < flagOrder r (simpleRefl r k a)) :
    rootVec a b = simpleRootVec r k := by
  unfold simpleRefl at hs
  unfold simpleRootVec
  split_ifs at hs ⊢ with h
  · rcases a with i | i <;> rcases b with j | j <;>
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, flagOrder_inl,
        flagOrder_inr] at hab hs
    · obtain ⟨rfl, rfl⟩ := swap_adjacent_of_lt h hab hs
      rfl
    · have := (Equiv.swap k ⟨k + 1, h⟩ i).2
      omega
    · have := j.2
      omega
    · have hji : j < i := by
        rw [Fin.lt_def]
        have := i.2
        have := j.2
        omega
      have hτ : Equiv.swap k ⟨k + 1, h⟩ i < Equiv.swap k ⟨k + 1, h⟩ j := by
        rw [Fin.lt_def]
        have := (Equiv.swap k ⟨k + 1, h⟩ i).2
        have := (Equiv.swap k ⟨k + 1, h⟩ j).2
        omega
      obtain ⟨rfl, rfl⟩ := swap_adjacent_of_lt h hji hτ
      simp [rootVec, lineVec, sub_eq_add_neg, add_comm]
  · have hk : (k : ℕ) + 1 = r := by have := k.2; omega
    have hfo : ∀ x : Fin r ⊕ Fin r, x ≠ Sum.inl k → x ≠ Sum.inr k →
        (flagOrder r x : ℕ) ≠ r - 1 ∧ (flagOrder r x : ℕ) ≠ r := by
      intro x h1 h2
      rcases x with i | i
      · rw [flagOrder_inl]
        have hik : i ≠ k := fun h' => h1 (by rw [h'])
        have := i.2
        have : (i : ℕ) ≠ k := fun h' => hik (Fin.ext h')
        omega
      · rw [flagOrder_inr]
        have hik : i ≠ k := fun h' => h2 (by rw [h'])
        have := i.2
        have : (i : ℕ) ≠ k := fun h' => hik (Fin.ext h')
        omega
    have hk1 : (flagOrder r (Sum.inl k) : ℕ) = r - 1 := by rw [flagOrder_inl]; omega
    have hk2 : (flagOrder r (Sum.inr k) : ℕ) = r := by rw [flagOrder_inr]; omega
    simp only [Equiv.swap_apply_def] at hs
    by_cases ha1 : a = Sum.inl k
    · by_cases hb2 : b = Sum.inr k
      · subst ha1
        subst hb2
        simp [rootVec, lineVec, two_smul]
      · rw [ite_eq_left ha1] at hs
        have hb1 : b ≠ Sum.inl k := fun h' => by rw [h', ha1] at hab; exact lt_irrefl _ hab
        rw [ite_eq_right hb1, ite_eq_right hb2, hk2] at hs
        rw [ha1, hk1] at hab
        have := hfo b hb1 hb2
        omega
    by_cases ha2 : a = Sum.inr k
    · rw [ite_eq_right ha1, ite_eq_left ha2, hk1] at hs
      rw [ha2, hk2] at hab
      by_cases hb1 : b = Sum.inl k
      · rw [hb1, hk1] at hab
        omega
      by_cases hb2 : b = Sum.inr k
      · rw [hb2, hk2] at hab
        omega
      rw [ite_eq_right hb1, ite_eq_right hb2] at hs
      have := hfo b hb1 hb2
      omega
    rw [ite_eq_right ha1, ite_eq_right ha2] at hs
    have hfa := hfo a ha1 ha2
    by_cases hb1 : b = Sum.inl k
    · rw [ite_eq_left hb1, hk2] at hs
      rw [hb1, hk1] at hab
      have := (flagOrder r a).2
      omega
    by_cases hb2 : b = Sum.inr k
    · rw [ite_eq_right hb1, ite_eq_left hb2, hk1] at hs
      rw [hb2, hk2] at hab
      omega
    rw [ite_eq_right hb1, ite_eq_right hb2] at hs
    omega

theorem epsAct_simpleRefl_mem_negRoots_iff (k : Fin r) {β : Fin r → ℤ}
    (hβ : β ∈ posRoots r ∨ β ∈ negRoots r) :
    epsAct (simpleRefl r k) β ∈ negRoots r ↔
      (β ∈ negRoots r ∧ β ≠ -simpleRootVec r k) ∨ β = simpleRootVec r k := by
  have hαpos : simpleRootVec r k ∈ posRoots r := simpleRootVec_mem_posRoots k
  have hs := simpleRefl_mem (r := r) k
  obtain ⟨c, d, hcd, rfl⟩ : ∃ c d : Fin r ⊕ Fin r, c ≠ d ∧ β = rootVec c d := by
    rcases hβ with hβ | hβ
    · obtain ⟨a, b, hab, rfl⟩ := exists_rootVec_of_mem_posRoots hβ
      exact ⟨a, b, fun h => by rw [h] at hab; exact lt_irrefl _ hab, rfl⟩
    · obtain ⟨a, b, hab, hβ'⟩ := exists_rootVec_of_mem_posRoots (mem_negRoots.mp hβ)
      refine ⟨b, a, fun h => by rw [h] at hab; exact lt_irrefl _ hab, ?_⟩
      rw [← neg_rootVec, ← hβ', neg_neg]
  have hscd : simpleRefl r k c ≠ simpleRefl r k d := (simpleRefl r k).injective.ne hcd
  rw [epsAct_rootVec hs, rootVec_mem_negRoots_iff hscd, rootVec_mem_negRoots_iff hcd]
  constructor
  · intro h
    rcases lt_or_gt_of_ne (flagOrder_ne hcd) with hlt | hlt
    · exact Or.inr (rootVec_eq_simpleRootVec_of_lt k hlt h)
    · refine Or.inl ⟨hlt, fun heq => ?_⟩
      have h2 : rootVec (simpleRefl r k c) (simpleRefl r k d) = simpleRootVec r k := by
        rw [← epsAct_rootVec hs, heq, epsAct_neg, epsAct_simpleRefl_simpleRootVec, neg_neg]
      exact not_mem_negRoots_of_mem_posRoots (by rw [h2]; exact hαpos)
        ((rootVec_mem_negRoots_iff hscd).mpr h)
  · rintro (⟨hlt, hne⟩ | heq)
    · by_contra hnot
      have hgt : (flagOrder r (simpleRefl r k c) : ℕ) < flagOrder r (simpleRefl r k d) :=
        lt_of_le_of_ne (not_lt.mp hnot) (flagOrder_ne hscd)
      exact hne (by rw [← neg_rootVec, rootVec_eq_simpleRootVec_of_lt k hlt hgt])
    · have h2 := epsAct_simpleRefl_simpleRootVec (r := r) k
      rw [← heq, epsAct_rootVec hs] at h2
      have : rootVec (simpleRefl r k c) (simpleRefl r k d) ∈ negRoots r := by
        rw [h2, mem_negRoots, neg_neg, heq]
        exact hαpos
      exact (rootVec_mem_negRoots_iff hscd).mp this

@[expose] def invCount (w : Equiv.Perm (Fin r ⊕ Fin r)) : ℕ :=
  ((posRoots r).filter fun α => epsAct w α ∈ negRoots r).card

@[expose] def spWordProd (l : List (Fin r)) : Equiv.Perm (Fin r ⊕ Fin r) :=
  (l.map (simpleRefl r)).prod

@[expose] noncomputable def spLength (w : Equiv.Perm (Fin r ⊕ Fin r)) : ℕ :=
  sInf {m | ∃ l : List (Fin r), l.length = m ∧ spWordProd l = w}

@[expose] def IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) (l : List (Fin r)) : Prop :=
  spWordProd l = w ∧ l.length = spLength w

theorem spWordProd_cons (k : Fin r) (l : List (Fin r)) :
    spWordProd (k :: l) = simpleRefl r k * spWordProd l := by
  simp [spWordProd]

theorem spWordProd_mem (l : List (Fin r)) : spWordProd l ∈ signedPermGroup r := by
  induction l with
  | nil => exact one_mem _
  | cons k l ih => rw [spWordProd_cons]; exact mul_mem (simpleRefl_mem k) ih

theorem invCount_one : invCount (1 : Equiv.Perm (Fin r ⊕ Fin r)) = 0 := by
  rw [invCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro α hα
  rw [epsAct_one]
  exact not_mem_negRoots_of_mem_posRoots hα

theorem invCount_simpleRefl_mul {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r)
    (k : Fin r) :
    (epsAct w⁻¹ (simpleRootVec r k) ∈ posRoots r →
      invCount (simpleRefl r k * w) = invCount w + 1) ∧
    (epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r →
      invCount (simpleRefl r k * w) + 1 = invCount w) := by
  classical
  set α := simpleRootVec r k
  have hαpos : α ∈ posRoots r := simpleRootVec_mem_posRoots k
  set p := epsAct w⁻¹ α
  have hwp : epsAct w p = α := epsAct_epsAct_inv hw α
  have hroot : ∀ γ ∈ posRoots r, epsAct w γ ∈ posRoots r ∨ epsAct w γ ∈ negRoots r :=
    fun γ hγ => epsAct_mem_posRoots_or hw (Or.inl hγ)
  have hset : ∀ γ ∈ posRoots r, (epsAct (simpleRefl r k * w) γ ∈ negRoots r ↔
      (epsAct w γ ∈ negRoots r ∧ γ ≠ -p) ∨ γ = p) := by
    intro γ hγ
    rw [epsAct_mul hw, epsAct_simpleRefl_mem_negRoots_iff k (hroot γ hγ)]
    change (epsAct w γ ∈ negRoots r ∧ epsAct w γ ≠ -α) ∨ epsAct w γ = α ↔ _
    have e1 : epsAct w γ = -α ↔ γ = -p := by
      constructor
      · intro h
        rw [← epsAct_inv_epsAct hw γ, h, epsAct_neg]
      · rintro rfl
        rw [epsAct_neg, hwp]
    have e2 : epsAct w γ = α ↔ γ = p := by
      constructor
      · intro h
        rw [← epsAct_inv_epsAct hw γ, h]
      · rintro rfl
        exact hwp
    rw [ne_eq, e1, e2]
  constructor
  · intro hp
    have hnp : -p ∉ posRoots r := fun h => not_mem_negRoots_of_mem_posRoots hp
      (mem_negRoots.mpr h)
    have hpA : p ∉ (posRoots r).filter fun γ => epsAct w γ ∈ negRoots r := by
      rw [Finset.mem_filter, hwp]
      exact fun h => not_mem_negRoots_of_mem_posRoots hαpos h.2
    have heq : ((posRoots r).filter fun γ => epsAct (simpleRefl r k * w) γ ∈ negRoots r) =
        insert p ((posRoots r).filter fun γ => epsAct w γ ∈ negRoots r) := by
      ext γ
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hγ, h⟩
        rcases (hset γ hγ).mp h with ⟨h1, -⟩ | h1
        · exact Or.inr ⟨hγ, h1⟩
        · exact Or.inl h1
      · rintro (rfl | ⟨hγ, h⟩)
        · exact ⟨hp, (hset p hp).mpr (Or.inr rfl)⟩
        · exact ⟨hγ, (hset γ hγ).mpr (Or.inl ⟨h, fun h' => hnp (h' ▸ hγ)⟩)⟩
    rw [invCount, heq, Finset.card_insert_of_notMem hpA, invCount]
  · intro hp
    have hq : -p ∈ posRoots r := mem_negRoots.mp hp
    have hpp : p ∉ posRoots r := fun h => not_mem_negRoots_of_mem_posRoots h hp
    have hqA : -p ∈ (posRoots r).filter fun γ => epsAct w γ ∈ negRoots r := by
      rw [Finset.mem_filter, epsAct_neg, hwp, mem_negRoots, neg_neg]
      exact ⟨hq, hαpos⟩
    have heq : ((posRoots r).filter fun γ => epsAct (simpleRefl r k * w) γ ∈ negRoots r) =
        ((posRoots r).filter fun γ => epsAct w γ ∈ negRoots r).erase (-p) := by
      ext γ
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hγ, h⟩
        rcases (hset γ hγ).mp h with ⟨h1, h2⟩ | h1
        · exact ⟨h2, hγ, h1⟩
        · exact absurd (h1 ▸ hγ) hpp
      · rintro ⟨hne, hγ, h⟩
        exact ⟨hγ, (hset γ hγ).mpr (Or.inl ⟨h, hne⟩)⟩
    rw [invCount, heq, Finset.card_erase_of_mem hqA, invCount]
    have := Finset.card_pos.mpr ⟨_, hqA⟩
    omega

theorem eq_one_of_forall_simple {v : Equiv.Perm (Fin r ⊕ Fin r)} (hv : v ∈ signedPermGroup r)
    (h : ∀ k : Fin r, epsAct v (simpleRootVec r k) ∈ posRoots r) : v = 1 := by
  set G : ℕ → ℕ := fun n => if hn : n < r then (flagOrder r (v (Sum.inl ⟨n, hn⟩)) : ℕ) else 0
    with hG
  have hGk : ∀ n (hn : n < r), G n = flagOrder r (v (Sum.inl ⟨n, hn⟩)) := fun n hn => by
    simp [hG, hn]
  have hpos : ∀ k : Fin r,
      (flagOrder r (v (Sum.inl k)) : ℕ) < flagOrder r (v (simpleSnd k)) := by
    intro k
    have := h k
    rwa [← rootVec_simpleSnd, epsAct_rootVec hv,
      rootVec_mem_posRoots_iff (v.injective.ne (inl_ne_simpleSnd k))] at this
  have hinc : ∀ n, (hn : n + 1 < r) → G n < G (n + 1) := by
    intro n hn
    have := hpos ⟨n, by omega⟩
    simp only [simpleSnd, dite_eq_left hn] at this
    rw [hGk n (by omega), hGk (n + 1) hn]
    exact this
  have hlast : ∀ n, n + 1 = r → G n < r := by
    intro n hn
    have hk := hpos ⟨n, by omega⟩
    simp only [simpleSnd, dite_eq_right (show ¬n + 1 < r by omega)] at hk
    have hs := flagOrder_swap (r := r) (v (Sum.inl ⟨n, by omega⟩))
    rw [← hv (Sum.inl _), Sum.swap_inl] at hs
    rw [hGk n (by omega)]
    omega
  have hge : ∀ n, n < r → n ≤ G n := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have := hinc n hn
      have := ih (by omega)
      omega
  have hle : ∀ m n, n < r → n + m + 1 = r → G n ≤ n := by
    intro m
    induction m with
    | zero =>
      intro n hn hnm
      have := hlast n (by omega)
      omega
    | succ m ih =>
      intro n hn hnm
      have h1 := hinc n (by omega)
      have h2 := ih (n + 1) (by omega) (by omega)
      omega
  have hfix : ∀ k : Fin r, v (Sum.inl k) = Sum.inl k := by
    intro k
    have h1 := hge k k.2
    have h2 := hle (r - k - 1) k k.2 (by have := k.2; omega)
    have h3 := hGk k k.2
    rw [Fin.eta] at h3
    have hk : (flagOrder r (v (Sum.inl k)) : ℕ) = flagOrder r (Sum.inl k) := by
      rw [flagOrder_inl]
      omega
    exact (flagOrder r).injective (Fin.ext hk)
  ext x
  rcases x with k | k
  · rw [hfix k, Equiv.Perm.one_apply]
  · rw [← Sum.swap_inl, hv, hfix k, Equiv.Perm.one_apply]

theorem invCount_le_length (l : List (Fin r)) : invCount (spWordProd l) ≤ l.length := by
  induction l with
  | nil => simp [spWordProd, invCount_one]
  | cons k l ih =>
    rw [spWordProd_cons, List.length_cons]
    have hw := spWordProd_mem l
    rcases epsAct_mem_posRoots_or (inv_mem hw)
        (Or.inl (simpleRootVec_mem_posRoots k)) with h | h
    · rw [(invCount_simpleRefl_mul hw k).1 h]
      omega
    · have := (invCount_simpleRefl_mul hw k).2 h
      omega

theorem exists_word_length_eq :
    ∀ (n : ℕ) (w : Equiv.Perm (Fin r ⊕ Fin r)), w ∈ signedPermGroup r → invCount w = n →
      ∃ l : List (Fin r), l.length = n ∧ spWordProd l = w := by
  intro n
  induction n with
  | zero =>
    intro w hw h0
    refine ⟨[], rfl, ?_⟩
    by_contra hne
    have : w⁻¹ ≠ 1 := fun h => hne (by rw [show w = 1 from inv_eq_one.mp h]; rfl)
    obtain ⟨k, hk⟩ : ∃ k : Fin r, epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r := by
      by_contra! hall
      exact this (eq_one_of_forall_simple (inv_mem hw) fun k =>
        (epsAct_mem_posRoots_or (inv_mem hw) (Or.inl (simpleRootVec_mem_posRoots k))).resolve_right
          (hall k))
    have := (invCount_simpleRefl_mul hw k).2 hk
    omega
  | succ n ih =>
    intro w hw hn
    have hne : w⁻¹ ≠ 1 := by
      intro h
      rw [show w = 1 from inv_eq_one.mp h, invCount_one] at hn
      omega
    obtain ⟨k, hk⟩ : ∃ k : Fin r, epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r := by
      by_contra! hall
      exact hne (eq_one_of_forall_simple (inv_mem hw) fun k =>
        (epsAct_mem_posRoots_or (inv_mem hw) (Or.inl (simpleRootVec_mem_posRoots k))).resolve_right
          (hall k))
    have h1 := (invCount_simpleRefl_mul hw k).2 hk
    obtain ⟨l, hl, hprod⟩ := ih (simpleRefl r k * w) (mul_mem (simpleRefl_mem k) hw)
      (by omega)
    refine ⟨k :: l, by rw [List.length_cons, hl], ?_⟩
    rw [spWordProd_cons, hprod, ← mul_assoc, simpleRefl_mul_self, one_mul]

theorem spLength_eq_invCount {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r) :
    spLength w = invCount w := by
  obtain ⟨l, hl, hprod⟩ := exists_word_length_eq _ w hw rfl
  apply le_antisymm
  · exact Nat.sInf_le ⟨l, hl, hprod⟩
  · obtain ⟨l', hl', hprod'⟩ := Nat.sInf_mem (s := {m | ∃ l : List (Fin r), l.length = m ∧
      spWordProd l = w}) ⟨_, l, rfl, hprod⟩
    rw [spLength, ← hl', ← hprod']
    exact invCount_le_length l'

theorem signed_descents {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ signedPermGroup r) :
    spLength w = invCount w ∧
    (∀ k : Fin r,
      (spLength (simpleRefl r k * w) = spLength w - 1 ↔
        epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r) ∧
      (epsAct w⁻¹ (simpleRootVec r k) ∉ negRoots r →
        spLength (simpleRefl r k * w) = spLength w + 1)) ∧
    (∀ (k : Fin r) (l : List (Fin r)), IsSpReducedWord w (k :: l) →
      epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r ∧ IsSpReducedWord (simpleRefl r k * w) l) := by
  have hcrit : ∀ v : Equiv.Perm (Fin r ⊕ Fin r), v ∈ signedPermGroup r → ∀ k : Fin r,
      (spLength (simpleRefl r k * v) = spLength v - 1 ↔
        epsAct v⁻¹ (simpleRootVec r k) ∈ negRoots r) ∧
      (epsAct v⁻¹ (simpleRootVec r k) ∉ negRoots r →
        spLength (simpleRefl r k * v) = spLength v + 1) := by
    intro v hv k
    have hsv : simpleRefl r k * v ∈ signedPermGroup r := mul_mem (simpleRefl_mem k) hv
    rw [spLength_eq_invCount hsv, spLength_eq_invCount hv]
    have hor := epsAct_mem_posRoots_or (inv_mem hv) (Or.inl (simpleRootVec_mem_posRoots k))
    refine ⟨⟨fun heq => ?_, fun hneg => ?_⟩, fun hnot => ?_⟩
    · by_contra hnot
      have := (invCount_simpleRefl_mul hv k).1 (hor.resolve_right hnot)
      omega
    · have := (invCount_simpleRefl_mul hv k).2 hneg
      omega
    · exact (invCount_simpleRefl_mul hv k).1 (hor.resolve_right hnot)
  refine ⟨spLength_eq_invCount hw, hcrit w hw, fun k l ⟨hprod, hlen⟩ => ?_⟩
  have hsw : spWordProd l = simpleRefl r k * w := by
    rw [← hprod, spWordProd_cons, ← mul_assoc, simpleRefl_mul_self, one_mul]
  have hle : spLength (simpleRefl r k * w) ≤ l.length := Nat.sInf_le ⟨l, rfl, hsw⟩
  rw [List.length_cons] at hlen
  have hdesc : epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r := by
    by_contra hnot
    have := (hcrit w hw k).2 hnot
    omega
  refine ⟨hdesc, hsw, ?_⟩
  have := (hcrit w hw k).1.mpr hdesc
  omega

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
