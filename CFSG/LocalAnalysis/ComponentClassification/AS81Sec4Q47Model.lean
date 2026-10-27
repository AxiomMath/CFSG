module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Tests
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AS81.Q47

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def xr (u v : Fin 64) : Fin 64 :=
  ⟨u.val ^^^ v.val, Nat.xor_lt_two_pow (n := 6) (lt_of_lt_of_eq u.2 (by norm_num))
    (lt_of_lt_of_eq v.2 (by norm_num))⟩

@[expose] def qv (v : Fin 64) : ℕ := q47Form[v.val]!

theorem xr_val (u v : Fin 64) : (xr u v).val = u.val ^^^ v.val := rfl

theorem xr_self (u : Fin 64) : xr u u = 0 := Fin.ext (by simp [xr_val])

theorem xr_zero (u : Fin 64) : xr u 0 = u := Fin.ext (by simp [xr_val])

theorem xr_assoc (u v w : Fin 64) : xr (xr u v) w = xr u (xr v w) :=
  Fin.ext (by simp [xr_val, Nat.xor_assoc])

theorem xr_comm (u v : Fin 64) : xr u v = xr v u := Fin.ext (by simp [xr_val, Nat.xor_comm])

theorem xr_xr_cancel (u v : Fin 64) : xr (xr u v) v = u := by
  rw [xr_assoc, xr_self, xr_zero]

@[expose] def IsIsom (π : Equiv.Perm (Fin 64)) : Prop :=
  (∀ u v, π (xr u v) = xr (π u) (π v)) ∧ ∀ v, qv (π v) = qv v

theorem IsIsom.map_zero {π : Equiv.Perm (Fin 64)} (h : IsIsom π) : π 0 = 0 := by
  have := h.1 0 0
  rw [xr_self, xr_self] at this
  exact this

@[expose] def oV : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {π | IsIsom π}
  mul_mem' {π σ} hπ hσ := ⟨fun u v => by
      simp only [Equiv.Perm.mul_apply]
      rw [hσ.1, hπ.1], fun v => by
      simp only [Equiv.Perm.mul_apply]
      rw [hπ.2, hσ.2]⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  inv_mem' {π} hπ := ⟨fun u v => by
      apply π.injective
      rw [hπ.1]
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply], fun v => by
      have := hπ.2 (π⁻¹ v)
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
      rw [Equiv.Perm.inv_def]
      exact this.symm⟩

theorem mem_oV {π : Equiv.Perm (Fin 64)} : π ∈ oV ↔ IsIsom π := Iff.rfl

theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem validA_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    validA n t = true := by
  have hr := rep_invCand_of_rep ht
  rw [validA, isInvA, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem isomCheck_parts {g : Array ℕ} (h : isomCheck g = true) :
    validA 64 g = true ∧ addCheck g = true ∧ formCheck g = true := by
  simp only [isomCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_oV_of_isomCheck {g : Array ℕ} (h : isomCheck g = true) : permOfArr 64 g ∈ oV := by
  obtain ⟨hv, ha, hf⟩ := isomCheck_parts h
  have hr := rep_of_validA hv
  refine ⟨fun u v => Fin.ext ?_, fun v => ?_⟩
  · have := List.all_eq_true.1 (List.all_eq_true.1 ha u.val (List.mem_range.2 u.2)) v.val
      (List.mem_range.2 v.2)
    rw [beq_iff_eq] at this
    rw [xr_val, ← hr.apply (xr u v).2, xr_val, this, hr.apply u.2, hr.apply v.2]
  · have := List.all_eq_true.1 hf v.val (List.mem_range.2 v.2)
    rw [beq_iff_eq] at this
    simp only [qv]
    rw [← hr.apply v.2]
    exact this

theorem exists_bit_lt : ∀ k : Fin 7, ∀ v : Fin 64, v.val < 2 ^ k.val → v.val ≠ 0 →
    ∃ i : Fin 6, i.val < k.val ∧ (v.val ^^^ 2 ^ i.val) < v.val := by decide

@[expose] def bv (i : Fin 6) : Fin 64 := ⟨2 ^ i.val, by
  have := i.2
  interval_cases i.val <;> norm_num⟩

theorem bv_val (i : Fin 6) : (bv i).val = 2 ^ i.val := rfl

theorem fix_of_fix_bv {π : Equiv.Perm (Fin 64)} (hπ : IsIsom π) {k : ℕ} (hk : k ≤ 6)
    (hfix : ∀ i : Fin 6, i.val < k → π (bv i) = bv i) :
    ∀ v : Fin 64, v.val < 2 ^ k → π v = v := by
  intro v
  induction hn : v.val using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hv
    subst hn
    by_cases h0 : v.val = 0
    · have : v = 0 := Fin.ext h0
      rw [this]
      exact hπ.map_zero
    · obtain ⟨i, hik, hlt⟩ := exists_bit_lt ⟨k, by omega⟩ v hv h0
      have hwk : (xr v (bv i)).val < 2 ^ k := by
        rw [xr_val, bv_val]
        exact Nat.xor_lt_two_pow hv (Nat.pow_lt_pow_right (by norm_num) hik)
      have e : v = xr (xr v (bv i)) (bv i) := (xr_xr_cancel v (bv i)).symm
      rw [e, hπ.1, ih _ hlt (xr v (bv i)) rfl hwk, hfix i hik]

theorem eq_one_of_fix_bv {π : Equiv.Perm (Fin 64)} (hπ : IsIsom π)
    (hfix : ∀ i : Fin 6, π (bv i) = bv i) : π = 1 :=
  Equiv.ext fun v =>
    fix_of_fix_bv hπ le_rfl (fun i _ => hfix i) v (lt_of_lt_of_eq v.2 (by norm_num))

@[expose] def prodFrom (k : ℕ) : List (Array ℕ) :=
  (q47Trans.drop k).foldr (fun T acc => T.flatMap fun t => acc.map fun a => compA 64 t a)
    [idA 64]

theorem prodFrom_zero : prodFrom 0 = oAll := rfl

theorem transCheckO_parts (h : transCheckO = true) :
    q47Trans.length = 6 ∧ ∀ k < 6,
      (∀ t ∈ q47Trans[k]!, isomCheck t = true ∧ ∀ i < k, t[2 ^ i]! = 2 ^ i) ∧
      ∀ x < 64, admK k x = true → ∃ t ∈ q47Trans[k]!, t[2 ^ k]! = x := by
  simp only [transCheckO, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  refine ⟨h.1, fun k hk => ⟨fun t ht => ?_, fun x hx hadm => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := (h.2 k hk).1 t ht
    exact ⟨h1, fun i hi => by simpa using h2 i hi⟩
  · rcases (h.2 k hk).2 x hx with h3 | ⟨t, ht, e⟩
    · rw [h3] at hadm
      exact absurd hadm (by decide)
    · exact ⟨t, ht, by simpa using e⟩

theorem prodFrom_succ (h : transCheckO = true) {k : ℕ} (hk : k < 6) :
    prodFrom k = q47Trans[k]!.flatMap fun t => (prodFrom (k + 1)).map fun a => compA 64 t a := by
  have hlen := (transCheckO_parts h).1
  rw [prodFrom, List.drop_eq_getElem_cons (by omega), List.foldr_cons, getElem!_pos q47Trans k
    (by omega)]
  rfl

theorem prodFrom_six (h : transCheckO = true) : prodFrom 6 = [idA 64] := by
  have hlen := (transCheckO_parts h).1
  rw [prodFrom, List.drop_of_length_le (by omega)]
  rfl

theorem admK_of_isom {π : Equiv.Perm (Fin 64)} (hπ : IsIsom π) {k : ℕ} (hk : k < 6)
    (hfix : ∀ i : Fin 6, i.val < k → π (bv i) = bv i) :
    admK k (π (bv ⟨k, hk⟩)).val = true := by
  have hfixv := fix_of_fix_bv hπ hk.le hfix
  simp only [admK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨?_, ?_⟩, fun i hi => ?_⟩
  · by_contra hc
    push Not at hc
    have h1 := hfixv _ hc
    have h2 : bv ⟨k, hk⟩ = π (bv ⟨k, hk⟩) := π.injective (by rw [h1])
    rw [← h2, bv_val] at hc
    exact lt_irrefl _ hc
  · have := hπ.2 (bv ⟨k, hk⟩)
    simpa [qv, bv_val] using this
  · have hi6 : i < 6 := by omega
    have e := hπ.1 (bv ⟨i, hi6⟩) (bv ⟨k, hk⟩)
    rw [hfix ⟨i, hi6⟩ hi] at e
    have := hπ.2 (xr (bv ⟨i, hi6⟩) (bv ⟨k, hk⟩))
    rw [e] at this
    simpa [qv, xr_val, bv_val] using this

theorem exists_mem_prodFrom (h : transCheckO = true) :
    ∀ m k, k + m = 6 → ∀ π : Equiv.Perm (Fin 64), IsIsom π →
      (∀ i : Fin 6, i.val < k → π (bv i) = bv i) → ∃ t ∈ prodFrom k, Rep 64 t π := by
  intro m
  induction m with
  | zero =>
    intro k hk π hπ hfix
    have hk6 : k = 6 := by omega
    subst hk6
    have : π = 1 := eq_one_of_fix_bv hπ (fun i => hfix i i.2)
    rw [this, prodFrom_six h]
    exact ⟨idA 64, List.mem_singleton_self _, rep_idA⟩
  | succ m ih =>
    intro k hkm π hπ hfix
    have hk6 : k < 6 := by omega
    obtain ⟨-, hparts⟩ := transCheckO_parts h
    obtain ⟨hT, hcov⟩ := hparts k hk6
    obtain ⟨t, ht, htx⟩ := hcov _ (π (bv ⟨k, hk6⟩)).2 (admK_of_isom hπ hk6 hfix)
    obtain ⟨hti, htfix⟩ := hT t ht
    have hτ := mem_oV_of_isomCheck hti
    have rt := rep_of_validA (isomCheck_parts hti).1
    set τ := permOfArr 64 t with hτdef
    have hτfix : ∀ i : Fin 6, i.val < k → τ (bv i) = bv i := fun i hi => Fin.ext (by
      rw [← rt.apply (bv i).2, bv_val]
      exact htfix i.val hi)
    have hτk : τ (bv ⟨k, hk6⟩) = π (bv ⟨k, hk6⟩) := Fin.ext (by
      rw [← rt.apply (bv ⟨k, hk6⟩).2, bv_val]
      exact htx)
    have hπ' : τ⁻¹ * π ∈ oV := oV.mul_mem (oV.inv_mem hτ) (mem_oV.mpr hπ)
    obtain ⟨t', ht', hrt'⟩ := ih (k + 1) (by omega) (τ⁻¹ * π) hπ' (fun i hi => by
      rcases Nat.lt_or_ge i.val k with hik | hik
      · rw [Equiv.Perm.mul_apply, hfix i hik, Equiv.Perm.inv_eq_iff_eq, hτfix i hik]
      · have : i = ⟨k, hk6⟩ := Fin.ext (show i.val = k by omega)
        rw [this, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, hτk])
    refine ⟨compA 64 t t', ?_, ?_⟩
    · rw [prodFrom_succ h hk6]
      exact List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨t', ht', rfl⟩⟩
    · have := rep_compA rt hrt'
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at this

theorem exists_mem_oAll (h : transCheckO = true) {π : Equiv.Perm (Fin 64)} (hπ : π ∈ oV) :
    ∃ t ∈ oAll, Rep 64 t π := by
  rw [← prodFrom_zero]
  exact exists_mem_prodFrom h 6 0 rfl π hπ (fun i hi => absurd hi (Nat.not_lt_zero _))

end CFSG.ComponentClassification.AS81.Q47
