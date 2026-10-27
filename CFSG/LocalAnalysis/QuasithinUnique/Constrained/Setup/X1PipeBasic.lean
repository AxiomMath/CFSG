module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

section Tables

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem eq_of_tab_eq [FaithfulSMul Γ (Fin n)] {x y : Γ} (h : tab n x = tab n y) : x = y := by
  have hact : ∀ p, act n x p = act n y p := fun p => by simp only [act, h]
  have h1 : x⁻¹ * y = 1 := by
    apply base_of_faithful (n := n)
    intro b hb
    have hb' : b < n := List.mem_range.mp hb
    rw [act_mul _ _ hb', ← hact b, ← act_mul _ _ hb', inv_mul_cancel, act_one hb']
  exact inv_mul_eq_one.mp h1

theorem tab_length (g : Γ) : (tab n g).length = n := by simp [tab]

theorem getD_toList_eq (ta : Array ℕ) (l : List ℕ) (h : l = ta.toList) (p : ℕ) :
    l.getD p 0 = ta.getD p 0 := by
  subst h
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem tab_inv_of_inv (a : Γ) (ta tai : Array ℕ) (hta : tab n a = ta.toList)
    (hsz : tai.size = n) (hinv : ∀ q < n, tai.getD (ta.getD q 0) 0 = q) :
    tab n a⁻¹ = tai.toList := by
  apply List.ext_getElem
  · simp [tab_length, hsz]
  · intro q h1 h2
    have hq : q < n := by simpa [tab_length] using h1
    have e1 : (tab n a⁻¹)[q] = act n a⁻¹ q := by
      simp [act, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    have hlt : act n a⁻¹ q < n := act_lt _ hq
    have e2 : ta.getD (act n a⁻¹ q) 0 = q := by
      have := act_mul a a⁻¹ hq
      rw [mul_inv_cancel, act_one hq] at this
      have h3 : act n a (act n a⁻¹ q) = ta.getD (act n a⁻¹ q) 0 :=
        getD_toList_eq ta (tab n a) hta _
      rw [← h3, ← this]
    have h4 := hinv (act n a⁻¹ q) hlt
    rw [e2] at h4
    have hq' : q < tai.size := by simpa using h2
    have h5 : tai.toList[q] = tai.getD q 0 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq']
    rw [h5, h4, e1]

variable (a b : Γ) (par gen : Array ℕ)

noncomputable def treeR (i : ℕ) : Γ :=
  if _h : 0 < i ∧ par.getD i 0 < i then
    (if gen.getD i 0 = 0 then a else b) * treeR (par.getD i 0)
  else 1
termination_by i
decreasing_by exact _h.2

theorem treeR_zero : treeR a b par gen 0 = 1 := by
  rw [treeR]; simp

variable {a b par gen}

theorem treeR_succ {N i : ℕ} (hv : treeValid N par gen) (hi : i < N) (hi0 : 0 < i) :
    treeR a b par gen i = (if gen.getD i 0 = 0 then a else b) * treeR a b par gen (par.getD i 0) := by
  have := (hv.2.2 i hi hi0).1
  conv_lhs => rw [treeR]
  rw [dite_eq_left_of_eq_true (eq_true ⟨hi0, this⟩)]

theorem tab_one : tab n (1 : Γ) = List.range n := by
  apply List.ext_getElem
  · simp [tab_length]
  · intro i h1 h2
    simp [tab]

theorem tab_gen (a b : Γ) (ta tb : Array ℕ) (hta : tab n a = ta.toList) (htb : tab n b = tb.toList)
    (c : ℕ) : tab n (if c = 0 then a else b) = (if c = 0 then ta else tb).toList := by
  split_ifs <;> assumption

theorem treeTabs_spec {N : ℕ} {a b : Γ} {ta tb par gen : Array ℕ} (hta : tab n a = ta.toList)
    (htb : tab n b = tb.toList) (hv : treeValid N par gen) :
    ∀ m, m + 1 ≤ N →
      ((List.range' 1 m).foldl (treeStepT ta tb par gen) #[Array.range n]).size = m + 1 ∧
      ∀ i ≤ m, ((List.range' 1 m).foldl (treeStepT ta tb par gen) #[Array.range n])[i]! =
        (tab n (treeR a b par gen i)).toArray := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    simp [treeR_zero, tab_one]
  | succ m ih =>
    intro hm
    obtain ⟨hsz, hent⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hacc : (List.range' 1 m).foldl (treeStepT ta tb par gen) #[Array.range n] = acc
      at hsz hent
    have hpar := (hv.2.2 (m + 1) (by omega) (by omega))
    have hp : par.getD (m + 1) 0 ≤ m := by omega
    have hent' : acc.getD (par.getD (m + 1) 0) #[] =
        (tab n (treeR a b par gen (par.getD (m + 1) 0))).toArray := by
      have h1 := hent _ hp
      have h2 : par.getD (m + 1) 0 < acc.size := by omega
      rw [getElem!_pos acc _ h2] at h1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
      simpa using h1
    have hr : treeR a b par gen (m + 1) =
        (if gen.getD (m + 1) 0 = 0 then a else b) * treeR a b par gen (par.getD (m + 1) 0) :=
      treeR_succ hv (by omega) (by omega)
    have hnew : treeStepT ta tb par gen acc (1 + 1 * m) =
        acc.push (tab n (treeR a b par gen (m + 1))).toArray := by
      unfold treeStepT
      rw [show 1 + 1 * m = m + 1 by omega, hent', hr, tab_mul, tab_gen a b ta tb hta htb]
      congr 1
      apply Array.toList_inj.1
      rw [compArr_toList]
    rw [hnew]
    refine ⟨by simp [hsz], ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hlt | rfl
    · rw [getElem!_push_lt' _ _ (by omega)]
      exact hent i (by omega)
    · rw [show m + 1 = acc.size by omega]
      rw [getElem!_push_self']

theorem treeInvTabs_spec {N : ℕ} {a b : Γ} {tai tbi par gen : Array ℕ}
    (htai : tab n a⁻¹ = tai.toList) (htbi : tab n b⁻¹ = tbi.toList) (hv : treeValid N par gen) :
    ∀ m, m + 1 ≤ N →
      ((List.range' 1 m).foldl (treeStepU tai tbi par gen) #[Array.range n]).size = m + 1 ∧
      ∀ i ≤ m, ((List.range' 1 m).foldl (treeStepU tai tbi par gen) #[Array.range n])[i]! =
        (tab n (treeR a b par gen i)⁻¹).toArray := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    simp [treeR_zero, tab_one]
  | succ m ih =>
    intro hm
    obtain ⟨hsz, hent⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hacc : (List.range' 1 m).foldl (treeStepU tai tbi par gen) #[Array.range n] = acc
      at hsz hent
    have hpar := (hv.2.2 (m + 1) (by omega) (by omega))
    have hp : par.getD (m + 1) 0 ≤ m := by omega
    have hent' : acc.getD (par.getD (m + 1) 0) #[] =
        (tab n (treeR a b par gen (par.getD (m + 1) 0))⁻¹).toArray := by
      have h1 := hent _ hp
      have h2 : par.getD (m + 1) 0 < acc.size := by omega
      rw [getElem!_pos acc _ h2] at h1
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2]
      simpa using h1
    have hr : (treeR a b par gen (m + 1))⁻¹ =
        (treeR a b par gen (par.getD (m + 1) 0))⁻¹ *
          (if gen.getD (m + 1) 0 = 0 then a else b)⁻¹ := by
      rw [treeR_succ hv (by omega) (by omega), mul_inv_rev]
    have hnew : treeStepU tai tbi par gen acc (1 + 1 * m) =
        acc.push (tab n (treeR a b par gen (m + 1))⁻¹).toArray := by
      unfold treeStepU
      rw [show 1 + 1 * m = m + 1 by omega, hent', hr, tab_mul]
      have hg : tab n (if gen.getD (m + 1) 0 = 0 then a else b)⁻¹ =
          (if gen.getD (m + 1) 0 = 0 then tai else tbi).toList := by
        split_ifs <;> assumption
      rw [hg]
      congr 1
      apply Array.toList_inj.1
      rw [compArr_toList]
    rw [hnew]
    refine ⟨by simp [hsz], ?_⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hlt | rfl
    · rw [getElem!_push_lt' _ _ (by omega)]
      exact hent i (by omega)
    · rw [show m + 1 = acc.size by omega]
      rw [getElem!_push_self']

end Tables

end CFSG.QuasithinUnique.Setup.X1
