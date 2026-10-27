module

public import CFSG.LargeExtraspecial.Setting

public section

namespace CFSG.LargeExtraspecial

open Matrix

namespace S2

variable {m : ℕ}

abbrev elemT {i j : Fin m} (h : i ≠ j) : SpecialLinearGroup (Fin m) (ZMod 2) :=
  SpecialLinearGroup.transvection h 1

theorem transvection_comm_matrix {i j k : Fin m} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (transvection i j (1 : ZMod 2)) * transvection j k 1 * transvection i j 1 *
      transvection j k 1 = transvection i k 1 := by
  simp only [transvection]
  have h1 : single i j (1 : ZMod 2) * single j k 1 = single i k 1 := by
    rw [single_mul_single_same, mul_one]
  have h2 : single j k (1 : ZMod 2) * single i j 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hik.symm _
  have h3 : single i j (1 : ZMod 2) * single i j 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hij.symm _
  have h4 : single j k (1 : ZMod 2) * single j k 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hjk.symm _
  have h5 : single i k (1 : ZMod 2) * single i j 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ hik.symm _
  have h6 : single i k (1 : ZMod 2) * single j k 1 = 0 :=
    single_mul_single_of_ne _ _ _ _ (Ne.symm hjk) _
  have h7 : ∀ a b : Fin m, single a b (1 : ZMod 2) + single a b 1 = 0 := fun a b => by
    rw [← single_add, show (1 : ZMod 2) + 1 = 0 by decide, single_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h1, h2, h3, h4, h5,
    h6, add_zero]
  have e : ∀ (A B C : Matrix (Fin m) (Fin m) (ZMod 2)), A + B = C + (single i j 1 + single i j 1) +
      (single j k 1 + single j k 1) + (single i k 1 + single i k 1) → A + B = C := by
    intro A B C h
    rw [h, h7, h7, h7, add_zero, add_zero, add_zero]
  apply e
  abel

theorem elemT_comm {i j k : Fin m} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    elemT hij * elemT hjk * elemT hij * elemT hjk = elemT hik := by
  ext a b
  have := congrFun (congrFun (transvection_comm_matrix hij hjk hik) a) b
  simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, transvection] using this

theorem closure_elemT_eq_top (hm : 2 ≤ m) :
    Subgroup.closure {t | ∃ (i j : Fin m) (h : i ≠ j), t = elemT h} = ⊤ := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [eq_top_iff]
  intro A _
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun B => B ∈ Subgroup.closure
    {t | ∃ (i j : Fin m) (h : i ≠ j), t = elemT h}) A (fun i j hij c hc => ?_) (fun i j hij a => ?_)
    (fun B C hB hC => mul_mem hB hC)
  · have hc1 : c = 1 := by
      revert c
      decide
    subst hc1
    have : SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      ext a b
      simp [SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply, Matrix.one_apply]
    rw [this]
    exact one_mem _
  · rcases (show a = 0 ∨ a = 1 by revert a; decide) with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨i, j, hij, rfl⟩

variable {n : ℕ}

theorem fin_ne_add_one (i : Fin (n + 2)) : i ≠ i + 1 := by
  intro h
  have h1 : (1 : Fin (n + 2)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this.symm
  exact absurd (congrArg Fin.val h1) (by simp)

@[expose] def cycT (i : Fin (n + 2)) : SpecialLinearGroup (Fin (n + 2)) (ZMod 2) :=
  elemT (fin_ne_add_one i)

theorem fin_ofNat_succ (d : ℕ) :
    Fin.ofNat (n + 2) (d + 1 + 1) = Fin.ofNat (n + 2) (d + 1) + 1 := by
  ext
  simp only [Fin.val_ofNat, Fin.val_add, Fin.val_one]
  rw [Nat.mod_add_mod]

theorem closure_cycT_eq_top :
    Subgroup.closure (Set.range (cycT (n := n))) = ⊤ := by
  set H := Subgroup.closure (Set.range (cycT (n := n))) with hH
  have hstep : ∀ d : ℕ, ∀ i : Fin (n + 2), d < n + 1 →
      ∀ h : i ≠ i + Fin.ofNat (n + 2) (d + 1), elemT h ∈ H := by
    intro d
    induction d with
    | zero =>
      intro i _ h
      have : elemT h = cycT i := by
        unfold cycT
        congr 1
      rw [this]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    | succ d ih =>
      intro i hd h
      set k := i + Fin.ofNat (n + 2) (d + 1) with hk
      have hik : i ≠ k := by
        intro h'
        have := congrArg (fun x => x - i) h'
        simp only [sub_self, hk, add_sub_cancel_left] at this
        have h2 := congrArg Fin.val this
        rw [Fin.val_ofNat, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h2
        omega
      have hkj : k ≠ k + 1 := fin_ne_add_one k
      have hj : k + 1 = i + Fin.ofNat (n + 2) (d + 1 + 1) := by
        rw [hk, add_assoc, fin_ofNat_succ]
      have hij : i ≠ k + 1 := by rw [hj]; exact h
      have e := elemT_comm hik hkj hij
      have h1 : elemT hik ∈ H := ih i (by omega) hik
      have h2 : elemT hkj ∈ H := by
        have : elemT hkj = cycT k := rfl
        rw [this]
        exact Subgroup.subset_closure ⟨k, rfl⟩
      have h3 : elemT h = elemT hij := by
        congr 1
        exact hj.symm
      rw [h3, ← e]
      exact mul_mem (mul_mem (mul_mem h1 h2) h1) h2
  rw [eq_top_iff, ← closure_elemT_eq_top (m := n + 2) (by omega), Subgroup.closure_le]
  rintro _ ⟨i, j, hij, rfl⟩
  set d := (j - i).val with hd
  have hd0 : d ≠ 0 := by
    intro h0
    have : j - i = 0 := Fin.ext (by rw [Fin.val_zero]; exact h0)
    exact hij (sub_eq_zero.mp this).symm
  have hdlt : d < n + 2 := (j - i).isLt
  have hjd : j = i + Fin.ofNat (n + 2) (d - 1 + 1) := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd0), hd, Fin.ofNat_val_eq_self,
      add_sub_cancel]
  have h' : i ≠ i + Fin.ofNat (n + 2) (d - 1 + 1) := by rw [← hjd]; exact hij
  have : elemT hij = elemT h' := by
    congr 1
  rw [this]
  exact hstep (d - 1) i (by omega) h'

end S2

end CFSG.LargeExtraspecial
