module

public import CFSG.LieType.Universal.Unitary.BinaryModel.Weight
public import CFSG.LieType.SpecialLinear.CurtisDatum.Torus

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) {F : Type} [Field F] {f : ℕ} {k : Type} [Field k]

@[expose] noncomputable def slChiEps (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1)))
    (g : SpecialLinearGroup (Fin (m + 1)) F) : k :=
  φ (∏ a, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a ^ bExp ε a)

theorem slChiEps_mul (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1)))
    {g h : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ ⨆ s, torus m F s) (hh : h ∈ ⨆ s, torus m F s) :
    slChiEps m φ ε (g * h) = slChiEps m φ ε g * slChiEps m φ ε h := by
  have hdg := ((mem_iSup_torus_iff m F).mp hg).diagonal_diag
  have hdh := ((mem_iSup_torus_iff m F).mp hh).diagonal_diag
  have hmat : (↑(g * h) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (fun a => (↑g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a *
        (↑h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hdg, ← hdh, diagonal_mul_diagonal]
    simp only [diagonal_apply_eq]
  simp only [slChiEps, hmat, diagonal_apply_eq, mul_pow, Finset.prod_mul_distrib, map_mul]

theorem slChiEps_one (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1))) :
    slChiEps m φ ε 1 = 1 := by
  simp [slChiEps]

theorem slChiEps_hdiag (φ : F →+* k) (ε : Fin f → Finset (Fin (m + 1)))
    (s : Fin m) (u : Fˣ) :
    slChiEps m φ ε (hdiag m F s u) = φ (u : F) ^ bDigit ε s.succ := by
  have hpq : (s.castSucc : Fin (m + 1)) ≠ s.succ := Fin.castSucc_lt_succ.ne
  have hmat : (↑(hdiag m F s u) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (fun r => if r = s.castSucc then (u : F) else
        if r = s.succ then ((u⁻¹ : Fˣ) : F) else 1) := by
    rw [hdiag, SpecialLinearGroup.diag2nUnit_coe]
  have hprod : (∏ a, (↑(hdiag m F s u) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a ^
      bExp ε a) = (u : F) ^ bExp ε s.castSucc *
        (((u⁻¹ : Fˣ) : F)) ^ bExp ε s.succ := by
    rw [hmat]
    simp only [diagonal_apply_eq]
    rw [← Finset.prod_subset (Finset.subset_univ ({s.castSucc, s.succ} :
      Finset (Fin (m + 1))))]
    · rw [Finset.prod_pair hpq]
      simp [Ne.symm hpq]
    · intro a _ ha
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      rw [if_neg ha.1, if_neg ha.2, one_pow]
  have hcombine : (u : F) ^ bExp ε s.castSucc *
      (((u⁻¹ : Fˣ) : F)) ^ bExp ε s.succ = (u : F) ^ bDigit ε s.succ := by
    have hu : (u : F) ≠ 0 := u.ne_zero
    rw [bExp_eq_add ε (a := s.castSucc) (b := s.succ) (by simp)]
    simp only [Units.val_inv_eq_inv_val, inv_pow, pow_add]
    rw [mul_assoc, mul_comm ((u : F) ^ bDigit ε s.succ) (((u : F) ^ bExp ε s.succ)⁻¹),
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]
  unfold slChiEps
  rw [hprod, hcombine, map_pow]

theorem torus_eq_closure_range_hdiag (s : Fin m) :
    torus m F s = Subgroup.closure (Set.range (hdiag m F s)) := by
  have hfun : ∀ t : Fˣ,
      (fun r : Fin (m + 1) => if r = s.castSucc then (t : F) else
        if r = s.succ then ((t⁻¹ : Fˣ) : F) else 1) =
      Function.update (Function.update (1 : Fin (m + 1) → F) s.castSucc (t : F))
        s.succ ((t⁻¹ : Fˣ) : F) := by
    intro t
    funext r
    by_cases h1 : r = s.castSucc
    · subst r
      have h2 : s.castSucc ≠ s.succ := Fin.castSucc_lt_succ.ne
      rw [Function.update_of_ne h2, Function.update_self]
      simp
    · by_cases h2 : r = s.succ
      · subst r
        rw [Function.update_self]
        simp [h1]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1]
        simp [h1, h2]
  rw [torus]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    rw [ht, hdiag, SpecialLinearGroup.diag2nUnit_coe]
    congr 1
    exact hfun t
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    rw [hdiag, SpecialLinearGroup.diag2nUnit_coe]
    congr 1
    exact hfun t

theorem eq_on_H_of_eq_hdiag {χ χ' : SpecialLinearGroup (Fin (m + 1)) F → k}
    (hχ : ∀ a ∈ ⨆ s, torus m F s, ∀ b ∈ ⨆ s, torus m F s, χ (a * b) = χ a * χ b)
    (hχ' : ∀ a ∈ ⨆ s, torus m F s, ∀ b ∈ ⨆ s, torus m F s, χ' (a * b) = χ' a * χ' b)
    (h1 : χ 1 = 1) (h1' : χ' 1 = 1)
    (h : ∀ (s : Fin m) (u : Fˣ), χ (hdiag m F s u) = χ' (hdiag m F s u)) :
    ∀ g ∈ ⨆ s, torus m F s, χ g = χ' g := by
  intro g hg
  exact Subgroup.iSup_induction' (fun s => torus m F s) (C := fun x _ => χ x = χ' x)
    (fun s x hx => by
      rw [torus_eq_closure_range_hdiag] at hx
      refine Subgroup.closure_induction (p := fun x _ => χ x = χ' x) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨u, rfl⟩
        exact h s u
      · exact h1.trans h1'.symm
      · intro a b ha hb iha ihb
        have haH : a ∈ ⨆ s, torus m F s := Subgroup.mem_iSup_of_mem s (by
          rwa [← torus_eq_closure_range_hdiag] at ha)
        have hbH : b ∈ ⨆ s, torus m F s := Subgroup.mem_iSup_of_mem s (by
          rwa [← torus_eq_closure_range_hdiag] at hb)
        rw [hχ a haH b hbH, hχ' a haH b hbH, iha, ihb]
      · intro a ha iha
        have haH : a ∈ ⨆ s, torus m F s := Subgroup.mem_iSup_of_mem s (by
          rwa [← torus_eq_closure_range_hdiag] at ha)
        have hainvH : a⁻¹ ∈ ⨆ s, torus m F s := inv_mem haH
        have hmulχ : χ a * χ a⁻¹ = 1 := by
          rw [← hχ a haH a⁻¹ hainvH, mul_inv_cancel, h1]
        have hmulχ' : χ' a * χ' a⁻¹ = 1 := by
          rw [← hχ' a haH a⁻¹ hainvH, mul_inv_cancel, h1']
        have hane : χ a ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hmulχ
          exact zero_ne_one hmulχ
        have hEq : χ a * χ a⁻¹ = χ a * χ' a⁻¹ := by
          calc
            χ a * χ a⁻¹ = 1 := hmulχ
            _ = χ' a * χ' a⁻¹ := hmulχ'.symm
            _ = χ a * χ' a⁻¹ := by rw [iha]
        exact mul_left_cancel₀ hane hEq)
    (h1.trans h1'.symm)
    (fun a b ha hb iha ihb => by
      rw [hχ a ha b hb, hχ' a ha b hb, iha, ihb])
    hg

end

end CFSG.LieType.SpecialLinear
