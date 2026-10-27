module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMonomial
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherInvariant

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def IsMonomial (M : Matrix (Fin n) (Fin n) K) (w : Equiv.Perm (Fin n)) : Prop :=
  ∃ c : Fin n → Kˣ, ∀ j, M *ᵥ Pi.single j 1 = (c j : K) • Pi.single (w j) 1

theorem IsMonomial.mul {M M' : Matrix (Fin n) (Fin n) K} {w w' : Equiv.Perm (Fin n)}
    (h : IsMonomial M w) (h' : IsMonomial M' w') : IsMonomial (M * M') (w * w') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨fun j => c' j * c (w' j), fun j => ?_⟩
  rw [← mulVec_mulVec, hc', mulVec_smul, hc, smul_smul, Equiv.Perm.mul_apply, Units.val_mul]

theorem IsMonomial.inv {g : SpecialLinearGroup (Fin n) K} {w : Equiv.Perm (Fin n)}
    (h : IsMonomial (g : Matrix (Fin n) (Fin n) K) w) :
    IsMonomial ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) w⁻¹ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun k => (c (w⁻¹ k))⁻¹, fun k => ?_⟩
  have h1 := hc (w⁻¹ k)
  rw [perm_apply_inv] at h1
  have hinv : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  have h2 : (Pi.single (w⁻¹ k) 1 : Fin n → K) = (c (w⁻¹ k) : K) •
      (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single k 1) := by
    rw [← mulVec_smul, ← h1, mulVec_mulVec, hinv, one_mulVec]
  rw [h2, smul_smul, Units.inv_mul, one_smul]

theorem isMonomial_signedPermMatrix (w : Equiv.Perm (Fin n)) :
    IsMonomial (signedPermMatrix n K w) w := by
  classical
  set ε : Fin n → K := fun a => if (a : ℕ) = 0 then ((Equiv.Perm.sign w : ℤ) : K) else 1 with hε
  have hε0 : ∀ a, ε a ≠ 0 := fun a => by
    simp only [hε]
    split_ifs
    · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
    · exact one_ne_zero
  refine ⟨fun j => Units.mk0 (ε (w j)) (hε0 _), fun j => ?_⟩
  rw [signedPermMatrix, ← mulVec_mulVec, permMatrix_mulVec_single, Units.val_mk0]
  ext a
  simp only [mulVec_diagonal, Pi.single_apply, Pi.smul_apply, smul_eq_mul, hε]
  split_ifs with h1 h2 h2 <;> simp_all

theorem isMonomial_reflection (i : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    IsMonomial (reflectionMatrix n K i) (adjSwap n i) := by
  classical
  set d : Fin n → K := fun b : Fin n => if (b : ℕ) = i then -1 else 1 with hd
  have hd0 : ∀ b, d b ≠ 0 := fun b => by
    simp only [hd]
    split_ifs
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  refine ⟨fun j => Units.mk0 (d j) (hd0 j), fun j => ?_⟩
  rw [reflectionMatrix_eq i hi hin, ← mulVec_mulVec, diagonal_mulVec_single, mul_one,
    adjSwap_of_lt hi hin, Units.val_mk0]
  rw [show (Pi.single j (d j) : Fin n → K) = d j • Pi.single j 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], mulVec_smul, permMatrix_mulVec_single]

theorem IsMonomial.exists_diagonal {M M' : SpecialLinearGroup (Fin n) K}
    {w : Equiv.Perm (Fin n)} (h : IsMonomial (M : Matrix (Fin n) (Fin n) K) w)
    (h' : IsMonomial (M' : Matrix (Fin n) (Fin n) K) w) :
    ∃ D ∈ upperTriangular n K, M = M' * D := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  obtain ⟨D, hD, -, hMD⟩ := (monomial_root_transport (K := K) (n := n)).2.1 M M' w c c' hc hc'
  exact ⟨D, hD, hMD⟩

theorem transvection_mem_upperTriangular {a b : Fin n} (h : a < b) (t : K) :
    SpecialLinearGroup.transvection h.ne t ∈ upperTriangular n K :=
  unitriangular_le_upperTriangular n K (transvection_mem_unitriangular h t)

theorem adjSwap_inv (i : ℕ) : (adjSwap n i)⁻¹ = adjSwap n i :=
  inv_eq_of_mul_eq_one_right (adjSwap_mul_self i)

theorem reduced_word_extraction (A : Subgroup (SpecialLinearGroup (Fin n) K)) :
    ∀ (l : List ℕ) (w : Equiv.Perm (Fin n)), upperTriangular n K ≤ A →
      (∀ b ∈ upperTriangular n K,
        signedPermutation n K w * b * (signedPermutation n K w)⁻¹ ∈ A) →
      IsReducedWord w l → ∀ i ∈ l, ∀ (hi : 1 ≤ i) (hin : i < n), reflection n K i hi hin ∈ A := by
  intro l
  induction l with
  | nil => intro _ _ _ _ i hi; exact absurd hi List.not_mem_nil
  | cons i l ih =>
    intro w hB hwB hred
    obtain ⟨hi, hin, hdesc, hred'⟩ := (symmetric_group_descents w).2.2 i l hred
    set x : Fin n := ⟨i - 1, by omega⟩ with hx
    set y : Fin n := ⟨i, hin⟩ with hy
    have hxy : x < y := by rw [Fin.lt_def]; simp [hx, hy]; omega
    have hri : reflection n K i hi hin ∈ A := by
      rw [(monomial_root_transport (K := K) (n := n)).2.2 i hi hin]
      obtain ⟨c, hc⟩ := isMonomial_signedPermMatrix (K := K) w
      set a := w⁻¹ y
      set b := w⁻¹ x
      have hab : a < b := hdesc
      have hwa : w a = y := perm_apply_inv w y
      have hwb : w b = x := perm_apply_inv w x
      have hlow : SpecialLinearGroup.transvection (i := y) (j := x) hxy.ne' 1 ∈ A := by
        have h1 := hwB _ (transvection_mem_upperTriangular hab ((c b : K) * (c a : K)⁻¹))
        rw [monomial_conj_transvection (M := signedPermutation n K w) hc hab.ne] at h1
        convert h1 using 1
        apply Subtype.ext
        simp only [SpecialLinearGroup.transvection_coe, hwa, hwb]
        congr 1
        field_simp [(c a).ne_zero, (c b).ne_zero]
      exact mul_mem (mul_mem (hB (transvection_mem_upperTriangular hxy (-1))) hlow)
        (hB (transvection_mem_upperTriangular hxy (-1)))
    have hvB : ∀ b ∈ upperTriangular n K, signedPermutation n K (adjSwap n i * w) * b *
        (signedPermutation n K (adjSwap n i * w))⁻¹ ∈ A := by
      have hmono : IsMonomial (((reflection n K i hi hin)⁻¹ * signedPermutation n K w :
          SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (adjSwap n i * w) := by
        rw [SpecialLinearGroup.coe_mul, ← adjSwap_inv]
        exact (IsMonomial.inv (isMonomial_reflection (K := K) i hi hin)).mul
          (isMonomial_signedPermMatrix w)
      obtain ⟨D, hD, hMD⟩ := hmono.exists_diagonal (M' := signedPermutation n K (adjSwap n i * w))
        (isMonomial_signedPermMatrix (K := K) (adjSwap n i * w))
      intro b hb
      have hv : signedPermutation n K (adjSwap n i * w) =
          (reflection n K i hi hin)⁻¹ * signedPermutation n K w * D⁻¹ := by
        rw [hMD, mul_inv_cancel_right]
      rw [hv]
      have h1 := hwB _ (mul_mem (mul_mem (inv_mem hD) hb) hD)
      have h2 := mul_mem (mul_mem (inv_mem hri) h1) hri
      convert h2 using 1
      group
    intro j hj hj1 hjn
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hri
    · exact ih _ hB hvB hred' j hj hj1 hjn

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
