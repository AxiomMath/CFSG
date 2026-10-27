module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public section

namespace CFSG.QuasithinUnique.Id2519.USp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Matrices

variable {F : Type} [Field F]

@[expose] def aMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0] !![1, 0; 0, 0] !![1, 0; 0, 1]

@[expose] def bMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, 0; 0, 0] !![1, 1; 0, 1] !![1, 0; 0, 1] !![0, 1; 1, 0]

theorem one_add_one_eq_zero [CharP F 2] : (1 : F) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharTwo.two_eq_zero

theorem aMat_cube [CharP F 2] :
    aMat * aMat * aMat = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have h2 := one_add_one_eq_zero (F := F)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2]

theorem bMat_pow_five [CharP F 2] :
    bMat * bMat * bMat * bMat * bMat = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have h2 := one_add_one_eq_zero (F := F)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2]

theorem aMat_symp [CharP F 2] :
    (aMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F * aMat = formJ 2 F := by
  have h2 := one_add_one_eq_zero (F := F)
  have h1 : (-1 : F) = 1 := CharTwo.neg_eq 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [aMat, formJ, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h1]

theorem bMat_symp [CharP F 2] :
    (bMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F * bMat = formJ 2 F := by
  have h2 := one_add_one_eq_zero (F := F)
  have h1 : (-1 : F) = 1 := CharTwo.neg_eq 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [bMat, formJ, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h1]

@[expose] def aGL [CharP F 2] : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨aMat, aMat * aMat, by rw [← mul_assoc]; exact aMat_cube, aMat_cube⟩

@[expose] def bGL [CharP F 2] : GL (Fin 2 ⊕ Fin 2) F :=
  ⟨bMat, bMat * bMat * bMat * bMat, by simp only [← mul_assoc]; exact bMat_pow_five,
    bMat_pow_five⟩

@[expose] def aS [CharP F 2] : StatedSp 2 F :=
  ⟨aGL, SymplecticTorusWeyl.mem_statedSp_iff.mpr aMat_symp⟩

@[expose] def bS [CharP F 2] : StatedSp 2 F :=
  ⟨bGL, SymplecticTorusWeyl.mem_statedSp_iff.mpr bMat_symp⟩

theorem aS_pow_three [CharP F 2] : (aS : StatedSp 2 F) ^ 3 = 1 := by
  rw [pow_three, ← mul_assoc]
  exact Subtype.ext (Units.ext aMat_cube)

theorem bS_pow_five [CharP F 2] : (bS : StatedSp 2 F) ^ 5 = 1 := by
  have h : (bS : StatedSp 2 F) * bS * bS * bS * bS = 1 := Subtype.ext (Units.ext bMat_pow_five)
  calc (bS : StatedSp 2 F) ^ 5 = bS * bS * bS * bS * bS := by simp [pow_succ]
    _ = 1 := h

theorem map_aMat (φ : F →+* F) : (aMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map φ = aMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [aMat]

theorem map_bMat (φ : F →+* F) : (bMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map φ = bMat := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [bMat]

end Matrices

section Commutant

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_commute_aMat_bMat (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hA : M * aMat = aMat * M) (hB : M * bMat = bMat * M)
    (hJ : Mᵀ * formJ 2 F * M = formJ 2 F) : M = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hA00 : M (Sum.inl 0) (Sum.inr 0) = M (Sum.inr 0) (Sum.inl 0) := by
    have h := congrFun (congrFun hA (Sum.inl 0)) (Sum.inl 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA01 : M (Sum.inl 0) (Sum.inl 1) = M (Sum.inr 0) (Sum.inl 1) := by
    have h := congrFun (congrFun hA (Sum.inl 0)) (Sum.inl 1)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA02 : M (Sum.inl 0) (Sum.inl 0) + M (Sum.inl 0) (Sum.inr 0) = M (Sum.inr 0) (Sum.inr 0) := by
    have h := congrFun (congrFun hA (Sum.inl 0)) (Sum.inr 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA03 : M (Sum.inl 0) (Sum.inr 1) = M (Sum.inr 0) (Sum.inr 1) := by
    have h := congrFun (congrFun hA (Sum.inl 0)) (Sum.inr 1)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA10 : M (Sum.inl 1) (Sum.inr 0) = M (Sum.inl 1) (Sum.inl 0) := by
    have h := congrFun (congrFun hA (Sum.inl 1)) (Sum.inl 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA12 : M (Sum.inl 1) (Sum.inl 0) + M (Sum.inl 1) (Sum.inr 0) = M (Sum.inl 1) (Sum.inr 0) := by
    have h := congrFun (congrFun hA (Sum.inl 1)) (Sum.inr 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA21 : M (Sum.inr 0) (Sum.inl 1) = M (Sum.inl 0) (Sum.inl 1) + M (Sum.inr 0) (Sum.inl 1) := by
    have h := congrFun (congrFun hA (Sum.inr 0)) (Sum.inl 1)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination (-1 : F) * h
  have hA23 : M (Sum.inr 0) (Sum.inr 1) = M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 0) (Sum.inr 1) := by
    have h := congrFun (congrFun hA (Sum.inr 0)) (Sum.inr 1)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination (-1 : F) * h
  have hA30 : M (Sum.inr 1) (Sum.inr 0) = M (Sum.inr 1) (Sum.inl 0) := by
    have h := congrFun (congrFun hA (Sum.inr 1)) (Sum.inl 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hA32 : M (Sum.inr 1) (Sum.inl 0) + M (Sum.inr 1) (Sum.inr 0) = M (Sum.inr 1) (Sum.inr 0) := by
    have h := congrFun (congrFun hA (Sum.inr 1)) (Sum.inr 0)
    simp [aMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hB01 : M (Sum.inl 0) (Sum.inr 1) = M (Sum.inl 0) (Sum.inl 1) + M (Sum.inr 0) (Sum.inl 1) + M (Sum.inr 1) (Sum.inl 1) := by
    have h := congrFun (congrFun hB (Sum.inl 0)) (Sum.inl 1)
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hB03 : M (Sum.inl 0) (Sum.inl 0) + M (Sum.inl 0) (Sum.inl 1) + M (Sum.inl 0) (Sum.inr 0) = M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1) := by
    have h := congrFun (congrFun hB (Sum.inl 0)) (Sum.inr 1)
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hB11 : M (Sum.inl 1) (Sum.inr 1) = M (Sum.inr 1) (Sum.inl 1) := by
    have h := congrFun (congrFun hB (Sum.inl 1)) (Sum.inl 1)
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hB13 : M (Sum.inl 1) (Sum.inl 0) + M (Sum.inl 1) (Sum.inl 1) + M (Sum.inl 1) (Sum.inr 0) = M (Sum.inr 1) (Sum.inr 1) := by
    have h := congrFun (congrFun hB (Sum.inl 1)) (Sum.inr 1)
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have hB23 : M (Sum.inr 0) (Sum.inl 0) + M (Sum.inr 0) (Sum.inl 1) + M (Sum.inr 0) (Sum.inr 0) = M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1) := by
    have h := congrFun (congrFun hB (Sum.inr 0)) (Sum.inr 1)
    simp [bMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h
    linear_combination h
  have e01 : M (Sum.inl 0) (Sum.inl 1) = 0 := by
    linear_combination hA21 + (M (Sum.inl 0) (Sum.inl 1)) * h2
  have e02 : M (Sum.inl 0) (Sum.inr 0) = 0 := by
    linear_combination hA00 + hA01 + hA02 + hA03 + hA23 + hB03 + hB23 + (- M (Sum.inl 0) (Sum.inl 0) - M (Sum.inl 0) (Sum.inl 1) - M (Sum.inl 0) (Sum.inr 0) + M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1)) * h2
  have e03 : M (Sum.inl 0) (Sum.inr 1) = 0 := by
    linear_combination hA23 + (M (Sum.inl 0) (Sum.inr 1)) * h2
  have e10 : M (Sum.inl 1) (Sum.inl 0) = 0 := by
    linear_combination hA12
  have e12 : M (Sum.inl 1) (Sum.inr 0) = 0 := by
    linear_combination hA10 + hA12
  have e13 : M (Sum.inl 1) (Sum.inr 1) = 0 := by
    linear_combination hA01 + hA23 + hB01 + hB11 + (M (Sum.inr 0) (Sum.inl 1) + M (Sum.inr 1) (Sum.inl 1)) * h2
  have e20 : M (Sum.inr 0) (Sum.inl 0) = 0 := by
    linear_combination hA01 + hA02 + hA03 + hA23 + hB03 + hB23 + (- M (Sum.inl 0) (Sum.inl 0) - M (Sum.inl 0) (Sum.inl 1) - M (Sum.inl 0) (Sum.inr 0) + M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1)) * h2
  have e21 : M (Sum.inr 0) (Sum.inl 1) = 0 := by
    linear_combination hA01 + hA21 + (M (Sum.inr 0) (Sum.inl 1)) * h2
  have e23 : M (Sum.inr 0) (Sum.inr 1) = 0 := by
    linear_combination hA03 + hA23 + (M (Sum.inr 0) (Sum.inr 1)) * h2
  have e30 : M (Sum.inr 1) (Sum.inl 0) = 0 := by
    linear_combination hA32
  have e31 : M (Sum.inr 1) (Sum.inl 1) = 0 := by
    linear_combination hA01 + hA23 + hB01 + (M (Sum.inr 0) (Sum.inl 1) + M (Sum.inr 1) (Sum.inl 1)) * h2
  have e32 : M (Sum.inr 1) (Sum.inr 0) = 0 := by
    linear_combination hA30 + hA32
  have d1 : M (Sum.inl 1) (Sum.inl 1) = M (Sum.inl 0) (Sum.inl 0) := by
    linear_combination hA00 + hA01 + hA02 + hA10 + hA21 + hA23 + hB13 + hB23 + (- M (Sum.inl 0) (Sum.inl 0) - M (Sum.inl 0) (Sum.inr 0) + M (Sum.inl 0) (Sum.inr 1) - M (Sum.inl 1) (Sum.inr 0) + M (Sum.inr 1) (Sum.inr 1)) * h2
  have d2 : M (Sum.inr 0) (Sum.inr 0) = M (Sum.inl 0) (Sum.inl 0) := by
    linear_combination hA00 + hA01 + hA03 + hA23 + hB03 + hB23 + (- M (Sum.inl 0) (Sum.inl 0) - M (Sum.inl 0) (Sum.inl 1) - M (Sum.inl 0) (Sum.inr 0) + M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1)) * h2
  have d3 : M (Sum.inr 1) (Sum.inr 1) = M (Sum.inl 0) (Sum.inl 0) := by
    linear_combination hA00 + hA01 + hA02 + hA21 + hA23 + hB23 + (- M (Sum.inl 0) (Sum.inl 0) - M (Sum.inl 0) (Sum.inr 0) + M (Sum.inl 0) (Sum.inr 1) + M (Sum.inr 1) (Sum.inr 1)) * h2
  have hMdiag : ∀ i j, M i j = if i = j then M (Sum.inl 0) (Sum.inl 0) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [e01, e02, e03, e10, e12, e13, e20, e21, e23, e30, e31, e32, d1, d2, d3]
  have hc : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
    simp [formJ, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, e10, e20, e30, e32,
      d2] at h
    exact h
  have hc1 : M (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h3 : (M (Sum.inl 0) (Sum.inl 0) - 1) ^ 2 = 0 := by
      linear_combination hc + (1 - M (Sum.inl 0) (Sum.inl 0)) * h2
    have h4 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    linear_combination h4
  ext i j
  rw [hMdiag i j, hc1, Matrix.one_apply]

theorem eq_one_of_commute_aS_bS {g : StatedSp 2 F} (ha : g * aS = aS * g) (hb : g * bS = bS * g) :
    g = 1 := by
  have hJ : (spMat g)ᵀ * formJ 2 F * spMat g = formJ 2 F :=
    SymplecticTorusWeyl.mem_statedSp_iff.mp g.2
  have hM := eq_one_of_commute_aMat_bMat (spMat g) (congrArg spMat ha) (congrArg spMat hb) hJ
  exact Subtype.ext (Units.ext hM)

end Commutant

section Torus

variable {F : Type} [Field F]

theorem entry_eq_zero_of_commute_diagonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (d : ι → F) (h : M * diagonal d = diagonal d * M) {i j : ι}
    (hij : d i ≠ d j) : M i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : M i j * (d j - d i) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hij.symm)

theorem pow_three_eq_one_of_commute_torus [Finite F] (hF : Nat.card F = 4) (g : StatedSp 2 F)
    (h : ∀ t : Fin 2 → Fˣ,
      g * SymplecticTorusWeyl.torusHom t = SymplecticTorusWeyl.torusHom t * g) :
    g ^ 3 = 1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card Fˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨ω, hω1⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Fˣ) (1 : Fˣ)
  have hω3 : ω ^ 3 = 1 := by
    rw [← hcard, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2]; simp
  have hn1 : (ω : F) ≠ 1 := fun hh => hω1 (Units.ext hh)
  have hn2 : (ω : F)⁻¹ ≠ 1 := fun hh => hn1 (inv_eq_one.mp hh)
  have hn3 : (ω : F) ≠ (ω : F)⁻¹ := by
    intro hh
    have h3 : (ω : F) * ω = 1 := by
      calc (ω : F) * ω = ω * (ω : F)⁻¹ := by rw [← hh]
        _ = 1 := mul_inv_cancel₀ ω.ne_zero
    apply hω2
    exact Units.ext (by simpa [sq] using h3)
  have hcomm : ∀ t : Fin 2 → Fˣ, spMat g * diagonal (Sum.elim (fun i => (t i : F))
      fun i => (((t i)⁻¹ : Fˣ) : F)) = diagonal (Sum.elim (fun i => (t i : F))
      fun i => (((t i)⁻¹ : Fˣ) : F)) * spMat g := fun t => by
    have h1 := congrArg spMat (h t)
    have hD : spMat (SymplecticTorusWeyl.torusHom t) = diagonal (Sum.elim (fun i => (t i : F))
        fun i => (((t i)⁻¹ : Fˣ) : F)) := SymplecticTorusWeyl.coe_torusHom t
    rw [show spMat (g * SymplecticTorusWeyl.torusHom t) = spMat g *
        spMat (SymplecticTorusWeyl.torusHom t) from rfl,
      show spMat (SymplecticTorusWeyl.torusHom t * g) = spMat (SymplecticTorusWeyl.torusHom t) *
        spMat g from rfl, hD] at h1
    exact h1
  have hoff : ∀ i j : Fin 2 ⊕ Fin 2, i ≠ j → spMat g i j = 0 := by
    intro i j hij
    have h1 := hcomm ![ω, 1]
    have h2 := hcomm ![1, ω]
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | (refine entry_eq_zero_of_commute_diagonal _ _ h1 ?_
         simp [hn1, hn2, hn3, hn1.symm, hn2.symm, hn3.symm]
         done)
      | (refine entry_eq_zero_of_commute_diagonal _ _ h2 ?_
         simp [hn3, hn3.symm])
  have hdiag : spMat g = diagonal fun i => spMat g i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have hinv : spMat g * spMat g⁻¹ = 1 := congrArg spMat (mul_inv_cancel g)
  have hne : ∀ i, spMat g i i ≠ 0 := by
    intro i
    have h1 := congrFun (congrFun hinv i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [hoff i k (Ne.symm hk), zero_mul]) (fun hi => absurd (Finset.mem_univ i) hi), Matrix.one_apply_eq] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hcube : ∀ i, spMat g i i ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (spMat g i i) (hne i)
    rwa [← Nat.card_eq_fintype_card, hF] at h
  refine Subtype.ext (Units.ext ?_)
  change spMat g ^ 3 = 1
  rw [hdiag, Matrix.diagonal_pow]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hcube]
  · simp [hij]

end Torus

end CFSG.QuasithinUnique.Id2519.USp4
