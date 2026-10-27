module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreDefs
public import CFSG.LargeExtraspecial.A2ModSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type*} [Field F] {σ : F ≃+* F}

theorem sigma_cube (h3 : orderOf σ = 3) (x : F) : σ (σ (σ x)) = x := by
  have h := pow_orderOf_eq_one σ
  rw [h3] at h
  have := congrArg (fun f : F ≃+* F => f x) h
  simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply] at this
  exact this

@[expose] def IsRat (σ : F ≃+* F) (v : Fin 3 → F) : Prop := ∀ i, σ (v i) = v i

@[expose] def IsRatM (σ : F ≃+* F) (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ i j, σ (M i j) = M i j

theorem isRatM_one : IsRatM σ (1 : Matrix (Fin 3) (Fin 3) F) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem IsRatM.mul {M N : Matrix (Fin 3) (Fin 3) F} (hM : IsRatM σ M) (hN : IsRatM σ N) :
    IsRatM σ (M * N) := by
  intro i j
  simp only [Matrix.mul_apply, map_sum, map_mul, hM _ _, hN _ _]

theorem IsRatM.mulVec {M : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F} (hM : IsRatM σ M)
    (hv : IsRat σ v) : IsRat σ (M *ᵥ v) := by
  intro i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hM _ _, hv _]

theorem IsRat.vecMul {M : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F} (hv : IsRat σ v)
    (hM : IsRatM σ M) : IsRat σ (v ᵥ* M) := by
  intro j
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, hM _ _, hv _]

theorem coe_inv_mul (g : GL (Fin 3) F) :
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem coe_mul_inv (g : GL (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem IsRatM.inv {g : GL (Fin 3) F} (hg : IsRatM σ (g : Matrix (Fin 3) (Fin 3) F)) :
    IsRatM σ ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  set N := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  set M := (g : Matrix (Fin 3) (Fin 3) F)
  set Nσ : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => σ (N i j)
  have h1 : M * Nσ = 1 := by
    ext i j
    have e := congrArg (fun P : Matrix (Fin 3) (Fin 3) F => σ (P i j)) (coe_mul_inv g)
    simp only [Matrix.mul_apply, map_sum, map_mul] at e
    simp only [Matrix.mul_apply, Nσ, Matrix.of_apply]
    rw [← isRatM_one (σ := σ) i j, ← e]
    exact Finset.sum_congr rfl fun l _ => by rw [hg i l]
  have h2 : Nσ = N := by
    calc Nσ = (N * M) * Nσ := by rw [coe_inv_mul, Matrix.one_mul]
      _ = N := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  intro i j
  exact congrFun (congrFun h2 i) j

@[expose] def ratGL (σ : F ≃+* F) : Subgroup (GL (Fin 3) F) where
  carrier := {g | IsRatM σ (g : Matrix (Fin 3) (Fin 3) F)}
  one_mem' := isRatM_one
  mul_mem' {a b} ha hb := by
    change IsRatM σ ((a * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Units.val_mul]
    exact IsRatM.mul ha hb
  inv_mem' {a} ha := IsRatM.inv ha

theorem mem_ratGL {g : GL (Fin 3) F} :
    g ∈ ratGL σ ↔ IsRatM σ (g : Matrix (Fin 3) (Fin 3) F) := Iff.rfl

theorem conjGL3_coe (h : GL (Fin 3) F) (g : SpecialLinearGroup (Fin 3) F) :
    ((conjGL3 h g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
        ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl

theorem conjGL3_mul (a h : GL (Fin 3) F) :
    conjGL3 (a * h) = (conjGL3 a).comp (conjGL3 h) := by
  ext g i j
  simp only [MonoidHom.comp_apply, conjGL3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.mul_assoc]

theorem conjGL3_one : conjGL3 (1 : GL (Fin 3) F) = MonoidHom.id _ := by
  ext g i j
  simp [conjGL3_coe]

theorem conjGL3_inv_apply (a : GL (Fin 3) F) (g : SpecialLinearGroup (Fin 3) F) :
    conjGL3 a⁻¹ (conjGL3 a g) = g := by
  rw [← MonoidHom.comp_apply, ← conjGL3_mul, inv_mul_cancel, conjGL3_one, MonoidHom.id_apply]

theorem conjGL3_apply_inv (a : GL (Fin 3) F) (g : SpecialLinearGroup (Fin 3) F) :
    conjGL3 a (conjGL3 a⁻¹ g) = g := by
  rw [← MonoidHom.comp_apply, ← conjGL3_mul, mul_inv_cancel, conjGL3_one, MonoidHom.id_apply]

theorem conjGL3_injective (a : GL (Fin 3) F) : Function.Injective (conjGL3 a) := fun x y hxy => by
  rw [← conjGL3_inv_apply a x, hxy, conjGL3_inv_apply]

theorem map_conjGL3_fixSL3 {a : GL (Fin 3) F} (ha : a ∈ ratGL σ) :
    (fixSL3 σ).map (conjGL3 a) = fixSL3 σ := by
  have key : ∀ b ∈ ratGL σ, ∀ g ∈ fixSL3 σ, conjGL3 b g ∈ fixSL3 σ := by
    intro b hb g hg
    change IsRatM σ _
    rw [conjGL3_coe]
    exact (IsRatM.mul hb hg).mul (IsRatM.inv hb)
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact key a ha g hg
  · exact ⟨conjGL3 a⁻¹ g, key _ ((ratGL σ).inv_mem ha) g hg, conjGL3_apply_inv a g⟩

@[expose] def joinH (σ : F ≃+* F) (h : GL (Fin 3) F) : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  fixSL3 σ ⊔ (fixSL3 σ).map (conjGL3 h)

theorem fixSL3_le_joinH (h : GL (Fin 3) F) : fixSL3 σ ≤ joinH σ h := le_sup_left

theorem joinH_rat_mul {a : GL (Fin 3) F} (ha : a ∈ ratGL σ) (h : GL (Fin 3) F) :
    joinH σ (a * h) = (joinH σ h).map (conjGL3 a) := by
  unfold joinH
  rw [Subgroup.map_sup, map_conjGL3_fixSL3 ha, conjGL3_mul, Subgroup.map_map]

theorem top_le_of_top_le_map {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {a : GL (Fin 3) F}
    (h : ⊤ ≤ K.map (conjGL3 a)) : ⊤ ≤ K := by
  intro x _
  obtain ⟨y, hy, hxy⟩ := h (Subgroup.mem_top (conjGL3 a x))
  rwa [conjGL3_injective a hxy] at hy

theorem top_le_joinH_of_rat_mul {a h : GL (Fin 3) F} (ha : a ∈ ratGL σ)
    (htop : ⊤ ≤ joinH σ (a * h)) : ⊤ ≤ joinH σ h := by
  rw [joinH_rat_mul ha] at htop
  exact top_le_of_top_le_map htop

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
