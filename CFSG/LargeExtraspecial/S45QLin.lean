module

public import CFSG.LargeExtraspecial.S45QSylow
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Module Subgroup

theorem isSimpleGroup_GL_zmod_two {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup (GL (Fin n) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n) (by omega)
    (Or.inl hn)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin n) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun _ =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin n) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem isSimpleGroup_top_of_three_le (h3 : 3 ≤ finrank (ZMod 2) V) :
    IsSimpleGroup (⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) := by
  have := isSimpleGroup_GL_zmod_two h3
  exact (Subgroup.topEquiv.trans
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
      (Module.finBasis (ZMod 2) V))).isSimpleGroup

theorem isSolvable_top_of_finrank_two (h2 : finrank (ZMod 2) V = 2) :
    Group.IsSolvable (⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hV : Nat.card V = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), h2, Nat.card_zmod]
    norm_num
  let b := Module.finBasisOfFinrankEq (ZMod 2) V h2
  have hinj : Function.Injective (fun e : V ≃ₗ[ZMod 2] V => fun i : Fin 2 => e (b i)) := by
    intro e₁ e₂ h
    exact LinearEquiv.toLinearMap_injective (b.ext fun i => congrFun h i)
  have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective _ hinj
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, hV, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at hcard
  apply CFSG.GroupTheory.groups_order_below_sixty_solvable
  rw [Subgroup.card_top]
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem transvection_mul_self {f : Dual (ZMod 2) V} {e₁ : V} (hf : f e₁ = 0) :
    LinearEquiv.transvection hf * LinearEquiv.transvection hf = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.transvection.apply, LinearEquiv.transvection.apply,
    map_add, map_smul, hf, smul_eq_mul, mul_zero, add_zero, add_assoc, ZModModule.add_self,
    add_zero]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem transvection_pair_sq {f h : Dual (ZMod 2) V} {e₁ e₂ : V} (hf1 : f e₁ = 0)
    (hf2 : f e₂ = 1) (hh1 : h e₁ = 0) (hh2 : h e₂ = 0) (v : V) :
    ((LinearEquiv.transvection hf1 * LinearEquiv.transvection hh2) ^ 2) v = v + h v • e₁ := by
  simp only [sq, LinearEquiv.mul_apply, LinearEquiv.transvection.apply, map_add, map_smul,
    hf1, hf2, hh1, hh2]
  match_scalars <;> ring_nf <;> reduce_mod_char

theorem nonabelianSylowTwo_top (h3 : 3 ≤ finrank (ZMod 2) V) :
    S5.NonabelianSylowTwo (⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  let b := Module.finBasis (ZMod 2) V
  let i₀ : Fin (finrank (ZMod 2) V) := ⟨0, by omega⟩
  let i₁ : Fin (finrank (ZMod 2) V) := ⟨1, by omega⟩
  let i₂ : Fin (finrank (ZMod 2) V) := ⟨2, by omega⟩
  have hc : ∀ i j, b.coord i (b j) = if j = i then 1 else 0 := fun i j => by
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have h01 : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  have h02 : i₀ ≠ i₂ := fun h => by simp [i₀, i₂, Fin.ext_iff] at h
  have h12 : i₁ ≠ i₂ := fun h => by simp [i₁, i₂, Fin.ext_iff] at h
  have hf1 : b.coord i₁ (b i₀) = 0 := by simp [hc, h01]
  have hf2 : b.coord i₁ (b i₁) = 1 := by simp [hc]
  have hh1 : b.coord i₂ (b i₀) = 0 := by simp [hc, h02]
  have hh2 : b.coord i₂ (b i₁) = 0 := by simp [hc, h12]
  have hh3 : b.coord i₂ (b i₂) = 1 := by simp [hc]
  set x := LinearEquiv.transvection hf1
  set y := LinearEquiv.transvection hh2
  have hsq := transvection_pair_sq hf1 hf2 hh1 hh2
  have hxx : x * x = 1 := transvection_mul_self hf1
  have hyy : y * y = 1 := transvection_mul_self hh2
  have hne1 : (x * y) ^ 2 ≠ 1 := by
    intro h
    have h1 := hsq (b i₂)
    rw [h, hh3, one_smul] at h1
    change b i₂ = b i₂ + b i₀ at h1
    rw [left_eq_add] at h1
    exact b.ne_zero i₀ h1
  refine nonabelianSylowTwo_of_mem (mem_top x) (mem_top y) hxx hyy (k := 2) ?_ ?_
  · rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
    ext v
    rw [sq ((x * y) ^ 2), LinearEquiv.mul_apply, hsq, hsq, map_add, map_smul, hh1, smul_zero,
      add_zero, add_assoc, ZModModule.add_self, add_zero]
    rfl
  · intro h
    apply hne1
    rw [sq, show x * y * (x * y) = x * (y * x) * y by group, ← h,
      show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]

end CFSG.LargeExtraspecial.S45Q
