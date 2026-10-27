module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ChevalleyGenerators

public section

namespace CFSG.Blueprint

variable (a : ℕ) {K : Type} [Field K]

theorem det_suzukiS (u v : K) : (suzukiS a u v).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
  · simp [suzukiS, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [suzukiS]

theorem det_suzukiD (l : Kˣ) : (suzukiD a l).det = 1 := by
  have h : l ^ (1 + (2 ^ a : ℤ)) * l ^ (2 ^ a : ℤ) * l ^ (-(2 ^ a : ℤ)) *
      l ^ (-1 - (2 ^ a : ℤ)) = 1 := by
    rw [← zpow_add, ← zpow_add, ← zpow_add]
    ring_nf
    exact zpow_zero l
  rw [suzukiD, Matrix.det_diagonal, Fin.prod_univ_four]
  change ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (2 ^ a : ℤ) : Kˣ) : K) *
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h, Units.val_one]

variable (K) in
theorem suzukiW_mul_self : suzukiW K * suzukiW K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_mem_suzukiGroup_eq_S (u v : K) :
    ∃ g ∈ suzukiGroup a K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v)
    (by rw [det_suzukiS]; exact one_ne_zero),
    Subgroup.subset_closure ?_, rfl⟩
  exact Or.inl ⟨u, v, rfl⟩

theorem exists_mem_suzukiGroup_eq_D (l : Kˣ) :
    ∃ g ∈ suzukiGroup a K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiD a l := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l)
    (by rw [det_suzukiD]; exact one_ne_zero),
    Subgroup.subset_closure ?_, rfl⟩
  exact Or.inr (Or.inl ⟨l, rfl⟩)

theorem exists_mem_suzukiGroup_eq_W :
    ∃ g ∈ suzukiGroup a K, (g : Matrix (Fin 4) (Fin 4) K) = suzukiW K := by
  refine ⟨⟨suzukiW K, suzukiW K, suzukiW_mul_self K, suzukiW_mul_self K⟩,
    Subgroup.subset_closure ?_, rfl⟩
  exact Or.inr (Or.inr rfl)

open Chevalley in
theorem reeRelationGroup_generators (τ : Tag) (K : Type) [Field K] (ρ : Equiv.Perm (Fin τ.rank))
    (e : Fin τ.rank → ℕ) (i : Fin τ.rank) (c : K) :
    (∃ gh ∈ reeRelationGroup τ K ρ e, gh.1 ∈ adjointGroup τ K ∧ gh.2 ∈ adjointGroup τ K ∧
      (gh.1 : Module.End K (RootModule τ K)) = xOp τ K i c ∧
        (gh.2 : Module.End K (RootModule τ K)) = xOp τ K (ρ i) (c ^ e i)) ∧
      ∃ gh ∈ reeRelationGroup τ K ρ e, gh.1 ∈ adjointGroup τ K ∧ gh.2 ∈ adjointGroup τ K ∧
        (gh.1 : Module.End K (RootModule τ K)) = yOp τ K i c ∧
          (gh.2 : Module.End K (RootModule τ K)) = yOp τ K (ρ i) (c ^ e i) := by
  obtain ⟨⟨g₁, hg₁, hx₁⟩, -⟩ := xOp_yOp_mem_adjointGroup τ K i c
  obtain ⟨⟨g₂, hg₂, hx₂⟩, -⟩ := xOp_yOp_mem_adjointGroup τ K (ρ i) (c ^ e i)
  obtain ⟨-, ⟨g₃, hg₃, hy₃⟩⟩ := xOp_yOp_mem_adjointGroup τ K i c
  obtain ⟨-, ⟨g₄, hg₄, hy₄⟩⟩ := xOp_yOp_mem_adjointGroup τ K (ρ i) (c ^ e i)
  exact ⟨⟨(g₁, g₂), Subgroup.subset_closure ⟨i, c, Or.inl ⟨hx₁, hx₂⟩⟩, hg₁, hg₂, hx₁, hx₂⟩,
    ⟨(g₃, g₄), Subgroup.subset_closure ⟨i, c, Or.inr ⟨hy₃, hy₄⟩⟩, hg₃, hg₄, hy₃, hy₄⟩⟩

end CFSG.Blueprint
