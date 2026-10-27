module

public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.CharacterTheory.OddOrderBasics.Schur
public import CFSG.CharacterTheory.SmallDefect.Basic
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralPrincipalInducedFamily
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalInduction

public section

namespace CFSG.GH74.GLS.Stage4.Q9

theorem class_sum_pair_gen {H : Type} [Group H] [Fintype H] {χ : H → ℂ} (hχ : χ ∈ BlocksIrr H)
    (J : Finset H) (hJ : ∀ g x, x ∈ J → g * x * g⁻¹ ∈ J) :
    (∑ x ∈ J, ∑ y ∈ J, χ (x * y)) * χ 1 = (∑ x ∈ J, χ x) ^ 2 := by
  classical
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := hχ
  set T : Module.End ℂ V := ∑ x ∈ J, ρ x with hTdef
  have hT : ∀ g : H, T ∘ₗ ρ g = ρ g ∘ₗ T := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hTdef, Finset.sum_mul,
      Finset.mul_sum]
    simp only [← map_mul]
    refine (Finset.sum_nbij' (fun y => g⁻¹ * y * g) (fun x => g * x * g⁻¹) ?_ ?_ ?_ ?_ ?_)
    · intro y hy
      simpa using hJ g⁻¹ y hy
    · intro x hx
      exact hJ g x hx
    · intro y _
      group
    · intro x _
      group
    · intro y _
      congr 1
      group
  obtain ⟨a, ha⟩ := OddOrderBasics.complex_irreducible_commuting_scalar ρ hρ T hT
  have htr : LinearMap.trace ℂ V T = ∑ x ∈ J, ρ.character x := by
    rw [hTdef, map_sum]
    rfl
  have htr2 : LinearMap.trace ℂ V (T * T) = ∑ x ∈ J, ∑ y ∈ J, ρ.character (x * y) := by
    rw [hTdef, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← map_mul]
    rfl
  have hsq : T * T = (a * a) • LinearMap.id := by
    rw [ha, smul_mul_smul_comm, ← Module.End.one_eq_id, mul_one]
  rw [ha, map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hsq, map_smul, LinearMap.trace_id, smul_eq_mul] at htr2
  rw [← htr2, Representation.char_one, ← htr]
  ring

theorem isClassFunction_of_comp_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {φ : B → ℂ} (h : BlocksIsClassFunction (φ ∘ f)) :
    BlocksIsClassFunction φ := by
  intro g k
  obtain ⟨a, rfl⟩ := hf g
  obtain ⟨c, rfl⟩ := hf k
  simpa only [Function.comp_apply, map_mul, map_inv] using h a c

theorem mem_blocksVChar_of_comp_surjective {A B : Type} [Group A] [Group B] [Fintype A]
    [Fintype B] (f : A →* B) (hf : Function.Surjective f) {φ : B → ℂ}
    (h : φ ∘ f ∈ BlocksVChar A) : φ ∈ BlocksVChar B := by
  have hclass : BlocksIsClassFunction φ :=
    isClassFunction_of_comp_surjective f hf (blocksVChar_isClassFunction h)
  have hexp := (irreducible_character_basis B).2.2.2 φ hclass
  rw [hexp]
  refine AddSubgroup.sum_mem _ fun χ hχ => ?_
  have hχ' : χ ∈ BlocksIrr B :=
    (BlockSectionOrthogonality.Helpers.irreducibles_finite B).mem_toFinset.mp hχ
  obtain ⟨n, hn⟩ := blocksInnerProduct_virtual_integer h
    (AddSubgroup.subset_closure (Semidihedral.Principal.comp_mem_blocksIrr f hf hχ'))
  rw [← Semidihedral.Principal.blocksInnerProduct_comp_surjective f hf φ χ, hn,
    Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hχ') n

theorem exists_descent_vchar {A B : Type} [Group A] [Group B] [Fintype A] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) {φ' : A → ℂ} (hφ' : φ' ∈ BlocksVChar A)
    (hconst : ∀ a a', f a = f a' → φ' a = φ' a') :
    ∃ φ : B → ℂ, φ ∘ f = φ' ∧ φ ∈ BlocksVChar B ∧
      BlocksInnerProduct φ φ = BlocksInnerProduct φ' φ' ∧
      BlocksInnerProduct φ 1 = BlocksInnerProduct φ' 1 ∧ (∀ a, φ (f a) = φ' a) ∧
      (∀ ψ : B → ℂ, BlocksInnerProduct φ ψ = BlocksInnerProduct φ' (ψ ∘ f)) ∧
      φ 1 = φ' 1 := by
  have hcomp : (φ' ∘ Function.surjInv hf) ∘ f = φ' := by
    funext a
    exact hconst _ _ (Function.surjInv_eq hf (f a))
  have hinner : ∀ ψ : B → ℂ, BlocksInnerProduct (φ' ∘ Function.surjInv hf) ψ =
      BlocksInnerProduct φ' (ψ ∘ f) := by
    intro ψ
    rw [← Semidihedral.Principal.blocksInnerProduct_comp_surjective f hf, hcomp]
  have hmem : (φ' ∘ Function.surjInv hf) ∘ f ∈ BlocksVChar A := by
    rw [hcomp]
    exact hφ'
  refine ⟨φ' ∘ Function.surjInv hf, hcomp, mem_blocksVChar_of_comp_surjective f hf hmem, ?_, ?_,
    fun a => congrFun hcomp a, hinner, ?_⟩
  · rw [hinner]
    simp only [hcomp]
  · rw [hinner]
    rfl
  · have := congrFun hcomp 1
    simpa only [Function.comp_apply, map_one] using this

section Theta

variable {H : Type} [Group H]

theorem theta_mem_blocksVChar {α β : H → ℂ} (hα : α ∈ BlocksIrr H) (hβ : β ∈ BlocksIrr H) :
    ((1 : H → ℂ) - α + β) ∈ BlocksVChar H :=
  (BlocksVChar H).add_mem ((BlocksVChar H).sub_mem
    (AddSubgroup.subset_closure (DirectProduct.one_mem_blocksIrr H))
    (AddSubgroup.subset_closure hα)) (AddSubgroup.subset_closure hβ)

theorem theta_ne_of_degrees {α β : H → ℂ} (hα81 : α 1 = 81) (hβ80 : β 1 = 80) :
    α ≠ 1 ∧ β ≠ α ∧ β ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 1
    rw [hα81] at this
    norm_num at this
  · have := congrFun h 1
    rw [hα81, hβ80] at this
    norm_num at this
  · have := congrFun h 1
    rw [hβ80] at this
    norm_num at this

theorem theta_apply_one {α β : H → ℂ} (hα81 : α 1 = 81) (hβ80 : β 1 = 80) :
    ((1 : H → ℂ) - α + β) 1 = 0 := by
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, hα81, hβ80]
  norm_num

variable [Fintype H]

theorem blocksInnerProduct_theta_one {α β : H → ℂ} (hα : α ∈ BlocksIrr H)
    (hβ : β ∈ BlocksIrr H) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) :
    BlocksInnerProduct ((1 : H → ℂ) - α + β) 1 = 1 := by
  have h1 := DirectProduct.one_mem_blocksIrr H
  have e11 : BlocksInnerProduct (1 : H → ℂ) 1 = 1 :=
    DirectProduct.blocksInnerProduct_self_of_mem h1
  have eα1 : BlocksInnerProduct α (1 : H → ℂ) = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hα h1, ite_eq_right hα1]
  have eβ1 : BlocksInnerProduct β (1 : H → ℂ) = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hβ h1, ite_eq_right hβ1]
  rw [SmallDefect.blocksInnerProduct_add_left, SmallDefect.blocksInnerProduct_sub_left, e11, eα1,
    eβ1]
  norm_num

theorem blocksInnerProduct_theta_self {α β : H → ℂ} (hα : α ∈ BlocksIrr H)
    (hβ : β ∈ BlocksIrr H) (hαβ : α ≠ β) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) :
    BlocksInnerProduct ((1 : H → ℂ) - α + β) ((1 : H → ℂ) - α + β) = 3 := by
  have h1 := DirectProduct.one_mem_blocksIrr H
  have e11 : BlocksInnerProduct (1 : H → ℂ) 1 = 1 :=
    DirectProduct.blocksInnerProduct_self_of_mem h1
  have eαα : BlocksInnerProduct α α = 1 := DirectProduct.blocksInnerProduct_self_of_mem hα
  have eββ : BlocksInnerProduct β β = 1 := DirectProduct.blocksInnerProduct_self_of_mem hβ
  have e1α : BlocksInnerProduct (1 : H → ℂ) α = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem h1 hα, ite_eq_right hα1.symm]
  have e1β : BlocksInnerProduct (1 : H → ℂ) β = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem h1 hβ, ite_eq_right hβ1.symm]
  have eα1 : BlocksInnerProduct α (1 : H → ℂ) = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hα h1, ite_eq_right hα1]
  have eβ1 : BlocksInnerProduct β (1 : H → ℂ) = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hβ h1, ite_eq_right hβ1]
  have eαβ : BlocksInnerProduct α β = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hα hβ, ite_eq_right hαβ]
  have eβα : BlocksInnerProduct β α = 0 := by
    rw [DirectProduct.blocksInnerProduct_of_mem hβ hα, ite_eq_right hαβ.symm]
  simp only [SmallDefect.blocksInnerProduct_add_left, SmallDefect.blocksInnerProduct_sub_left,
    SmallDefect.blocksInnerProduct_add_right, SmallDefect.blocksInnerProduct_sub_right, e11, eαα,
    eββ, e1α, e1β, eα1, eβ1, eαβ, eβα]
  norm_num

theorem theta_data_of_degrees {α β : H → ℂ} (hα : α ∈ BlocksIrr H) (hβ : β ∈ BlocksIrr H)
    (hα81 : α 1 = 81) (hβ80 : β 1 = 80) :
    ((1 : H → ℂ) - α + β) ∈ BlocksVChar H ∧
      BlocksInnerProduct ((1 : H → ℂ) - α + β) ((1 : H → ℂ) - α + β) = 3 ∧
      BlocksInnerProduct ((1 : H → ℂ) - α + β) 1 = 1 ∧ ((1 : H → ℂ) - α + β) 1 = 0 := by
  obtain ⟨hα1, hβα, hβ1⟩ := theta_ne_of_degrees (H := H) hα81 hβ80
  exact ⟨theta_mem_blocksVChar hα hβ, blocksInnerProduct_theta_self hα hβ hβα.symm hα1 hβ1,
    blocksInnerProduct_theta_one hα hβ hα1 hβ1, theta_apply_one hα81 hβ80⟩

theorem theta_class_pair_sum {α β : H → ℂ} (hα : α ∈ BlocksIrr H) (hβ : β ∈ BlocksIrr H)
    (J : Finset H) (hJ : ∀ g x, x ∈ J → g * x * g⁻¹ ∈ J) :
    ∑ x ∈ J, ∑ y ∈ J, ((1 : H → ℂ) - α + β) (x * y) =
      (J.card : ℂ) ^ 2 - (∑ x ∈ J, α x) ^ 2 / α 1 + (∑ x ∈ J, β x) ^ 2 / β 1 := by
  have hA := eq_div_of_mul_eq (DirectProduct.identity_ne_zero_of_mem hα)
    (class_sum_pair_gen hα J hJ)
  have hB := eq_div_of_mul_eq (DirectProduct.identity_ne_zero_of_mem hβ)
    (class_sum_pair_gen hβ J hJ)
  have hone : ∑ x ∈ J, ∑ y ∈ J, (1 : ℂ) = (J.card : ℂ) ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hone, hA, hB]

theorem kappa_class_sum_eval {α β : H → ℂ} (hα : α ∈ BlocksIrr H) (hβ : β ∈ BlocksIrr H)
    (J : Finset H) (hJ : ∀ g x, x ∈ J → g * x * g⁻¹ ∈ J) (hJv : ∀ x ∈ J, α x = 1 ∧ β x = 0)
    (hα81 : α 1 = 81) (hβ80 : β 1 = 80) (hcard : J.card = 6642) :
    ∑ x ∈ J, ∑ y ∈ J, ((1 : H → ℂ) - α + β) (x * y) = 43571520 := by
  have hsumα : ∑ x ∈ J, α x = 6642 := by
    rw [Finset.sum_congr rfl fun x hx => (hJv x hx).1, Finset.sum_const, hcard]
    simp
  have hsumβ : ∑ x ∈ J, β x = 0 := Finset.sum_eq_zero fun x hx => (hJv x hx).2
  rw [theta_class_pair_sum hα hβ J hJ, hsumα, hsumβ, hα81, hβ80, hcard]
  norm_num

end Theta

theorem theta_data_of_irr {A B : Type} [Group A] [Group B] [Fintype A] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) {α' β' : A → ℂ}
    (hα' : α' ∈ BlocksVChar A) (hβ' : β' ∈ BlocksVChar A)
    (hαc : ∀ a a', f a = f a' → α' a = α' a') (hβc : ∀ a a', f a = f a' → β' a = β' a')
    (hαn : BlocksInnerProduct α' α' = 1) (hβn : BlocksInnerProduct β' β' = 1)
    (hα81 : α' 1 = 81) (hβ80 : β' 1 = 80) :
    ∃ α β : B → ℂ, α ∘ f = α' ∧ β ∘ f = β' ∧ α ∈ BlocksIrr B ∧ β ∈ BlocksIrr B ∧
      ((1 : B → ℂ) - α + β) ∈ BlocksVChar B ∧
      BlocksInnerProduct ((1 : B → ℂ) - α + β) ((1 : B → ℂ) - α + β) = 3 ∧
      BlocksInnerProduct ((1 : B → ℂ) - α + β) 1 = 1 ∧ ((1 : B → ℂ) - α + β) 1 = 0 ∧
      α 1 = 81 ∧ β 1 = 80 ∧ ((1 : B → ℂ) - α + β) ∘ f = (1 : A → ℂ) - α' + β' := by
  obtain ⟨α, hαf, hαv, hαα, -, -, -, hα1⟩ := exists_descent_vchar f hf hα' hαc
  obtain ⟨β, hβf, hβv, hββ, -, -, -, hβ1⟩ := exists_descent_vchar f hf hβ' hβc
  rw [hα81] at hα1
  rw [hβ80] at hβ1
  have hαirr : α ∈ BlocksIrr B := Wreathed.CentralSL2.mem_blocksIrr_of_virtual_norm_one hαv
    (hαα.trans hαn) (by rw [hα1]; norm_num)
  have hβirr : β ∈ BlocksIrr B := Wreathed.CentralSL2.mem_blocksIrr_of_virtual_norm_one hβv
    (hββ.trans hβn) (by rw [hβ1]; norm_num)
  obtain ⟨hθv, hθθ, hθ1, hθ0⟩ := theta_data_of_degrees hαirr hβirr hα1 hβ1
  refine ⟨α, β, hαf, hβf, hαirr, hβirr, hθv, hθθ, hθ1, hθ0, hα1, hβ1, ?_⟩
  rw [← hαf, ← hβf]
  rfl

end CFSG.GH74.GLS.Stage4.Q9
