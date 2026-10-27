module

public import CFSG.LieType.SteinbergBRBlockParabolicResidual
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix

variable {F : Type*} [Field F] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b]

theorem toBlocks₁₁_mul_inv {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    g.val.toBlocks₁₁ * (g⁻¹).val.toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul (inv_mem hg)]
  change ((g * g⁻¹).val).toBlocks₁₁ = 1
  rw [mul_inv_cancel]
  exact toBlocks_fromBlocks₁₁ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
    (congrArg Matrix.toBlocks₁₁ fromBlocks_one.symm)

theorem toBlocks₁₁_inv_mul {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    (g⁻¹).val.toBlocks₁₁ * g.val.toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul hg]
  rw [inv_mul_cancel]
  exact toBlocks_fromBlocks₁₁ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
    (congrArg Matrix.toBlocks₁₁ fromBlocks_one.symm)

theorem toBlocks₂₂_mul_inv {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    g.val.toBlocks₂₂ * (g⁻¹).val.toBlocks₂₂ = 1 := by
  rw [← toBlocks₂₂_mul hg]
  rw [mul_inv_cancel]
  exact toBlocks_fromBlocks₂₂ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
    (congrArg Matrix.toBlocks₂₂ fromBlocks_one.symm)

theorem toBlocks₂₂_inv_mul {g : SpecialLinearGroup (a ⊕ b) F} (hg : g ∈ parQ) :
    (g⁻¹).val.toBlocks₂₂ * g.val.toBlocks₂₂ = 1 := by
  rw [← toBlocks₂₂_mul (inv_mem hg)]
  change ((g⁻¹ * g).val).toBlocks₂₂ = 1
  rw [inv_mul_cancel]
  exact toBlocks_fromBlocks₂₂ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
    (congrArg Matrix.toBlocks₂₂ fromBlocks_one.symm)

variable (a b F) in
@[expose] noncomputable def chiL : (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) →* GL a F where
  toFun g := ⟨(g : SpecialLinearGroup (a ⊕ b) F).val.toBlocks₁₁,
    ((g : SpecialLinearGroup (a ⊕ b) F)⁻¹).val.toBlocks₁₁, toBlocks₁₁_mul_inv g.2,
    toBlocks₁₁_inv_mul g.2⟩
  map_one' := Units.ext (by
    change (1 : SpecialLinearGroup (a ⊕ b) F).val.toBlocks₁₁ = 1
    exact toBlocks_fromBlocks₁₁ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
      (congrArg Matrix.toBlocks₁₁ fromBlocks_one.symm))
  map_mul' g h := Units.ext (toBlocks₁₁_mul h.2)

variable (a b F) in
@[expose] noncomputable def chiR : (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) →* GL b F where
  toFun g := ⟨(g : SpecialLinearGroup (a ⊕ b) F).val.toBlocks₂₂,
    ((g : SpecialLinearGroup (a ⊕ b) F)⁻¹).val.toBlocks₂₂, toBlocks₂₂_mul_inv g.2,
    toBlocks₂₂_inv_mul g.2⟩
  map_one' := Units.ext (by
    change (1 : SpecialLinearGroup (a ⊕ b) F).val.toBlocks₂₂ = 1
    exact toBlocks_fromBlocks₂₂ (1 : Matrix a a F) 0 0 (1 : Matrix b b F) ▸
      (congrArg Matrix.toBlocks₂₂ fromBlocks_one.symm))
  map_mul' g h := Units.ext (toBlocks₂₂_mul g.2)

theorem ker_chiL : (chiL F a b).ker = (parJR F a b).subgroupOf parQ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_parJR, Units.ext_iff]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem ker_chiR : (chiR F a b).ker = (parJL F a b).subgroupOf parQ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_parJL, Units.ext_iff]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem matrix_mul_comm_of_subsingleton {c : Type*} [Fintype c] [Subsingleton c]
    (M N : Matrix c c F) : M * N = N * M := by
  ext i j
  rw [Subsingleton.elim j i, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Subsingleton.elim k i, mul_comm]

theorem isSolvable_quotient_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hcomm : ∀ x y : H, x * y = y * x) : Group.IsSolvable (G ⧸ f.ker) := by
  have : Group.IsSolvable f.range :=
    Group.isSolvable_of_comm fun x y => Subtype.ext (hcomm x y)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.quotientKerEquivRange f).toMonoidHom) (MulEquiv.injective _)

theorem isPerfect_subgroupOf {G : Type*} [Group G] {J Q : Subgroup G} (hJQ : J ≤ Q)
    (hJ : ⁅J, J⁆ = J) : Group.IsPerfect (J.subgroupOf Q) := by
  rw [Subgroup.isPerfect_iff]
  apply Subgroup.map_injective Q.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJQ, hJ]

theorem perfectResidual_parQ_eq_parJR [Finite F] [Subsingleton a] [Nontrivial b]
    (hSL : commutator (SpecialLinearGroup b F) = ⊤) :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) =
      (parJR F a b).subgroupOf parQ := by
  obtain ⟨-, -, -, -, hiff, -⟩ :=
    CFSG.perfect_residual_characterization (G := (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  obtain ⟨-, -, hperf⟩ := CFSG.perfect_residual_transport
    (MonoidHom.id (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  refine le_antisymm ?_ (hperf _ (isPerfect_subgroupOf parJR_le_parQ (commutator_parJR hSL)))
  rw [← ker_chiL]
  exact (hiff _).1 (isSolvable_quotient_ker _ fun x y =>
    Units.ext (matrix_mul_comm_of_subsingleton _ _))

theorem perfectResidual_parQ_eq_parJL [Finite F] [Subsingleton b] [Nontrivial a]
    (hSL : commutator (SpecialLinearGroup a F) = ⊤) :
    CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)) =
      (parJL F a b).subgroupOf parQ := by
  obtain ⟨-, -, -, -, hiff, -⟩ :=
    CFSG.perfect_residual_characterization (G := (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  obtain ⟨-, -, hperf⟩ := CFSG.perfect_residual_transport
    (MonoidHom.id (parQ : Subgroup (SpecialLinearGroup (a ⊕ b) F)))
  refine le_antisymm ?_ (hperf _ (isPerfect_subgroupOf parJL_le_parQ (commutator_parJL hSL)))
  rw [← ker_chiR]
  exact (hiff _).1 (isSolvable_quotient_ker _ fun x y =>
    Units.ext (matrix_mul_comm_of_subsingleton _ _))

end CFSG.LieType.SteinbergBR.BlockPar
