module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SimpleGroupReductions
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Nc
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks StabL
open scoped MatrixGroups

namespace FL4

section Generic

variable {X : Type} [Group X]

theorem normal_of_perfect_max {C H : Subgroup X} (hHC : H ≤ C) (hHp : ⁅H, H⁆ = H)
    (hmax : ∀ M : Subgroup X, M ≤ C → ⁅M, M⁆ = M → M ≤ H) : (H.subgroupOf C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hM := hmax (H.map (MulAut.conj (g : X)).toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem g.2 (hHC hx)) (inv_mem g.2))
    (by rw [← Subgroup.map_commutator, hHp])
  have := hM ⟨n, hn, rfl⟩
  simpa using this

theorem isQuasisimple_of_simple {H : Subgroup X} [IsSimpleGroup H] [Group.IsPerfect H] :
    CFSG.Open.IsQuasisimple H := by
  have hZ : Subgroup.center H = ⊥ :=
    DisconnectedInvolutionGraph.Helpers.simple_nonabelian_center_eq_bot
      Q5L4.exists_ne_comm_of_perfect
  exact ⟨Group.IsPerfect.commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩

theorem center_eq_bot_of_perfect [IsSimpleGroup X] (H : Subgroup X) [Nontrivial H]
    [Group.IsPerfect H] : Subgroup.center X = ⊥ := by
  obtain ⟨a, b, hab⟩ := Q5L4.exists_ne_comm_of_perfect (H := H)
  exact DisconnectedInvolutionGraph.Helpers.simple_nonabelian_center_eq_bot
    ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem center_eq_bot_of_sl2 [IsSimpleGroup X] {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (ψ : SL(2, F) →* X) (hψ : Function.Injective ψ) :
    Subgroup.center X = ⊥ := by
  have : Nontrivial (SL(2, F)) := ⟨⟨PSpL.slU 1, 1, fun h => by
    have := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) h)
      0) 1
    simp [PSpL.slU, uu] at this⟩⟩
  have : Group.IsPerfect (SL(2, F)) := (GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4).1
  obtain ⟨a, b, hab⟩ := Q5L4.exists_ne_comm_of_perfect (H := SL(2, F))
  refine DisconnectedInvolutionGraph.Helpers.simple_nonabelian_center_eq_bot
    ⟨ψ a, ψ b, fun h => hab (hψ ?_)⟩
  rw [map_mul, map_mul, h]

theorem layerExcludesQ8_of_simple (hZ : Subgroup.center X = ⊥) {t : X} {H : Subgroup X}
    [IsSimpleGroup H] [Group.IsPerfect H] (hHt : H ≤ Subgroup.centralizer ({t} : Set X))
    (hmax : ∀ M : Subgroup X, M ≤ Subgroup.centralizer ({t} : Set X) → ⁅M, M⁆ = M → M ≤ H)
    (hfix : NoQ8Fix X H) : LayerExcludesQ8 X t := by
  have hK : IsComponentOf H (Subgroup.centralizer ({t} : Set X)) :=
    isComponentOf_of_normal hHt (normal_of_perfect_max hHt
      (Subgroup.isPerfect_iff.mp inferInstance) hmax) isQuasisimple_of_simple
  exact layerExcludesQ8_of_noQ8Fix hZ (fun _ _ hg h hh => hg H hK h hh) hfix

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem normal_inl (β : SL(2, F) × SL(2, F) →* X) :
    ((β.comp (MonoidHom.inl _ _)).range.subgroupOf β.range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha⟩ := hn
  obtain ⟨⟨x, y⟩, hxy⟩ := g.2
  refine ⟨x * a * x⁻¹, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply] at ha ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hxy, ← ha, ← map_inv, ← map_mul,
    ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_inv_cancel]

omit [Finite F] in
theorem normal_inr (β : SL(2, F) × SL(2, F) →* X) :
    ((β.comp (MonoidHom.inr _ _)).range.subgroupOf β.range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨b, hb⟩ := hn
  obtain ⟨⟨x, y⟩, hxy⟩ := g.2
  refine ⟨y * b * y⁻¹, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply] at hb ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hxy, ← hb, ← map_inv, ← map_mul,
    ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, mul_inv_cancel]

theorem layerExcludesQ8_of_block (hZ : Subgroup.center X = ⊥) {t : X} (h4 : 4 ≤ Nat.card F)
    (β : SL(2, F) × SL(2, F) →* X) (hinl : Function.Injective (β.comp (MonoidHom.inl _ _)))
    (hinr : Function.Injective (β.comp (MonoidHom.inr _ _)))
    (hHt : β.range ≤ Subgroup.centralizer ({t} : Set X)) (hHp : ⁅β.range, β.range⁆ = β.range)
    (hmax : ∀ M : Subgroup X, M ≤ Subgroup.centralizer ({t} : Set X) → ⁅M, M⁆ = M →
      M ≤ β.range) (hfix : NoQ8Fix X β.range) : LayerExcludesQ8 X t := by
  set C := Subgroup.centralizer ({t} : Set X) with hC
  have hnH := normal_of_perfect_max hHt hHp hmax
  have hle1 : (β.comp (MonoidHom.inl _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hle2 : (β.comp (MonoidHom.inr _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hK1 : IsComponentOf (β.comp (MonoidHom.inl _ _)).range C :=
    ⟨hle1.trans hHt, IsSubnormal.step hle1 (normal_inl β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinl).symm⟩
  have hK2 : IsComponentOf (β.comp (MonoidHom.inr _ _)).range C :=
    ⟨hle2.trans hHt, IsSubnormal.step hle2 (normal_inr β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinr).symm⟩
  refine layerExcludesQ8_of_noQ8Fix hZ (fun g _ hg h hh => ?_) hfix
  obtain ⟨⟨a, b⟩, rfl⟩ := hh
  have e : β (a, b) = (β.comp (MonoidHom.inl _ _)) a * (β.comp (MonoidHom.inr _ _)) b := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply]
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e]
  exact commute_of_mem_sup (hg _ hK1) (hg _ hK2) _
    (mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩))

end Generic

section L4

variable {K : Type} [Field K]

theorem injective_inl (P : GL (Fin 4) K) :
    Function.Injective (((proj 4 K).comp (bdHom P)).comp (MonoidHom.inl _ _)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 ha)
  have hc' : ((bdHom P (a, 1) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.scalar (Fin 4) (c : K) := hc
  have e : bd (a : Matrix (Fin 2) (Fin 2) K) ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := by
    rw [← Q3L4.cP4_bdHom_mk P a 1, Q3L4.cP4, hc', Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 := congrFun (congrFun (congrArg lr e) 0) 0
  rw [lr_bd, Matrix.SpecialLinearGroup.coe_one] at e2
  simp [lr] at e2
  have e1 := congrArg ul e
  rw [ul_bd, ← e2, one_smul] at e1
  refine Subtype.ext ?_
  rw [e1, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul]

theorem injective_inr (P : GL (Fin 4) K) :
    Function.Injective (((proj 4 K).comp (bdHom P)).comp (MonoidHom.inr _ _)) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hb)
  have hc' : ((bdHom P (1, b) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.scalar (Fin 4) (c : K) := hc
  have e : bd ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := by
    rw [← Q3L4.cP4_bdHom_mk P 1 b, Q3L4.cP4, hc', Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 := congrFun (congrFun (congrArg ul e) 0) 0
  rw [ul_bd, Matrix.SpecialLinearGroup.coe_one] at e2
  simp [ul] at e2
  have e1 := congrArg lr e
  rw [lr_bd, ← e2, one_smul] at e1
  refine Subtype.ext ?_
  rw [e1, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr]

theorem center_eq_bot [Finite K] (h4 : 4 ≤ Nat.card K) :
    Subgroup.center (projectiveSL 4 K) = ⊥ := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 4) (by norm_num)
    (Or.inl (by norm_num))).2.1
  have : IsSimpleGroup (projectiveSL 4 K) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K).symm.isSimpleGroup
  exact center_eq_bot_of_sl2 h4 _ (injective_inl 1)

end L4

end FL4

end CFSG.ClassicalInvolution.Q3.TA3.Frame
