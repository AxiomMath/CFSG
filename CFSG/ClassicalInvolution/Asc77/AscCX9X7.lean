module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X6
public import CFSG.ClassicalInvolution.Asc77.AscCX9W
public import CFSG.ClassicalInvolution.Asc77.AscCX9X3

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F] {Y : Type} [Group Y] [Finite Y]
variable (θ : SL(4, F) →* Y) (hθ : Function.Surjective θ) (hker : θ.ker = scalars 4 F)

@[expose] def eTheta : projectiveSL 4 F ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ)

theorem eTheta_proj (s : SL(4, F)) : eTheta θ hθ hker (proj 4 F s) = θ s := rfl

@[expose] def cHat : Y ≃* Y :=
  (eTheta θ hθ hker).symm.trans ((conjAut 4 F d0GL).trans (eTheta θ hθ hker))

theorem cHat_apply (s : SL(4, F)) : cHat θ hθ hker (θ s) = θ (slConjugation 4 F d0GL s) := by
  have h1 : (eTheta θ hθ hker).symm (θ s) = proj 4 F s := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show eTheta θ hθ hker (conjAut 4 F d0GL ((eTheta θ hθ hker).symm (θ s))) = _
  rw [h1, conjAut_proj, eTheta_proj]

theorem map_cHat (H : Subgroup SL(4, F)) :
    (H.map θ).map (cHat θ hθ hker).toMonoidHom =
      (H.map (slConjugation 4 F d0GL).toMonoidHom).map θ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext s
  exact cHat_apply θ hθ hker s

include hker in
theorem theta_block0_injective :
    Function.Injective (θ.comp (blockSL F 4 2 0 (by norm_num))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro b hb
  have hb' : blockSL F 4 2 0 (by norm_num) b ∈ scalars 4 F := by
    rw [← hker]
    exact hb
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hb'
  rw [WeakCT.coe_blockSL, blockMat_four_zero] at hc
  have e33 := congrFun (congrFun hc 3) 3
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp at e33 e00 e01 e10 e11
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, ← e33]

theorem map_cHat_block0 :
    ((blockSL F 4 2 0 (by norm_num)).range.map θ).map (cHat θ hθ hker).toMonoidHom =
      (blockSL F 4 2 0 (by norm_num)).range.map θ := by
  rw [map_cHat]
  congr 1
  rw [← MonoidHom.range_comp]
  have h : (slConjugation 4 F d0GL).toMonoidHom.comp (blockSL F 4 2 0 (by norm_num)) =
      (blockSL F 4 2 0 (by norm_num)).comp (slConjugation 2 F c0GL).toMonoidHom := by
    ext b : 1
    exact d0_block0 b
  rw [h, range_comp_mulAut]

theorem cHat_fix_block2 {y : Y} (hy : y ∈ (blockSL F 4 2 2 (by norm_num)).range.map θ) :
    cHat θ hθ hker y = y := by
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
  rw [cHat_apply, d0_block2]

include hθ hker in
theorem diagWit_of_graph (p : ℕ) [Fact p.Prime] [CharP F p] [Finite F]
    (hsq : ¬ IsSquare (-1 : F)) (h4 : 4 ≤ Nat.card F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (A₁ A₂ : GL (Fin 4) F) (hA₁ : (A₁ : Matrix (Fin 4) (Fin 4) F) = spForm m n)
    (hA₂ : (A₂ : Matrix (Fin 4) (Fin 4) F) = spForm (-m) n) (β β' : MulAut Y)
    (hβ : ∀ s, β (θ s) = θ (slConjugation 4 F A₁ ((s⁻¹).transpose)))
    (hβ' : ∀ s, β' (θ s) = θ (slConjugation 4 F A₂ ((s⁻¹).transpose)))
    (hA : (blockSL F 4 2 0 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : (blockSL F 4 2 2 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : (blockSL F 4 2 0 (by norm_num)).range.map θ ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : (blockSL F 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β')) :
    DiagWit p (centTG _ _ β hA hA') (centTG _ _ β' hB hB') := by
  have hX₁ := perfRes_fix_eq h4 hm hn θ hθ hker A₁ hA₁ β hβ
  have hX₂ := perfRes_fix_eq h4 (neg_ne_zero.mpr hm) hn θ hθ hker A₂ hA₂ β' hβ'
  have hmapX : (Goldschmidt75.perfRes (fixSubgroup β)).map (cHat θ hθ hker).toMonoidHom =
      Goldschmidt75.perfRes (fixSubgroup β') := by
    rw [hX₁, hX₂, map_cHat, map_d0_spM]
  set φ : ↥(Goldschmidt75.perfRes (fixSubgroup β)) ≃* ↥(Goldschmidt75.perfRes (fixSubgroup β')) :=
    ((cHat θ hθ hker).subgroupMap (Goldschmidt75.perfRes (fixSubgroup β))).trans
      (MulEquiv.subgroupCongr hmapX) with hφ
  have hφv : ∀ x, (φ x : Y) = cHat θ hθ hker x := fun x => rfl
  have h0 := map_cHat_block0 θ hθ hker
  have hφA : (((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockSL F 4 2 0 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockSL F 4 2 0 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, ← h0]
      exact Subgroup.mem_map_of_mem _ hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf, ← h0] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨⟨x, hA hx⟩, Subgroup.mem_subgroupOf.mpr hx, Subtype.ext ?_⟩
      exact hxy
  have hφA' : (((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf
      (Goldschmidt75.perfRes (fixSubgroup β))).map (φ : _ →* _) =
      ((blockSL F 4 2 2 (by norm_num)).range.map θ).subgroupOf
        (Goldschmidt75.perfRes (fixSubgroup β')) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (x : Y) ∈ (blockSL F 4 2 2 (by norm_num)).range.map θ := hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (φ x : Y) ∈ _
      rw [hφv, cHat_fix_block2 θ hθ hker hx']
      exact hx'
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      refine ⟨⟨y, hA' hy⟩, Subgroup.mem_subgroupOf.mpr hy, Subtype.ext ?_⟩
      exact cHat_fix_block2 θ hθ hker hy
  refine ⟨φ, hφA, hφA', fun hiff => ?_⟩
  have hr' : DiagTriv p (TwinGroup.restr' (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA') := by
    intro u _
    refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    apply Subtype.ext
    exact (congrArg Subtype.val (TwinGroup.restr'_apply (L₁ := centTG _ _ β hA hA')
      (L₂ := centTG _ _ β' hB hB') φ hφA' u)).trans (cHat_fix_block2 θ hθ hker u.2)
  have hr := hiff.mpr hr'
  have hinj := theta_block0_injective θ hker
  set u : ↥((blockSL F 4 2 0 (by norm_num)).range.map θ) :=
    ⟨θ (blockSL F 4 2 0 (by norm_num) (uT 1)), Subgroup.mem_map_of_mem θ ⟨uT 1, rfl⟩⟩ with hu
  have hou : orderOf u = p := by
    rw [← Subgroup.orderOf_coe, hu]
    show orderOf ((θ.comp (blockSL F 4 2 0 (by norm_num))) (uT 1)) = p
    rw [orderOf_injective _ hinj, orderOf_upT_one p]
  obtain ⟨g, hg⟩ := hr u hou
  obtain ⟨_, ⟨b, rfl⟩, hgb⟩ := g.2
  have e1 : (TwinGroup.restr (L₁ := centTG _ _ β hA hA') (L₂ := centTG _ _ β' hB hB') φ hφA u :
      Y) = θ (blockSL F 4 2 0 (by norm_num) (uT (-1))) := by
    show cHat θ hθ hker (θ (blockSL F 4 2 0 (by norm_num) (uT 1))) = _
    rw [cHat_apply, d0_block0, c0_upT]
  have e2 := congrArg Subtype.val hg
  rw [e1] at e2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu] at e2
  rw [← hgb, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at e2
  exact upT_not_conj hsq (hinj e2).symm

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
