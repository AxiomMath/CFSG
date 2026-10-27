module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompInner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
public import CFSG.LieType.Chevalley.E6PinnedAdjoint
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Fix

variable
  {K : Type} [Field K]

theorem pinnedX_rootVec_of_not_add_root {δ μ : Fin Tag.E6.rank → ℤ} (hδ : IsRoot .E6 δ)
    (hμ : IsRoot .E6 μ) (h : ¬IsRoot .E6 (μ + δ)) (hne : μ ≠ δ) (hne' : μ ≠ -δ) (c : K) :
    (pinnedX Tag.E6 K δ c : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K μ) =
      rootVec Tag.E6 K μ := by
  set w := (pinnedData Tag.E6 δ).2.1 with hw
  set j := (pinnedData Tag.E6 δ).1 with hj
  have hfold : wordReflect Tag.E6 w (Pi.single j 1) = δ := foldl_reflect_pinnedData hδ
  set μ' := wordReflectInv Tag.E6 w μ with hμ'
  have hμ'r : IsRoot Tag.E6 μ' := E6PinnedAdjoint.wordReflectInv_isRoot w hμ
  have hback : wordReflect Tag.E6 w μ' = μ := wordReflect_wordReflectInv w μ
  have hsum : wordReflect Tag.E6 w (μ' + Pi.single j 1) = μ + δ := by
    rw [wordReflect_add, hback, hfold]
  have hroot : ¬IsRoot Tag.E6 (μ' + Pi.single j 1) := fun hr =>
    h (by rw [← hsum]; exact E6PinnedAdjoint.wordReflect_isRoot w hr)
  have hne₁ : μ' ≠ Pi.single j 1 := fun e => hne (by rw [← hback, e, hfold])
  have hne₂ : μ' ≠ -Pi.single j 1 := by
    intro e
    have h0 : wordReflect Tag.E6 w (0 : Fin Tag.E6.rank → ℤ) = 0 := by
      simpa using wordReflect_nsmul (τ := Tag.E6) w 0 0
    rw [e, neg_add_cancel, h0] at hsum
    exact hne' (eq_neg_of_add_eq_zero_left hsum.symm)
  obtain ⟨s₁, hs₁, h₁⟩ := E6PinnedAdjoint.prodWeyl_rootVec_sgn (K := K) w hμ'r
  rw [hback] at h₁
  have hW₁ : (pinnedWeyl Tag.E6 K δ : Module.End K (RootModule Tag.E6 K))
      (rootVec Tag.E6 K μ') = s₁ • rootVec Tag.E6 K μ := h₁
  have hWinv := E6PinnedAdjoint.units_inv_apply_of_apply_eq (pinnedWeyl Tag.E6 K δ) s₁ hs₁ hW₁
  have hs₁sq : s₁ * s₁ = 1 := by rcases hs₁ with rfl | rfl <;> simp
  have hx : (xOp Tag.E6 K j (((pinnedData Tag.E6 δ).2.2 • c : K)))
      (rootVec Tag.E6 K μ') = rootVec Tag.E6 K μ' := by
    rw [C2E6Std.xOp_rootVec_E6 j _ hμ'r hne₁ hne₂,
      show rootVec Tag.E6 K (μ' + Pi.single j 1) = 0 from dif_neg hroot, smul_zero, add_zero]
  have hpin : (pinnedX Tag.E6 K δ c : Module.End K (RootModule Tag.E6 K)) =
      (pinnedWeyl Tag.E6 K δ : Module.End K (RootModule Tag.E6 K)) *
        xOp Tag.E6 K j (((pinnedData Tag.E6 δ).2.2 • c : K)) *
        ((pinnedWeyl Tag.E6 K δ)⁻¹ : (Module.End K (RootModule Tag.E6 K))ˣ) :=
    rfl
  rw [hpin, Module.End.mul_apply, Module.End.mul_apply, hWinv, map_smul, hx, map_smul, hW₁,
    smul_smul, hs₁sq, one_smul]

theorem e6LineFactor_fix_rootVec {i j : Fin 3} (hij : i ≠ j) {μ : Fin Tag.E6.rank → ℤ}
    (hμ : μ ∈ e6LineRoots i) {g : ModGL Tag.E6 K} (hg : g ∈ e6LineFactor K j) :
    (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K μ) = rootVec Tag.E6 K μ := by
  let F : Subgroup (ModGL Tag.E6 K) :=
    { carrier := {g | (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K μ) =
        rootVec Tag.E6 K μ}
      one_mem' := by
        simp only [Set.mem_setOf_eq, Units.val_one, Module.End.one_apply]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Units.val_mul, Module.End.mul_apply] at ha hb ⊢
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply] }
  have hle : e6LineFactor K j ≤ F := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le F).2 ?_
    rintro _ ⟨c, rfl⟩
    have hβ' : β ∈ e6LineRoots j := hβ
    obtain ⟨hne, hne'⟩ := ne_and_ne_neg_of_e6LineRoots i j hij μ hμ β hβ'
    have hnr := not_isRoot_nsmul_add_of_e6LineRoots hij hμ hβ' one_pos one_pos
    rw [one_smul, one_smul] at hnr
    exact pinnedX_rootVec_of_not_add_root (isRoot_of_mem_e6LineRoots hβ')
      (isRoot_of_mem_e6LineRoots hμ) hnr hne hne' c
  exact hle hg

private theorem hVec_fix_of_commute (i : Fin Tag.E6.rank) {u : ModGL Tag.E6 K}
    (hc : u * xUnit Tag.E6 K i 1 = xUnit Tag.E6 K i 1 * u)
    (hp : (u : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (Pi.single i 1)) =
      rootVec Tag.E6 K (Pi.single i 1))
    (hn : (u : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (-Pi.single i 1)) =
      rootVec Tag.E6 K (-Pi.single i 1)) :
    (u : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i) = hVec Tag.E6 K i := by
  have h := congrArg (fun g : ModGL Tag.E6 K =>
    (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (-Pi.single i 1))) hc
  simp only [Units.val_mul, Module.End.mul_apply, coe_xUnit, hn,
    CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single, map_add, map_smul, hp, one_smul,
    one_pow] at h
  exact add_left_cancel (add_right_cancel h)

private theorem xUnit_mem_e6LineFactor_zero {i : Fin Tag.E6.rank}
    (hi : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ e6LineRoots 0) :
    xUnit Tag.E6 K i 1 ∈ e6LineFactor K 0 := by
  rw [← pinnedX_single]
  exact pinnedX_mem_rootSpan (S := (e6LineRoots 0 : Set (Fin Tag.E6.rank → ℤ))) hi 1

theorem fix_of_commute_e6LineFactor_zero {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {u : ModGL Tag.E6 K} (hu : u ∈ toralRootGroup .E6 K (e6LineChar ω))
    (hcomm : ∀ g ∈ e6LineFactor K 0, u * g = g * u) :
    (∀ μ ∈ e6LineRoots 0, (u : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K μ) =
      rootVec Tag.E6 K μ) ∧
    (u : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K 0) = hVec Tag.E6 K 0 ∧
    (u : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K 2) = hVec Tag.E6 K 2 := by
  choose ρ σf hfr hrange using exists_frame_e6Line K
  have htor : ∀ i b s, rootDiagUnit Tag.E6 b * ρ i s * (rootDiagUnit Tag.E6 b)⁻¹ =
      ρ i (conjSL (diagGL3 fun j => rootChar b (σf i j 0)) s) := fun i b s => by
    rw [conjSL_diagGL3]
    exact (hfr i).torus b s
  obtain ⟨π, hπ, -, -, -, -, -, hMdec⟩ := exists_commProd_of_frames
    (D := fun i b => diagGL3 fun j => rootChar b (σf i j 0)) hw3 hw1 hrange htor
  obtain ⟨c, x, hc, rfl⟩ := hMdec u hu
  have hmemF : ∀ i s, ρ i s ∈ e6LineFactor K i := fun i s => (hrange i) ▸ ⟨s, rfl⟩
  set r : ModGL Tag.E6 K := ρ 1 (x 1) * ρ 2 (x 2) with hr
  set g₀ : ModGL Tag.E6 K := rootDiagUnit Tag.E6 c * ρ 0 (x 0) with hg₀
  have hdec : rootDiagUnit Tag.E6 c * π x = g₀ * r := by
    rw [hπ, hg₀, hr]
    simp only [mul_assoc]
  have hrfix : ∀ μ ∈ e6LineRoots 0, (r : Module.End K (RootModule Tag.E6 K))
      (rootVec Tag.E6 K μ) = rootVec Tag.E6 K μ := fun μ hμ => by
    rw [hr, Units.val_mul, Module.End.mul_apply,
      e6LineFactor_fix_rootVec (by decide) hμ (hmemF 2 _),
      e6LineFactor_fix_rootVec (by decide) hμ (hmemF 1 _)]
  have hrc : ∀ g ∈ e6LineFactor K 0, r * g = g * r := fun g hg => by
    have h1 := e6LineFactor_commute (by decide : (1 : Fin 3) ≠ 0) (hmemF 1 (x 1)) hg
    have h2 := e6LineFactor_commute (by decide : (2 : Fin 3) ≠ 0) (hmemF 2 (x 2)) hg
    calc r * g = ρ 1 (x 1) * (ρ 2 (x 2) * g) := by rw [hr, mul_assoc]
      _ = ρ 1 (x 1) * g * ρ 2 (x 2) := by rw [h2, mul_assoc]
      _ = g * r := by rw [h1, hr, mul_assoc]
  have hg₀c : ∀ g ∈ e6LineFactor K 0, g₀ * g = g * g₀ := fun g hg => by
    have h1 := hcomm g hg
    rw [hdec] at h1
    apply mul_right_cancel (b := r)
    calc g₀ * g * r = g₀ * (r * g) := by rw [mul_assoc, hrc g hg]
      _ = g * (g₀ * r) := by rw [← mul_assoc g₀ r g, h1]
      _ = g * g₀ * r := (mul_assoc g g₀ r).symm
  have hg₀conj : ∀ s, g₀ * ρ 0 s * g₀⁻¹ = ρ 0 (conjSL ((diagGL3 fun j => rootChar c (σf 0 j 0)) *
      SpecialLinearGroup.toGL (x 0)) s) := fun s => by
    rw [map_mul, MulAut.mul_apply, conjSL_toGL, MulAut.conj_apply, ← htor 0 c, map_mul, map_mul,
      map_inv, hg₀]
    group
  have hscal : conjSL ((diagGL3 fun j => rootChar c (σf 0 j 0)) *
      SpecialLinearGroup.toGL (x 0)) = 1 := by
    refine MulEquiv.ext fun s => (hfr 0).injective ?_
    rw [MulAut.one_apply, ← hg₀conj, hg₀c (ρ 0 s) (hmemF 0 s), mul_inv_cancel_right]
  obtain ⟨κ, hκ⟩ := exists_smul_one_of_conjSL_eq_one hscal
  have hoff : ∀ i j, i ≠ j → ((x 0 : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hκ i) j
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      show ((diagGL3 fun j => rootChar c (σf 0 j 0) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal fun j => ((rootChar c (σf 0 j 0) : Kˣ) : K) from rfl,
      Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (Units.ne_zero _)
  have hg₀T : g₀ ∈ torusGroup Tag.E6 K := mul_mem hc ((hfr 0).diag (x 0) hoff)
  obtain ⟨e, he⟩ := torusGroup_le_range_rootDiagUnitHom_E6 hg₀T
  have he' : rootDiagUnit Tag.E6 e = g₀ := he
  have hchar : ∀ μ ∈ e6LineRoots 0, ((rootChar e μ : Kˣ) : K) = 1 := fun μ hμ => by
    have hμr := isRoot_of_mem_e6LineRoots hμ
    have hX : pinnedX Tag.E6 K μ 1 ∈ e6LineFactor K 0 :=
      pinnedX_mem_rootSpan (S := (e6LineRoots 0 : Set (Fin Tag.E6.rank → ℤ))) hμ 1
    have h1 := hg₀c _ hX
    rw [← he'] at h1
    have h2 : rootDiagUnit Tag.E6 e * pinnedX Tag.E6 K μ 1 * (rootDiagUnit Tag.E6 e)⁻¹ =
        pinnedX Tag.E6 K μ 1 := by
      rw [h1, mul_inv_cancel_right]
    rw [rootDiagUnit_conj_pinnedX e hμr 1, mul_one] at h2
    exact pinnedX_injective Tag.E6 K μ h2
  have hg₀fix : ∀ μ ∈ e6LineRoots 0, (g₀ : Module.End K (RootModule Tag.E6 K))
      (rootVec Tag.E6 K μ) = rootVec Tag.E6 K μ := fun μ hμ => by
    rw [← he']
    change rootDiag e (rootVec Tag.E6 K μ) = rootVec Tag.E6 K μ
    rw [rootDiag_rootVec e (isRoot_of_mem_e6LineRoots hμ), hchar μ hμ, one_smul]
  have hufix : ∀ μ ∈ e6LineRoots 0,
      ((rootDiagUnit Tag.E6 c * π x : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K μ) = rootVec Tag.E6 K μ := fun μ hμ => by
    rw [hdec, Units.val_mul, Module.End.mul_apply, hrfix μ hμ, hg₀fix μ hμ]
  refine ⟨hufix, ?_, ?_⟩
  · exact hVec_fix_of_commute 0 (hcomm _ (xUnit_mem_e6LineFactor_zero (by decide)))
      (hufix _ (by decide)) (hufix _ (by decide))
  · exact hVec_fix_of_commute 2 (hcomm _ (xUnit_mem_e6LineFactor_zero (by decide)))
      (hufix _ (by decide)) (hufix _ (by decide))

private theorem finrank_rootModule_e6Fix : Module.finrank K (RootModule Tag.E6 K) = 78 := by
  rw [Module.finrank_finsupp_self, Fintype.card_sum, Fintype.card_fin, card_isRoot]
  rfl

private theorem eight_le_finrank (W : Submodule K (RootModule Tag.E6 K))
    (h0 : hVec Tag.E6 K 0 ∈ W) (h2 : hVec Tag.E6 K 2 ∈ W)
    (hμ : ∀ μ ∈ e6LineRoots 0, rootVec Tag.E6 K μ ∈ W) : 8 ≤ Module.finrank K W := by
  classical
  let g : Fin 2 ⊕ ↥(e6LineRoots 0) → Label Tag.E6 :=
    Sum.elim (fun j => Sum.inl (![0, 2] j))
      (fun μ => Sum.inr ⟨μ.1, isRoot_of_mem_e6LineRoots μ.2⟩)
  have h02 : Function.Injective (![0, 2] : Fin 2 → Fin Tag.E6.rank) := by decide
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (h02 (Sum.inl.inj h))
    · cases h
    · cases h
    · have h' : (⟨a.1, isRoot_of_mem_e6LineRoots a.2⟩ : {v : Fin Tag.E6.rank → ℤ // IsRoot .E6 v}) =
          ⟨b.1, isRoot_of_mem_e6LineRoots b.2⟩ := Sum.inr.inj h
      exact congrArg Sum.inr (Subtype.ext (Subtype.mk.inj h'))
  have hmem : ∀ k, Finsupp.single (g k) (1 : K) ∈ W := by
    rintro (j | μ)
    · fin_cases j
      · exact h0
      · exact h2
    · have e : Finsupp.single (g (Sum.inr μ)) (1 : K) = rootVec Tag.E6 K μ.1 :=
        (rootVec_eq_single_of_isRoot (isRoot_of_mem_e6LineRoots μ.2)).symm
      rw [e]
      exact hμ μ.1 μ.2
  have hli : LinearIndependent K (fun k => (⟨_, hmem k⟩ : W)) :=
    LinearIndependent.of_comp W.subtype
      ((Finsupp.linearIndependent_single_one K (Label Tag.E6)).comp g hg)
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, card_e6LineRoots] at hcard
  exact hcard

theorem false_of_commute_e6LineFactor_zero {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    (h3 : (3 : K) ≠ 0) {u : ModGL Tag.E6 K} (hu : u ∈ toralRootGroup .E6 K (e6LineChar ω))
    (hcomm : ∀ g ∈ e6LineFactor K 0, u * g = g * u) (hu3 : u ^ 3 = 1)
    (h1 : Module.finrank K
      (LinearMap.ker ((u : Module.End K (RootModule Tag.E6 K)) - 1)) = 24)
    (h2 : Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) * u : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) - 1)) = 24)
    (h4 : Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) ^ 2 * u : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) - 1)) = 24) : False := by
  have hFM : e6LineFactor K 0 ≤ toralRootGroup .E6 K (e6LineChar ω) := by
    show _ ≤ torusGroup .E6 K ⊔ rootSpan .E6 K (rootCharKernel (e6LineChar ω))
    rw [e6Line_kernel hw3 hw1, rootSpan_eq_iSup_e6LineFactor]
    exact (le_iSup (fun i => e6LineFactor K i) 0).trans le_sup_right
  have hh₀M : rootDiagUnit .E6 (e6LineChar ω) ∈ toralRootGroup .E6 K (e6LineChar ω) :=
    Subgroup.mem_sup_left (e6Line_diag_mem_torusGroup ω)
  have hcomm₀ : ∀ g ∈ toralRootGroup .E6 K (e6LineChar ω),
      rootDiagUnit .E6 (e6LineChar ω) * g = g * rootDiagUnit .E6 (e6LineChar ω) :=
    fun g hg => by
      have h := (mem_toralCentralizer.1 (toralRootGroup_le _ hg)).2
      calc rootDiagUnit .E6 (e6LineChar ω) * g
          = rootDiagUnit .E6 (e6LineChar ω) * g * (rootDiagUnit .E6 (e6LineChar ω))⁻¹ *
              rootDiagUnit .E6 (e6LineChar ω) := by group
        _ = g * rootDiagUnit .E6 (e6LineChar ω) := by rw [h]
  have hFV := fix_of_commute_e6LineFactor_zero hw3 hw1 hu hcomm
  have hFV₀ := fix_of_commute_e6LineFactor_zero hw3 hw1 hh₀M fun g hg => hcomm₀ g (hFM hg)
  have hh₀3 : rootDiagUnit .E6 (e6LineChar ω) ^ 3 = (1 : ModGL Tag.E6 K) := by
    have e : (e6LineChar ω) ^ 3 = 1 := funext fun i => by
      rw [Pi.pow_apply, e6LineChar_pow_three hw3 i, Pi.one_apply]
    show (rootDiagUnitHom Tag.E6 K (e6LineChar ω)) ^ 3 = 1
    rw [← map_pow, e, map_one]
  have ha3 : ((rootDiagUnit .E6 (e6LineChar ω) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hh₀3, Units.val_one]
  have hb3 : (u : Module.End K (RootModule Tag.E6 K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hab : Commute ((rootDiagUnit .E6 (e6LineChar ω) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) (u : Module.End K (RootModule Tag.E6 K)) := by
    show _ * _ = _ * _
    rw [← Units.val_mul, ← Units.val_mul, hcomm₀ u hu]
  have hsum := finrank_lineSum h3 ha3 hb3 hab
  have hA : Module.finrank K (LinearMap.ker (((rootDiagUnit .E6 (e6LineChar ω) : ModGL Tag.E6 K) :
      Module.End K (RootModule Tag.E6 K)) - 1)) = 24 :=
    e6Line_finrank_fixed_aux hw3 hw1
  rw [Units.val_mul] at h2
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at h4
  rw [hA, h1, h2, h4, finrank_rootModule_e6Fix] at hsum
  have hmemW : ∀ y : RootModule Tag.E6 K,
      ((rootDiagUnit .E6 (e6LineChar ω) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) y = y →
      (u : Module.End K (RootModule Tag.E6 K)) y = y →
      y ∈ LinearMap.ker (((rootDiagUnit .E6 (e6LineChar ω) : ModGL Tag.E6 K) :
          Module.End K (RootModule Tag.E6 K)) - 1) ⊓
        LinearMap.ker ((u : Module.End K (RootModule Tag.E6 K)) - 1) := fun y hy₁ hy₂ =>
    Submodule.mem_inf.2
      ⟨by rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hy₁, sub_self],
        by rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hy₂, sub_self]⟩
  have h8 := eight_le_finrank _ (hmemW _ hFV₀.2.1 hFV.2.1) (hmemW _ hFV₀.2.2 hFV.2.2)
    fun μ hμ => hmemW _ (hFV₀.1 μ hμ) (hFV.1 μ hμ)
  omega

theorem false_of_commute_conj_e6LineFactor_zero {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    (h3 : (3 : K) ≠ 0) {v t : ModGL Tag.E6 K} (hv : v ∈ toralRootGroup .E6 K (e6LineChar ω))
    (ht : t ∈ Subgroup.normalizer (toralRootGroup .E6 K (e6LineChar ω) : Set (ModGL Tag.E6 K)))
    (hth : t * rootDiagUnit .E6 (e6LineChar ω) = rootDiagUnit .E6 (e6LineChar ω) * t)
    (hcomm : ∀ g ∈ e6LineFactor K 0, v * (t * g * t⁻¹) = t * g * t⁻¹ * v) (hv3 : v ^ 3 = 1)
    (h1 : Module.finrank K
      (LinearMap.ker ((v : Module.End K (RootModule Tag.E6 K)) - 1)) = 24)
    (h2 : Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) * v : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) - 1)) = 24)
    (h4 : Module.finrank K (LinearMap.ker
      (((rootDiagUnit .E6 (e6LineChar ω) ^ 2 * v : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) - 1)) = 24) : False := by
  have hu : t⁻¹ * v * t⁻¹⁻¹ ∈ toralRootGroup .E6 K (e6LineChar ω) :=
    (Subgroup.mem_normalizer_iff.1 (inv_mem ht) v).1 hv
  have hth2 : t * rootDiagUnit .E6 (e6LineChar ω) ^ 2 = rootDiagUnit .E6 (e6LineChar ω) ^ 2 * t :=
    (show Commute t (rootDiagUnit .E6 (e6LineChar ω)) from hth).pow_right 2
  have e1 : rootDiagUnit .E6 (e6LineChar ω) * (t⁻¹ * v * t⁻¹⁻¹) =
      t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) * v) * t⁻¹⁻¹ := by
    calc rootDiagUnit .E6 (e6LineChar ω) * (t⁻¹ * v * t⁻¹⁻¹)
        = t⁻¹ * (t * rootDiagUnit .E6 (e6LineChar ω)) * t⁻¹ * v * t := by group
      _ = t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) * t) * t⁻¹ * v * t := by rw [hth]
      _ = t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) * v) * t⁻¹⁻¹ := by group
  have e2 : rootDiagUnit .E6 (e6LineChar ω) ^ 2 * (t⁻¹ * v * t⁻¹⁻¹) =
      t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) ^ 2 * v) * t⁻¹⁻¹ := by
    calc rootDiagUnit .E6 (e6LineChar ω) ^ 2 * (t⁻¹ * v * t⁻¹⁻¹)
        = t⁻¹ * (t * rootDiagUnit .E6 (e6LineChar ω) ^ 2) * t⁻¹ * v * t := by group
      _ = t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) ^ 2 * t) * t⁻¹ * v * t := by rw [hth2]
      _ = t⁻¹ * (rootDiagUnit .E6 (e6LineChar ω) ^ 2 * v) * t⁻¹⁻¹ := by group
  refine false_of_commute_e6LineFactor_zero hw3 hw1 h3 hu (fun g hg => ?_) ?_ ?_ ?_ ?_
  · calc t⁻¹ * v * t⁻¹⁻¹ * g = t⁻¹ * (v * (t * g * t⁻¹)) * t := by group
      _ = t⁻¹ * (t * g * t⁻¹ * v) * t := by rw [hcomm g hg]
      _ = g * (t⁻¹ * v * t⁻¹⁻¹) := by group
  · rw [conj_pow, hv3, mul_one, mul_inv_cancel]
  · rw [finrank_ker_conj_sub_one]
    exact h1
  · rw [e1, finrank_ker_conj_sub_one]
    exact h2
  · rw [e2, finrank_ker_conj_sub_one]
    exact h4

end Fix

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
