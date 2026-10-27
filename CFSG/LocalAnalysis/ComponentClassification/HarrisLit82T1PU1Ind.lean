module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_semilinear_spinAction [Finite K] (h2 : (2 : K) ≠ 0)
    (α : MulAut (spinGroup (quadOdd 3 K))) :
    ∃ (σ : K ≃+* K) (F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)),
      (∀ (c : K) v, F (c • v) = σ c • F v) ∧ ∃ μ : K, μ ≠ 0 ∧
        (∀ v, quadOdd 3 K (F v) = μ * σ (quadOdd 3 K v)) ∧
        ∀ s v, spinAction (quadOdd 3 K) (α s) v = F (spinAction (quadOdd 3 K) s (F.symm v)) := by
  set κ : spinGroup (quadOdd 3 K) →* ProjOrthDerived (quadOdd 3 K) := spinProj h2 (le_refl 3)
    with hκ
  have hκs : Function.Surjective κ := spinProj_surjective h2 (le_refl 3)
  have hker : κ.ker = center (spinGroup (quadOdd 3 K)) := ker_spinProj h2 (le_refl 3)
  set ε : spinGroup (quadOdd 3 K) ⧸ center (spinGroup (quadOdd 3 K)) ≃*
      ProjOrthDerived (quadOdd 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective κ hκs)
  have hεmk : ∀ x, ε (QuotientGroup.mk x) = κ x := fun x => rfl
  set αb : MulAut (ProjOrthDerived (quadOdd 3 K)) :=
    MulAut.congr ε (PerfectAutomorphisms.onCenterQuotient α) with hαb
  have hαbκ : ∀ x, αb (κ x) = κ (α x) := by
    intro x
    rw [← hεmk, ← hεmk]
    simp only [hαb, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg ε (PerfectAutomorphisms.onCenterQuotient_apply_mk α x)
  have hdim : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨σ, F, hF, μ, hμ, hQF, hind⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le
      (quadOdd 3 K) (nondegenerate_polarBilin_quadOdd 3 K h2) hdim.ge
      (fun h => absurd (hdim.symm.trans h) (by norm_num)) αb
  refine ⟨σ, F, hF, μ, hμ, hQF, fun s v => ?_⟩
  set g' : orthDerived (quadOdd 3 K) := ⟨semiConj hF (spinAction (quadOdd 3 K) s),
    semiConj_mem_orthDerived hF hQF (spinOmega h2 (le_refl 3) s).2⟩ with hg'
  have h1 := hind (spinOmega h2 (le_refl 3) s) g' fun w => rfl
  have h3 : κ (α s) = QuotientGroup.mk g' := by
    rw [← hαbκ]
    exact h1
  rw [hκ, spinProj_apply, QuotientGroup.eq] at h3
  have h4 := eq_one_of_mem_scalars_quadOdd ((spinOmega h2 (le_refl 3) (α s))⁻¹ * g').2
    (Subgroup.mem_subgroupOf.mp h3)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one] at h4
  exact LinearEquiv.congr_fun h4 v

theorem sq_eq_smul_of_spinAction (h2 : (2 : K) ≠ 0) {σ : K ≃+* K}
    {F : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}
    (hF : ∀ (c : K) v, F (c • v) = σ c • F v) {μ : K}
    (hQF : ∀ v, quadOdd 3 K (F v) = μ * σ (quadOdd 3 K v))
    {α : MulAut (spinGroup (quadOdd 3 K))} (hα : α * α = 1)
    (hπ : ∀ s v, spinAction (quadOdd 3 K) (α s) v = F (spinAction (quadOdd 3 K) s (F.symm v))) :
    (∀ c, σ (σ c) = c) ∧ ∃ c : K, c ≠ 0 ∧ ∀ v, F (F v) = c • v := by
  have hcomm : ∀ s v, F (F (spinAction (quadOdd 3 K) s v)) =
      spinAction (quadOdd 3 K) s (F (F v)) := by
    intro s v
    have hαα : α (α s) = s := by
      have := congrArg (fun β : MulAut (spinGroup (quadOdd 3 K)) => β s) hα
      simpa using this
    have h1 := hπ (α s) (F (F v))
    rw [hαα, hπ s, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h1
    exact h1.symm
  set F2 : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃+ (Fin 3 ⊕ Fin 3 ⊕ Unit → K) := F.trans F with hF2d
  have hF2 : ∀ (c : K) v, F2 (c • v) = (σ.trans σ) c • F2 v := fun c v => by
    simp only [hF2d, AddEquiv.trans_apply, RingEquiv.trans_apply, hF]
  have hQ2 : ∀ v, quadOdd 3 K (F2 v) = (μ * σ μ) * (σ.trans σ) (quadOdd 3 K v) := fun v => by
    simp only [hF2d, AddEquiv.trans_apply, RingEquiv.trans_apply, hQF, map_mul]
    ring
  have hL : ∀ (A : SL(2, K)) v, F2 ((frame01 K).La A v) = (frame01 K).La A (F2 v) := by
    intro A v
    have h := hcomm ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true A) v
    rwa [spinAction_longSL2] at h
  have hR : ∀ (A : SL(2, K)) v, F2 ((frame01 K).swap.La A v) = (frame01 K).swap.La A (F2 v) := by
    intro A v
    have h := hcomm ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false A) v
    rwa [spinAction_longSL2, show (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false =
      (frame01 K).swap from toFrame_not _ fin3_zero_ne_one true true] at h
  have hS : ∀ (s : Bool) (c : K) v,
      F2 (spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) v) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) (F2 v) :=
    fun s c v => hcomm _ v
  obtain ⟨hσ2, c, hc0, hcases⟩ := eq_smul_or_eq_smul_La_of_commute h2 hF2 hQ2 hL hR hS
  refine ⟨fun c' => hσ2 c', c, hc0, ?_⟩
  rcases hcases with h | h
  · exact h
  exfalso
  have h' : ∀ v, F (F v) = c • (frame01 K).La (-1) v := h
  have hgf : spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 0 true (.ofAdd 1))
      ((oddFrame 3 K).vec 0 false) =
        (oddFrame 3 K).vec 0 false + (oddFrame 3 K).z - (oddFrame 3 K).vec 0 true := by
    have := (oddFrame 3 K).spinAction_shortRoot_vec_not 0 true 1
    rwa [Bool.not_true, one_smul, one_pow, one_smul] at this
  have hLf : (frame01 K).La (-1) ((oddFrame 3 K).vec 0 false) = -(oddFrame 3 K).vec 0 false :=
    ((frame01 K).mem_span_iff_inv h2).mp (frame01 K).f₁_mem_span
  have hLe : (frame01 K).La (-1) ((oddFrame 3 K).vec 0 true) = -(oddFrame 3 K).vec 0 true :=
    ((frame01 K).mem_span_iff_inv h2).mp (frame01 K).e₁_mem_span
  have hLz : (frame01 K).La (-1) (oddFrame 3 K).z = (oddFrame 3 K).z := La_neg_one_apply_z
  have hk := hcomm ((oddFrame 3 K).shortRoot 0 true (.ofAdd 1)) ((oddFrame 3 K).vec 0 false)
  rw [h', h', map_smul] at hk
  have hk' := smul_right_injective _ hc0 hk
  rw [hgf, map_sub, map_add, hLf, hLe, hLz, map_neg, hgf] at hk'
  have hz : (2 : K) • (oddFrame 3 K).z = 0 := by linear_combination (norm := module) hk'
  have hz0 : (oddFrame 3 K).z = 0 := (smul_eq_zero.mp hz).resolve_left h2
  have hQz : quadOdd 3 K (oddFrame 3 K).z = 1 := quadOdd_oddZ 3 K
  rw [hz0, QuadraticMap.map_zero] at hQz
  exact zero_ne_one hQz

end CFSG.ComponentClassification.HarrisLit.T1
