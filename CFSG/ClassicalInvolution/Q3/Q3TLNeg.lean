module

public import CFSG.ClassicalInvolution.Q3.Q3TLFam
public import CFSG.ClassicalInvolution.Q3.Q3TLLin
public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussBasis

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

section Span

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem linearIndependent_of_polar_dual {ι : Type} [Fintype ι] [DecidableEq ι] (u w : ι → V)
    (h : ∀ i j, polar Q (u i) (w j) = if i = j then 1 else 0) : LinearIndependent K u := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 : polarBilin Q (∑ i, c i • u i) (w j) = 0 := by rw [hc, map_zero, LinearMap.zero_apply]
  rw [map_sum, LinearMap.sum_apply] at h1
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, h, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  exact h1

theorem polar_eq_zero_of_mem_span {ι : Type} (u : ι → V)
    (hpol : ∀ i j, polar Q (u i) (u j) = 0) {x y : V} (hx : x ∈ Submodule.span K (Set.range u))
    (hy : y ∈ Submodule.span K (Set.range u)) : polar Q x y = 0 := by
  have h1 : ∀ i, Submodule.span K (Set.range u) ≤ LinearMap.ker (polarBilin Q (u i)) := fun i =>
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hpol i j)
  have h2 : Submodule.span K (Set.range u) ≤ LinearMap.ker (polarBilin Q y) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      change polar Q y (u i) = 0
      rw [polar_comm]
      exact h1 i hy)
  have := h2 hx
  change polar Q y x = 0 at this
  rw [polar_comm]
  exact this

theorem eq_zero_of_mem_span {ι : Type} (u : ι → V) (hQ : ∀ i, Q (u i) = 0)
    (hpol : ∀ i j, polar Q (u i) (u j) = 0) {x : V}
    (hx : x ∈ Submodule.span K (Set.range u)) : Q x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hQ i
  | zero => exact QuadraticMap.map_zero Q
  | add x y hx hy ihx ihy =>
    rw [QuadraticMap.map_add Q, ihx, ihy, polar_eq_zero_of_mem_span u hpol hx hy, add_zero,
      add_zero]
  | smul c x _ ih => rw [QuadraticMap.map_smul, ih, smul_zero]

end Span

variable {K : Type} [Field K] [Finite K]

theorem not_fixFam_point_of_sq_eq_neg (hK : Nat.card K = 3) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = -x) :
    ¬ FixFam (statedPointFamily (coe_quadPlus 4 K))
      (Subgroup.zpowers (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))) := by
  intro h
  obtain ⟨w, hw0, -, hH⟩ := exists_of_fixFam_point h
  have hmem := (mk_mem_stabilizer_iff g _).mp (hH (Subgroup.mem_zpowers _))
  have hGw : toLinEquiv _ K g.val w ∈ K ∙ w := by
    rw [← hmem]
    exact ⟨w, Submodule.mem_span_singleton_self w, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hGw
  have h2 := hg2 w
  rw [← hc, map_smul, ← hc, smul_smul] at h2
  have h3 : (c * c + 1) • w = 0 := by rw [add_smul, h2, one_smul, neg_add_cancel]
  have h4 : c * c + 1 = 0 := (smul_eq_zero.mp h3).resolve_right hw0
  exact mul_self_ne_neg_one_of_card_three hK c (by linear_combination h4)

theorem fixFam_solid_of_sq_eq_neg (hK : Nat.card K = 3) (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = -x) :
    FixFam (conjugacyFamily
        (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)))
        (Subgroup.zpowers (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))) ∨
      FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
        (Xstar 4 K (by omega))))
        (Subgroup.zpowers
          (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))) := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  set G := toLinEquiv _ K g.val with hGdef
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hK (nondegenerate_polarBilin_quadPlus 4 K)
    (toLinEquiv_mem_orthogonalGroup g.2) hg2
  have hm4 : m = 4 := by
    have : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    omega
  subst hm4
  set b := ab.basis with hb
  have hGl : ∀ k, G (b (Sum.inl k)) = b (Sum.inr k) := fun k => (ab.inr_eq k).symm
  have hGr : ∀ k, G (b (Sum.inr k)) = -b (Sum.inl k) := fun k => by rw [hb, ab.inr_eq, hg2]
  have hpb : ∀ i j, polar (quadPlus 4 K) (b i) (b j) = if i = j then 1 else 0 := ab.orth
  set u : Fin 4 → (Fin 4 ⊕ Fin 4 → K) := ![b (.inl 0) + b (.inl 1) + b (.inr 1),
    b (.inr 0) + b (.inr 1) - b (.inl 1), b (.inl 2) + b (.inl 3) + b (.inr 3),
    b (.inr 2) + b (.inr 3) - b (.inl 3)] with hu
  have hpol : ∀ i j, polar (quadPlus 4 K) (u i) (u j) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, polar_add_left, polar_add_right, polar_sub_left, polar_sub_right, hpb,
        -QuadraticMap.polar_self] <;>
      linear_combination h3
  have hQu : ∀ i, quadPlus 4 K (u i) = 0 := fun i => by
    have h := hpol i i
    rw [QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.mp h).resolve_left h2
  set w : Fin 4 → (Fin 4 ⊕ Fin 4 → K) := ![b (.inl 0), b (.inr 0), b (.inl 2), b (.inr 2)]
    with hw
  have hdual : ∀ i j, polar (quadPlus 4 K) (u i) (w j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu, hw, polar_add_left, polar_sub_left, hpb]
  set S := Submodule.span K (Set.range u) with hS
  have hSdim : Module.finrank K S = 4 := by
    rw [hS, finrank_span_eq_card (linearIndependent_of_polar_dual u w hdual), Fintype.card_fin]
  have hSsing : S ∈ singularSubspaces (quadPlus 4 K) 4 :=
    ⟨hSdim, fun x hx => eq_zero_of_mem_span u hQu hpol hx⟩
  have hGu : ∀ i, G (u i) ∈ S := by
    have hmem : ∀ j, u j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    intro i
    fin_cases i
    · convert hmem 1 using 1
      simp [hu, map_add, hGl, hGr, sub_eq_add_neg]
    · convert S.neg_mem (hmem 0) using 1
      simp [hu, hGl, hGr]
      abel
    · convert hmem 3 using 1
      simp [hu, map_add, hGl, hGr, sub_eq_add_neg]
    · convert S.neg_mem (hmem 2) using 1
      simp [hu, hGl, hGr]
      abel
  have hinv : S.map G.toLinearMap = S := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
    rw [hS, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hGu i
  refine fixFam_solid_of_le hSsing (Subgroup.zpowers_le.mpr ?_)
  exact (mk_mem_stabilizer_iff g S).mpr hinv

theorem smul_eq_of_sq_eq_neg (hK : Nat.card K = 3)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) {k : ℕ} (hβk : β ^ (3 ^ k) = 1)
    (g : StatedOmega (StatedQuadPlus 4 K))
    (hg2 : ∀ x, toLinEquiv _ K g.val (toLinEquiv _ K g.val x) = -x)
    (hβg : β (QuotientGroup.mk g) = QuotientGroup.mk g) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  refine smul_eq_of_fixFam_solid β hβk ?_ (not_fixFam_point_of_sq_eq_neg hK g hg2)
    (fixFam_solid_of_sq_eq_neg hK g hg2)
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hβg

end CFSG.ClassicalInvolution.Q3.Q3T
