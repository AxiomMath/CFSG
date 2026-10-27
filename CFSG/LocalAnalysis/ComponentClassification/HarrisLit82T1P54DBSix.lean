module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Klein
public import CFSG.ClassicalInvolution.SmallOrth.Perfect

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isQuasisimple_statedOmega_six (hodd : Odd (Nat.card K)) {Q : QuadraticForm K (ι → K)}
    {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) (hnd : Q.polarBilin.Nondegenerate)
    (hdim : Fintype.card ι = 6) : IsQuasisimple (StatedOmega Q₀) :=
  LocalCores.isQuasisimple_of_mulEquiv ((Klein.commutatorEquiv Q).trans (statedOmegaEquiv hQ₀).symm)
    (Klein.isQuasisimple_commutator_orthogonalSix hodd Q hnd
      (by rw [Module.finrank_fintype_fun_eq_card, hdim]))

theorem exists_lieModel_six {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hnd : Q.polarBilin.Nondegenerate) (hdim : Fintype.card ι = 6)
    (hq : IsQuasisimple (StatedOmega Q₀)) :
    ∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (StatedOmega Q₀ ⧸ center (StatedOmega Q₀)) τ' n' p f := by
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h => by simp [h] at h5
  refine Klein.exists_lieModel_of_orthogonalSix_cover' hp hp2 hf hK Q hnd
    (by rw [Module.finrank_fintype_fun_eq_card, hdim]) hq (statedOmegaEquiv hQ₀).toMonoidHom
    (statedOmegaEquiv hQ₀).surjective fun x hx => ?_
  have h1 : statedOmegaEquiv hQ₀ x = statedOmegaEquiv hQ₀ 1 := by
    rw [map_one]
    exact hx
  rw [(statedOmegaEquiv hQ₀).injective h1]
  exact one_mem _

variable {b c : K}

theorem neg_one_mem_statedOmega_quadMinus_three (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hsq : IsSquare (4 * c - b ^ 2)) :
    (-1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadMinus 3 K b c) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have h4c : 4 * c - b ^ 2 ≠ 0 := by
    intro h
    apply hirr (-b / 2)
    field_simp
    linear_combination h
  have hP : ∀ i j : Fin (3 - 1), i ≠ j →
      (minusPair K b c i).Orth (minusPair K b c j) := fun i j hij => minusPair_orth hij
  set pv₀ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1
    with hpv₀
  set pv₁ : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
    (-b) • Pi.single (Sum.inr (Sum.inr 0)) 1 + (2 : K) • Pi.single (Sum.inr (Sum.inr 1)) 1
    with hpv₁
  have hq0 : quadMinus 3 K b c pv₀ = 1 := by
    rw [quadMinus_apply]
    simp [hpv₀]
  have hq1 : quadMinus 3 K b c pv₁ = 4 * c - b ^ 2 := by
    rw [quadMinus_apply]
    simp [hpv₁]
    ring
  have hp01 : QuadraticMap.polar (quadMinus 3 K b c) pv₀ pv₁ = 0 := by
    rw [polar_quadMinus]
    simp [hpv₀, hpv₁]
    ring
  set l : List (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    hypList (minusPair K b c : Fin (3 - 1) → HypPair (quadMinus 3 K b c)) ++ [pv₀, pv₁] with hl
  have hpv0 : ∀ i, pv₀ (Sum.inl i) = 0 := fun i => by simp [hpv₀]
  have hpv0' : ∀ i, pv₀ (Sum.inr (Sum.inl i)) = 0 := fun i => by simp [hpv₀]
  have hpv1 : ∀ i, pv₁ (Sum.inl i) = 0 := fun i => by simp [hpv₁]
  have hpv1' : ∀ i, pv₁ (Sum.inr (Sum.inl i)) = 0 := fun i => by simp [hpv₁]
  have hl0 : ∀ a ∈ l, quadMinus 3 K b c a ≠ 0 := by
    intro a ha
    rw [hl, List.mem_append] at ha
    rcases ha with ha | ha
    · exact hypList_map_ne_zero a ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [hq0]
        exact one_ne_zero
      · rw [hq1]
        exact h4c
  have hpair : l.Pairwise (fun u v => QuadraticMap.polar (quadMinus 3 K b c) u v = 0) := by
    rw [hl, List.pairwise_append]
    refine ⟨hypList_pairwise hP, ?_, ?_⟩
    · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      exact hp01
    · intro x hx y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact polar_hypList_of_plane 3 hpv0 hpv0' hx
      · exact polar_hypList_of_plane 3 hpv1 hpv1' hx
  have hlen : l.length = Module.finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) := by
    rw [hl, List.length_append, hypList_length, Module.finrank_fintype_fun_eq_card]
    simp
  have hprod := prod_map_reflect_eq_neg hl0 hpair (span_eq_top_of_pairwise_polar h2 hl0 hpair hlen)
  have hE : (LinearEquiv.neg K : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃ₗ[K] _) ∈
      elementaryGroup (quadMinus 3 K b c) := by
    rw [← hprod]
    refine prod_map_reflect_mem_elementaryGroup hnd
      (minusPair_orth (K := K) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (by simp)) hl0
      ⟨3, by rw [hl, List.length_append, hypList_length]; rfl⟩ ?_
    have hval : (l.map (quadMinus 3 K b c)).prod = 4 * c - b ^ 2 := by
      rw [hl, List.map_append, List.prod_append, hypList_prod_map]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, hq0, hq1]
      norm_num
    rw [hval]
    exact hsq
  obtain ⟨τ, hτ, hτ2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K h4
  have hEp := Small.commutator_elementaryGroup_eq_top_small h2 hnd
    (Small.hasAnisoPerp_of_three_le_finrank hnd
      (by rw [Module.finrank_fintype_fun_eq_card]; simp)) hτ hτ2
  have hEO : elementaryGroup (quadMinus 3 K b c) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ := by
    rw [← Subgroup.isPerfect_iff.mp ⟨hEp⟩]
    exact commutator_mono (elementaryGroup_le_orthogonalGroup _)
      (elementaryGroup_le_orthogonalGroup _)
  have e : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K (-1) = LinearEquiv.neg K := by
    refine LinearEquiv.ext fun x => ?_
    rw [toLinEquiv_apply, Units.val_neg, Units.val_one, neg_mulVec, one_mulVec]
    rfl
  rw [statedOmega_eq_comap (coe_quadMinus 3 K b c), mem_comap, MulEquiv.coe_toMonoidHom, e]
  exact hEO hE

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
