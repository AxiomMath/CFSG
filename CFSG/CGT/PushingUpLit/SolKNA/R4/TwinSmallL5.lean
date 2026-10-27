module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallFive
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain
public import CFSG.ClassicalInvolution.Q3.TA3FrameL5

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
  CFSG.Blueprint CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply_of_not_mem_left
  blockMat_apply_of_not_mem_right)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped MatrixGroups

section Sl5

variable {X : Type} [Group X] {K : Type} [Field K] [Finite K]

theorem twoBlock_of_sl5 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) (θ : SL(5, K) →* X)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(5, K))
    {z : SL(5, K)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ B₁ B₂ I₁ I₂ : Subgroup X, CFSG.Open.IsComponentOf B₁ (Subgroup.centralizer ({θ z} : Set X)) ∧
      CFSG.Open.IsComponentOf B₂ (Subgroup.centralizer ({θ z} : Set X)) ∧ I₁ ≤ B₁ ∧ I₂ ≤ B₂ ∧
      (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) ∧ Nonempty (↥I₁ ≃* SL(2, K)) ∧
      Nonempty (↥I₂ ≃* SL(2, K)) := by
  have h2 := two_ne_zero_of_odd_natCard hodd
  have hI : (z : Matrix (Fin 5) (Fin 5) K) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, ha, P, hP⟩ := ModelFacts.exists_sl_conj_diagonal h2 (by norm_num) hI
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz1
    have h1 : z * P = 1 * P := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, hP, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      simp)
    exact mul_right_cancel h1
  have hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1 := by
    have := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, z.2, P.2, one_mul, one_mul, Matrix.det_diagonal] at this
    exact this.symm
  have ha24 := Frame.FL5.eq_two_or_four h2 ha ha0 hprod
  set σ : Fin 5 → Bool := fun j => decide (a ≤ j.val) with hσ
  have hx : (z : Matrix (Fin 5) (Fin 5) K) * (P : Matrix (Fin 5) (Fin 5) K) =
      (P : Matrix (Fin 5) (Fin 5) K) * Matrix.diagonal fun j => 1 * signOf K (σ j) := by
    rw [hP]
    congr 2
    funext j
    simp only [one_mul, signOf, hσ, decide_eq_true_eq]
    split_ifs <;> first | rfl | omega
  have hf : ∀ y, θ z * (θ.comp (MulAut.conj P).toMonoidHom) y * (θ z)⁻¹ =
      (θ.comp (MulAut.conj P).toMonoidHom) (slConjugation 5 K (signGL K σ) y) := by
    intro y
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul, chart_of_lift one_ne_zero hx y]
  have hk := ker_comp_conj_le_center θ hker P
  have hs : Function.Surjective (θ.comp (MulAut.conj P).toMonoidHom) :=
    hsurj.comp (MulAut.conj P).surjective
  have hJ₁ := Frame.FL5.mem_coordSet_zero ha24
  have hJ₂ := Frame.FL5.mem_coordSet_two ha24
  obtain ⟨e₁⟩ := IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hk
    ⟨_, _, isLongRootSL2_range_blockSL h2 (by norm_num : 0 + 2 ≤ 5), rfl, rfl⟩
  obtain ⟨e₂⟩ := IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hk
    ⟨_, _, isLongRootSL2_range_blockSL h2 (by norm_num : 2 + 2 ≤ 5), rfl, rfl⟩
  have hB₁ := isComponentOf_block_centralizer h2 h4 _ hk _ σ hf false
    (Frame.FL5.two_le_card (by norm_num) hJ₁)
  have hB₂ := isComponentOf_block_centralizer h2 h4 _ hk _ σ hf (decide (a ≤ 2))
    (Frame.FL5.two_le_card (by norm_num) hJ₂)
  rw [MonoidHom.range_eq_top.mpr hs, top_inf_eq] at hB₁ hB₂
  refine ⟨_, _, _, _, hB₁, hB₂, Subgroup.map_mono (Frame.FL5.range_blockSL_le _ hJ₁),
    Subgroup.map_mono (Frame.FL5.range_blockSL_le _ hJ₂), ?_, ⟨e₁⟩, ⟨e₂⟩⟩
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact blockSL_comm (K := K) (by norm_num : 0 + 2 ≤ 5) (by norm_num : 2 + 2 ≤ 5)
    (Or.inl le_rfl) A B

end Sl5

theorem twoBlockShape_l5 {F : Type} [Group F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hm : LieModel F .PSL 5 p f) : TwoBlockShape F := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card K := by rw [hK]; omega
  let θ : SL(5, K) →* F := e.symm.toMonoidHom.comp
    ((projectiveSpecialLinearGroupEquivStatedProj 5 K).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center SL(5, K))))
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((projectiveSpecialLinearGroupEquivStatedProj 5 K).surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hker : θ.ker ≤ Subgroup.center SL(5, K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
  intro t ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker center_pow_five
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨B₁, B₂, I₁, I₂, hB₁, hB₂, hI₁, hI₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    twoBlock_of_sl5 hodd h4 θ hsurj hker hz hz1
  exact ⟨K, K, inferInstance, inferInstance, inferInstance, inferInstance, B₁, B₂, I₁, I₂, hodd,
    hodd, h4, h4, hB₁, hB₂, hI₁, hI₂, hc, ⟨e₁⟩, ⟨e₂⟩⟩


theorem false_of_l5Ne3 {r n : ℕ} (hr : 4 ≤ r) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : PerpHypR r n Y R S t)
    (hsmall : TwoSubgroupsFourGenerated ↥(genFittingFStar Y))
    (hF : SmallL5Ne3 ↥(genFittingFStar Y)) : False := by
  haveI := h.core.simple
  obtain ⟨p, f, hp, hp2, hf, h4, h3, hm⟩ := hF
  obtain ⟨-, h5⟩ := Q5L5U5.five_le hp hp2 hf h3
  exact not_twinPair_of_twoBlockShape (twoBlockShape_l5 hp hp2 h5 hm) hsmall
    (exists_twinPair_of_perp hr h (socleComm2_of_outTwoCyclic (outTwoCyclic_PSL5 hp hf h4 hm)))

theorem twinLeafR_l5Ne3 {r n : ℕ} (hr : 4 ≤ r) : TwinLeafR r n SmallL5Ne3 :=
  fun _ _ _ _ _ _ hP hsmall hF => false_of_l5Ne3 hr hP hsmall hF

theorem twinLeafR_l5 {r n : ℕ} (hr : 4 ≤ r)
    (h₃ : TwinLeafR r n fun F _ => LieModel F .PSL 5 3 1) : TwinLeafR r n SmallL5 := by
  refine TwinLeafR.of_split (fun F _ hF => ?_) h₃ (twinLeafR_l5Ne3 hr)
  obtain ⟨p, f, hp, hp2, hf, h4, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h4, h3, hm⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
