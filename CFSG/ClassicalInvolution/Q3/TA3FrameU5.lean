module

public import CFSG.ClassicalInvolution.Q3.TA3FrameL5
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear (coordSet ker_comp_conj_le_center)
open scoped MatrixGroups

section Su5

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K] {p f : ℕ}
  [Fact p.Prime] [CharP K p]

theorem FU5.range_blockEmb_le {m j : ℕ} (hj : j + 2 ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, j ≤ x.val → x.val < j + 2 → x ∈ J) :
    (blockEmb K p f m 2 j hj).range ≤ coordBlockSU K p f J := by
  rintro _ ⟨A, rfl⟩
  rw [mem_coordBlockSU_iff]
  intro a b hab
  rw [coe_coe_blockEmb]
  exact FL5.blockMat_apply_of_not_mem hJ _ a b hab

theorem layerExcludesQ8_of_su5 (hF : TwoSubgroupsFourGenerated X)
    (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (θ : Su K p f 5 →* X)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f 5))
    {z : Su K p f 5} (hz : z * z = 1) (hz1 : z ≠ 1) : LayerExcludesQ8 X (θ z) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨a, ha, g, hg⟩ := ModelFacts.exists_su_conj_negBlock hK h2 (by norm_num) hz
  rw [ModelFacts.negBlockK_zero_eq_diagonal] at hg
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz1
    have h1 : z * g = 1 * g := suMat_injective (by
      rw [suMat_mul, hg, suMat_mul, suMat_one, Matrix.one_mul]
      simp)
    exact mul_right_cancel h1
  have hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1 := by
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, det_suMat, det_suMat, one_mul, one_mul,
      Matrix.det_diagonal] at this
    exact this.symm
  have ha24 := FL5.eq_two_or_four h2 ha ha0 hprod
  set σ : Fin 5 → Bool := fun j => decide (a ≤ j.val) with hσ
  have hD : (((g⁻¹ * z * g : Su K p f 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal fun i => signOf K (σ i) := by
    change suMat (g⁻¹ * z * g) = _
    rw [suMat_mul, suMat_mul, Matrix.mul_assoc, hg, ← Matrix.mul_assoc, ← suMat_mul,
      inv_mul_cancel, suMat_one, Matrix.one_mul]
    congr 1
    funext j
    simp only [signOf, hσ, decide_eq_true_eq]
    split_ifs <;> first | rfl | omega
  have hf : ∀ y, θ z * (θ.comp (MulAut.conj g).toMonoidHom) y * (θ z)⁻¹ =
      (θ.comp (MulAut.conj g).toMonoidHom) (g⁻¹ * z * g * y * (g⁻¹ * z * g)⁻¹) := by
    intro y
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hk := ker_comp_conj_le_center θ hker g
  have hs : Function.Surjective (θ.comp (MulAut.conj g).toMonoidHom) :=
    hsurj.comp (MulAut.conj g).surjective
  have hJ₁ := FL5.mem_coordSet_zero ha24
  have hJ₂ := FL5.mem_coordSet_two ha24
  obtain ⟨e₁⟩ := IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hk
    ⟨_, _, isLongRootSU2_range_blockEmb hK hp (by norm_num : 0 + 2 ≤ 5), rfl, rfl⟩
  obtain ⟨e₂⟩ := IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hk
    ⟨_, _, isLongRootSU2_range_blockEmb hK hp (by norm_num : 2 + 2 ≤ 5), rfl, rfl⟩
  have hodd : Odd (Nat.card (fixedSubfield K p f)) := by
    rw [card_fixedSubfield hK]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  refine FL5.layerExcludesQ8_of_blocks hF _ hs
    (isComponentOf_block_centralizer_su hK hq h2 _ hk _ σ _ hD hf false
      (FL5.two_le_card (by norm_num) hJ₁))
    (isComponentOf_block_centralizer_su hK hq h2 _ hk _ σ _ hD hf (decide (a ≤ 2))
      (FL5.two_le_card (by norm_num) hJ₂))
    (FU5.range_blockEmb_le _ hJ₁) (FU5.range_blockEmb_le _ hJ₂) ?_ hodd hodd e₁ e₂
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact blockEmb_comm (K := K) (p := p) (f := f) (by norm_num : 0 + 2 ≤ 5)
    (by norm_num : 2 + 2 ≤ 5) (Or.inl le_rfl) A B

end Su5

variable {X : Type} [Group X] [Finite X]

theorem layerExcludesQ8_u5 (hF : TwoSubgroupsFourGenerated X) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hm : LieModel X .PSU 5 p f) (t : X) (ht : orderOf t = 2) :
    LayerExcludesQ8 X t := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := ClassicalGroups.Unitary.charP_of_card_sq hK
  let θ : Su K p f 5 →* X := e.symm.toMonoidHom.comp
    ((QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K))).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)).toMonoidHom)
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5)).surjective)
  have hker : θ.ker ≤ Subgroup.center (Su K p f 5) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : MulEquiv.subgroupCongr (SUid_eq_statedSU hK 5) x ∈
        (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K) := by
      simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx' (g : GL (Fin 5) K))
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker (center_pow_five_su hK h5)
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  exact layerExcludesQ8_of_su5 hF hK hp2 h5 θ hsurj hker hz hz1

end CFSG.ClassicalInvolution.Q3.TA3.Frame
