module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinear

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
  CFSG.Blueprint
open CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply_of_not_mem_left
  blockMat_apply_of_not_mem_right)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

namespace FL5

theorem layerExcludesQ8_of_blocks {X : Type} [Group X] [Finite X]
    (hF : TwoSubgroupsFourGenerated X) {G : Type} [Group G] (Ψ : G →* X)
    (hΨ : Function.Surjective Ψ) {t : X} {B₁ B₂ L₁ L₂ : Subgroup G}
    (hB₁ : CFSG.Open.IsComponentOf (B₁.map Ψ) (Ψ.range ⊓ Subgroup.centralizer ({t} : Set X)))
    (hB₂ : CFSG.Open.IsComponentOf (B₂.map Ψ) (Ψ.range ⊓ Subgroup.centralizer ({t} : Set X)))
    (h₁ : L₁ ≤ B₁) (h₂ : L₂ ≤ B₂) (hc : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hF₁ : Odd (Nat.card F₁))
    (hF₂ : Odd (Nat.card F₂)) (e₁ : L₁.map Ψ ≃* SL(2, F₁)) (e₂ : L₂.map Ψ ≃* SL(2, F₂)) :
    LayerExcludesQ8 X t := by
  rw [MonoidHom.range_eq_top.mpr hΨ, top_inf_eq] at hB₁ hB₂
  refine layerExcludesQ8_of_sl2Pair hF hB₁ hB₂ (Subgroup.map_mono h₁) (Subgroup.map_mono h₂) ?_
    hF₁ hF₂ e₁ e₂
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hc x hx y hy]

variable {K : Type} [Field K]

theorem eq_two_or_four (h2 : (2 : K) ≠ 0) {a : ℕ} (ha : a ≤ 5) (ha0 : a ≠ 0)
    (hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1) : a = 2 ∨ a = 4 := by
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  rw [Fin.prod_univ_five] at hprod
  interval_cases a
  · exact absurd rfl ha0
  · norm_num at hprod
    exact (hne hprod).elim
  · exact Or.inl rfl
  · norm_num at hprod
    exact (hne hprod).elim
  · exact Or.inr rfl
  · norm_num at hprod
    exact (hne hprod).elim

theorem two_le_card {m j : ℕ} (hj : j + 2 ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, j ≤ x.val → x.val < j + 2 → x ∈ J) : 2 ≤ J.card :=
  Finset.one_lt_card.mpr ⟨⟨j, by omega⟩, hJ _ le_rfl (by simp), ⟨j + 1, by omega⟩,
    hJ _ (by simp) (by simp), by simp [Fin.ext_iff]⟩

theorem blockMat_apply_of_not_mem {m j k : ℕ} {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, j ≤ x.val → x.val < j + k → x ∈ J) (A : Matrix (Fin k) (Fin k) K)
    (a b : Fin m) (hab : a ∉ J ∨ b ∉ J) : blockMat m j A a b = if a = b then 1 else 0 := by
  rcases hab with ha | hb
  · rw [blockMat_apply_of_not_mem_left A (fun h => ha (hJ a h.1 h.2)), Matrix.one_apply]
  · rw [blockMat_apply_of_not_mem_right A a (fun h => hb (hJ b h.1 h.2)), Matrix.one_apply]

theorem range_blockSL_le {m j : ℕ} (hj : j + 2 ≤ m) {J : Finset (Fin m)}
    (hJ : ∀ x : Fin m, j ≤ x.val → x.val < j + 2 → x ∈ J) :
    (blockSL K m 2 j hj).range ≤ coordBlockSL K J := by
  rintro _ ⟨A, rfl⟩
  rw [mem_coordBlockSL_iff]
  intro a b hab
  rw [coe_blockSL]
  exact blockMat_apply_of_not_mem hJ _ a b hab

theorem mem_coordSet_zero {a : ℕ} (ha : a = 2 ∨ a = 4) (x : Fin 5) (h0 : 0 ≤ x.val)
    (h1 : x.val < 0 + 2) : x ∈ coordSet (fun j : Fin 5 => decide (a ≤ j.val)) false := by
  rw [mem_coordSet]
  simp only [decide_eq_false_iff_not, not_le]
  omega

theorem mem_coordSet_two {a : ℕ} (ha : a = 2 ∨ a = 4) (x : Fin 5) (h0 : 2 ≤ x.val)
    (h1 : x.val < 2 + 2) :
    x ∈ coordSet (fun j : Fin 5 => decide (a ≤ j.val)) (decide (a ≤ 2)) := by
  rw [mem_coordSet]
  simp only [decide_eq_decide]
  constructor <;> intro <;> omega

end FL5

section Sl5

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]

theorem layerExcludesQ8_of_sl5 (hF : TwoSubgroupsFourGenerated X) (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) (θ : SL(5, K) →* X) (hsurj : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(5, K)) {z : SL(5, K)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    LayerExcludesQ8 X (θ z) := by
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
  have ha24 := FL5.eq_two_or_four h2 ha ha0 hprod
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
  have hJ₁ := FL5.mem_coordSet_zero ha24
  have hJ₂ := FL5.mem_coordSet_two ha24
  obtain ⟨e₁⟩ := IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hk
    ⟨_, _, isLongRootSL2_range_blockSL h2 (by norm_num : 0 + 2 ≤ 5), rfl, rfl⟩
  obtain ⟨e₂⟩ := IsLongRootImage.nonempty_mulEquiv hodd (by norm_num) hk
    ⟨_, _, isLongRootSL2_range_blockSL h2 (by norm_num : 2 + 2 ≤ 5), rfl, rfl⟩
  refine FL5.layerExcludesQ8_of_blocks hF _ hs
    (isComponentOf_block_centralizer h2 h4 _ hk _ σ hf false
      (FL5.two_le_card (by norm_num) hJ₁))
    (isComponentOf_block_centralizer h2 h4 _ hk _ σ hf (decide (a ≤ 2))
      (FL5.two_le_card (by norm_num) hJ₂))
    (FL5.range_blockSL_le _ hJ₁) (FL5.range_blockSL_le _ hJ₂) ?_ hodd hodd e₁ e₂
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact blockSL_comm (K := K) (by norm_num : 0 + 2 ≤ 5) (by norm_num : 2 + 2 ≤ 5)
    (Or.inl le_rfl) A B

end Sl5

variable {X : Type} [Group X] [Finite X]

theorem layerExcludesQ8_l5 (hF : TwoSubgroupsFourGenerated X) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hm : LieModel X .PSL 5 p f) (t : X) (ht : orderOf t = 2) :
    LayerExcludesQ8 X t := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psl hm
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  let θ : SL(5, K) →* X := e.symm.toMonoidHom.comp
    ((projectiveSpecialLinearGroupEquivStatedProj 5 K).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center SL(5, K))))
  have hsurj : Function.Surjective θ :=
    e.symm.surjective.comp ((projectiveSpecialLinearGroupEquivStatedProj 5 K).surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hker : θ.ker ≤ Subgroup.center SL(5, K) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simpa [θ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] using hx
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker center_pow_five
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  exact layerExcludesQ8_of_sl5 hF hodd (by rw [hK]; omega) θ hsurj hker hz hz1

end CFSG.ClassicalInvolution.Q3.TA3.Frame
