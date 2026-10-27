module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL5U5Lin
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSU

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.Transfer CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {X : Type} [Group X] {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
  [CharP K p]

theorem center_pow_five_su (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (k : Su K p f 5)
    (hk : k ∈ Subgroup.center (Su K p f 5)) : k ^ 5 = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_su hK hq (by norm_num) hk
  have hdet : c ^ 5 = 1 := by
    have h1 := det_suMat k
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal] at h1
    simpa using h1
  have hpow : ∀ m : ℕ, suMat (k ^ m) = suMat k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, suMat_mul, ih, pow_succ]
  apply suMat_injective
  rw [hpow, hc, ← map_pow, hdet, map_one, suMat_one]

theorem exists_commuting_longRoot_su5 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {z : Su K p f 5} (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ (L₁ L₂ : Subgroup (Su K p f 5)) (i₁ i₂ : Su K p f 5),
      IsLongRootSU2 K p f (by norm_num) L₁ i₁ ∧ IsLongRootSU2 K p f (by norm_num) L₂ i₂ ∧
      L₁ ≤ Subgroup.centralizer ({z} : Set (Su K p f 5)) ∧
      L₂ ≤ Subgroup.centralizer ({z} : Set (Su K p f 5)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨a, ha, g, hg⟩ := ModelFacts.exists_su_conj_negBlock hK h2 (by norm_num) hz
  rw [ModelFacts.negBlockK_zero_eq_diagonal] at hg
  set D : Matrix (Fin 5) (Fin 5) K :=
    Matrix.diagonal (fun j : Fin 5 => if j.val < a then (-1 : K) else 1) with hD
  have hdetD : D.det = 1 := by
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, det_suMat, det_suMat, one_mul, one_mul] at this
    exact this.symm
  let δ : SL(5, K) := ⟨D, hdetD⟩
  let ι := suToSL (unitaryInvolution K p f) 5
  have hzδ : ι z = ι g * δ * (ι g)⁻¹ := by
    have h1 : ι z * ι g = ι g * δ := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_suToSL,
        coe_suToSL]
      exact hg)
    rw [← h1]
    group
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hprod : ∏ j : Fin 5, (if j.val < a then (-1 : K) else 1) = 1 := by
    rw [← Matrix.det_diagonal]
    exact hdetD
  have ha24 : a = 2 ∨ a = 4 := by
    rw [Fin.prod_univ_five] at hprod
    interval_cases a
    · exfalso
      apply hz1
      have hδ : δ = 1 := Subtype.ext (by simp [δ, hD])
      apply suToSL_injective
      rw [hzδ, hδ, mul_one, mul_inv_cancel, map_one]
    · norm_num at hprod
      exact (hne hprod).elim
    · exact Or.inl rfl
    · norm_num at hprod
      exact (hne hprod).elim
    · exact Or.inr rfl
    · norm_num at hprod
      exact (hne hprod).elim
  have hcent : ∀ (j : ℕ) (hj : j + 2 ≤ 5), (j = 0 ∨ j = 2) →
      (blockEmb K p f 5 2 j hj).range.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set (Su K p f 5)) := by
    rintro j hj hj' _ ⟨_, ⟨A, rfl⟩, rfl⟩
    have hA : ι (blockEmb K p f 5 2 j hj A) * δ = δ * ι (blockEmb K p f 5 2 j hj A) :=
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_suToSL,
          suMat_blockEmb]
        exact (diagonal_mul_blockMat_comm_of_eq (sign_eq_of_block ha24 hj') _).symm)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    apply suToSL_injective
    simp only [map_mul, map_inv]
    rw [hzδ]
    calc ι g * ι (blockEmb K p f 5 2 j hj A) * (ι g)⁻¹ * (ι g * δ * (ι g)⁻¹)
        = ι g * (ι (blockEmb K p f 5 2 j hj A) * δ) * (ι g)⁻¹ := by group
      _ = ι g * (δ * ι (blockEmb K p f 5 2 j hj A)) * (ι g)⁻¹ := by rw [hA]
      _ = ι g * δ * (ι g)⁻¹ * (ι g * ι (blockEmb K p f 5 2 j hj A) * (ι g)⁻¹) := by group
  refine ⟨_, _, _, _, (isLongRootSU2_range_blockEmb hK hp (by norm_num : 0 + 2 ≤ 5)).conj g,
    (isLongRootSU2_range_blockEmb hK hp (by norm_num : 2 + 2 ≤ 5)).conj g,
    hcent 0 _ (Or.inl rfl), hcent 2 _ (Or.inr rfl), ?_⟩
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hAB := blockEmb_comm (K := K) (p := p) (f := f) (by norm_num : 0 + 2 ≤ 5)
    (by norm_num : 2 + 2 ≤ 5) (Or.inl le_rfl) A B
  calc g * blockEmb K p f 5 2 0 _ A * g⁻¹ * (g * blockEmb K p f 5 2 2 _ B * g⁻¹)
      = g * (blockEmb K p f 5 2 0 _ A * blockEmb K p f 5 2 2 _ B) * g⁻¹ := by group
    _ = g * (blockEmb K p f 5 2 2 _ B * blockEmb K p f 5 2 0 _ A) * g⁻¹ := by rw [hAB]
    _ = g * blockEmb K p f 5 2 2 _ B * g⁻¹ * (g * blockEmb K p f 5 2 0 _ A * g⁻¹) := by group

theorem exists_sl2_pair_of_psu5 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : X ≃* StatedProj (StatedSU 5 (p ^ f) K)) {t : X} (ht : orderOf t = 2) :
    ∃ H₁ H₂ : Subgroup X, H₁ ≤ Subgroup.centralizer ({t} : Set X) ∧
      H₂ ≤ Subgroup.centralizer ({t} : Set X) ∧ (∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) ∧
      Nonempty (H₁ ≃* SL(2, fixedSubfield K p f)) ∧
      Nonempty (H₂ ≃* SL(2, fixedSubfield K p f)) := by
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
  obtain ⟨z, hz, rfl⟩ := exists_sq_eq_one_lift_of_pow_five θ hker (center_pow_five_su hK hq)
    (MonoidHom.mem_range.mpr (hsurj t)) ht2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨L₁, L₂, i₁, i₂, hL₁, hL₂, hC₁, hC₂, hcomm⟩ := exists_commuting_longRoot_su5 hK hp hz hz1
  refine ⟨L₁.map θ, L₂.map θ, map_le_centralizer_of_le θ hC₁, map_le_centralizer_of_le θ hC₂,
    ?_, IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hker ⟨L₁, i₁, hL₁, rfl, rfl⟩,
    IsLongRootSU2Image.nonempty_mulEquiv hK hp hq (by norm_num) hker ⟨L₂, i₂, hL₂, rfl, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hcomm x hx y hy]

end CFSG.ClassicalInvolution.Q3.TA3
