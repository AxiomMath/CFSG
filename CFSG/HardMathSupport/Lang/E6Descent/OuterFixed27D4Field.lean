module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4FieldFrob
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.D4Three

@[expose] def D4FieldType {K : Type} [Field K] (α : MulAut (adjointGroup Tag.D4 K)) : Prop :=
  ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K),
    α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)

theorem D4FieldType_of_normal_form {K : Type} [Field K] {α : MulAut (adjointGroup Tag.D4 K)}
    {g : adjointGroup Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε = 0)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) : D4FieldType α :=
  ⟨g, a, σ, hε ▸ hα⟩

section Square

variable {K : Type} [Field K]

theorem sq_conj_mul_exactNormalAut (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) :
    ∃ (g' : adjointGroup Tag.D4 K) (a' : Fin Tag.D4.rank → Kˣ),
      (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) ^ 2 =
        MulAut.conj g' * exactNormalAut Tag.D4 K a' (σ ^ 2) 0 := by
  refine ⟨g * exactNormalAut Tag.D4 K a σ 0 g,
    fun j => a j * Units.map σ.toRingHom.toMonoidHom (a ((exactPerm Tag.D4 0).symm j)), ?_⟩
  rw [pow_two, mul_assoc, ← mul_assoc (exactNormalAut Tag.D4 K a σ 0), mul_conj_eq, map_mul,
    mul_assoc, mul_assoc, exactNormalAut_mul, pow_two]

end Square

section Descent

variable {K : Type} [Field K]

theorem exists_conj_eq_entrywiseAdjointAut_D4 {ℓ f d : ℕ} [Fact ℓ.Prime] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (hd : 1 ≤ d) (hdf : d * 3 = f)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ ℓ ^ d) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (β : MulAut (adjointGroup Tag.D4 K))
    (hβ : β = MulAut.conj g * exactNormalAut Tag.D4 K a T 0) (hβ3 : β ^ 3 = 1) :
    ∃ ψ : MulAut (adjointGroup Tag.D4 K), ψ * β * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T := by
  classical
  set L := AlgebraicClosure K with hL
  set x : ModGL Tag.D4 L :=
    baseChangeGL (algebraMap K L) ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hβx : ∀ u : adjointGroup Tag.D4 K, baseChangeGL (algebraMap K L)
      ((β u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = x * baseChangeGL (algebraMap K L)
        ((entrywiseAdjointAut Tag.D4 T u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * x⁻¹ := by
    intro u
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_exactNormalAut, exactQ_D4, coe_entrywiseAdjointAut, hxdef]
    simp only [map_mul, map_inv, mul_one, inv_one]
    group
  exact exists_conj_eq_entrywiseAdjointAut_of_ambient Tag.D4 K hK hK4 hd (by norm_num) hdf T hT L
    x hx β hβx hβ3

end Descent

theorem twentySeven_dvd_fixedSubgroup_D4_field {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (hα : α ∉ inner (adjointGroup Tag.D4 K)) (hfield : D4FieldType α) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨g, a, σ, hαeq⟩ := hfield
  have hσ3 : σ ^ 3 = 1 := cube_normal_form_sigma_cube (hαeq ▸ hα3)
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hα (hαeq ▸ mem_inner_of_normal_form_one g a (hαeq ▸ hα3))
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ := exists_frobenius_of_cube hℓ hf K hK σ hσ3 hσ1
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f
  have hconj : ∀ (β : MulAut (adjointGroup Tag.D4 K)) (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' T 0 →
      β ^ 3 = 1 → 27 ∣ Nat.card (fixedSubgroup β) := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
    rw [← card_fixedSubgroup_conj ψ β, hψ]
    exact (twentySeven_dvd_card_adjointGroup_D4 (fixSubfield T)).trans
      (CFSG.HardMathSupport.Malle.E27Lie.card_adjointGroup_dvd_card_fixedSubgroup T)
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    rw [fixedSubgroup_pow_eq hα22]
    exact hconj (α ^ 2) g' a' hα2 hα23
