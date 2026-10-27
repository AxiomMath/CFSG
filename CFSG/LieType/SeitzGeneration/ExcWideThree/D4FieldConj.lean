module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldKernel
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Conj


theorem fixedSubgroup_eq_fixedSubgroup_sq {G : Type*} [Group G] {β : MulAut G} (h3 : β ^ 3 = 1) :
    fixedSubgroup β = fixedSubgroup (β ^ 2) := by
  ext x
  rw [mem_fixedSubgroup, mem_fixedSubgroup]
  constructor
  · intro hx
    rw [pow_two, MulAut.mul_apply, hx, hx]
  · intro hx
    have h1 : (β ^ 3) x = x := by rw [h3]; rfl
    rw [pow_succ' β 2, MulAut.mul_apply, hx] at h1
    exact h1

theorem exists_conj_matrixInner_D4_field {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα : α = MulAut.conj g * exactNormalAut Tag.D4 K a T 0)
    (hα3 : α ^ 3 = 1) :
    ∃ ψ ∈ matrixInner Tag.D4 K L, ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T := by
  classical
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set x : ModGL Tag.D4 L :=
    baseChangeGL (algebraMap K L) ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hα' : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K 0) := by
    rw [d4Graph_zero, mul_one]
    exact hα
  have hβ : ∀ u : adjointGroup Tag.D4 K,
      baseChangeGL (algebraMap K L) (α u : ModGL Tag.D4 K) =
        x * baseChangeGL (algebraMap K L)
          (Subtype.val (twistedEntrywiseAut TwistTag.D4 ((0 : ℕ) : ℤ) T u) : ModGL Tag.D4 K) *
            x⁻¹ := by
    intro u
    rw [hα', hxdef]
    exact baseChange_normalForm L (algebraMap K L) g a T 0 u
  obtain ⟨ψ, h, -, hψ, hψα⟩ := exists_conj_eq_twistedEntrywiseAut_of_ambient TwistTag.D4 K hK hK4
    he hef T hT ((0 : ℕ) : ℤ) L x hx α hβ hα3
  have h0 : twistedEntrywiseAut TwistTag.D4 ((0 : ℕ) : ℤ) T = entrywiseAdjointAut Tag.D4 T := by
    unfold twistedEntrywiseAut
    rw [Nat.cast_zero, zpow_zero, one_mul]
    rfl
  exact ⟨ψ, ⟨h.1, hψ⟩, hψα.trans h0⟩

theorem exists_conj_fixedSubgroup_D4_field {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K]
    [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e)
    (hef : e * 3 = f) (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1)
    (hσ : σ = T ∨ σ = T ^ 2) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (α : MulAut (adjointGroup Tag.D4 K))
    (hα : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) (hα3 : α ^ 3 = 1) :
    ∃ ψ ∈ matrixInner Tag.D4 K L, fixedSubgroup (ψ * α * ψ⁻¹) = subfieldGroup Tag.D4 T := by
  classical
  rcases hσ with rfl | hσ
  · obtain ⟨ψ, hψ, hψα⟩ := exists_conj_matrixInner_D4_field hK hK4 he hef σ hT L g a α hα hα3
    exact ⟨ψ, hψ, by rw [hψα]⟩
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hα] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    obtain ⟨ψ, hψ, hψα⟩ := exists_conj_matrixInner_D4_field hK hK4 he hef T hT L g' a' (α ^ 2)
      hα2 hα23
    refine ⟨ψ, hψ, ?_⟩
    have hconj3 : (ψ * α * ψ⁻¹) ^ 3 = 1 := by
      have : (ψ * α * ψ⁻¹) ^ 3 = ψ * α ^ 3 * ψ⁻¹ := by
        rw [pow_three, pow_three]
        group
      rw [this, hα3]
      group
    have hconj2 : (ψ * α * ψ⁻¹) ^ 2 = entrywiseAdjointAut Tag.D4 T := by
      rw [← hψα]
      rw [pow_two, pow_two]
      group
    rw [fixedSubgroup_eq_fixedSubgroup_sq hconj3, hconj2]

end Conj

end CFSG.LieType.SeitzGeneration.ExcWideThree
