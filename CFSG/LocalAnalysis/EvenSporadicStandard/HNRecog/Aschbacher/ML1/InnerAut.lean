module

public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open Subgroup CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

theorem exists_conj_of_forall_mul_inv_mem_center {Q : Type} [Group Q] [Finite Q]
    (hE : IsExtraspecialPGroup 2 Q) (γ : Q ≃* Q)
    (hγ : ∀ x : Q, γ x * x⁻¹ ∈ Subgroup.center Q) : ∃ q : Q, ∀ x : Q, γ x = q * x * q⁻¹ := by
  classical
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  have hmul : ∀ x y : Q, ind (γ (x * y) * (x * y)⁻¹) =
      ind (γ x * x⁻¹) + ind (γ y * y⁻¹) := by
    intro x y
    rw [← ind_mul hE (hγ x) (hγ y)]
    congr 1
    have hc := mem_center_iff.mp (hγ y)
    calc γ (x * y) * (x * y)⁻¹
        = γ x * (γ y * y⁻¹) * x⁻¹ := by rw [map_mul]; group
      _ = γ x * ((γ y * y⁻¹) * x⁻¹) := by rw [mul_assoc]
      _ = γ x * (x⁻¹ * (γ y * y⁻¹)) := by rw [hc x⁻¹]
      _ = γ x * x⁻¹ * (γ y * y⁻¹) := by rw [← mul_assoc]
  let μ : Q →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (ind (γ x * x⁻¹))
      map_one' := by
        rw [map_one, inv_one, mul_one, ind_one]
        rfl
      map_mul' := fun x y => by
        rw [hmul x y, ofAdd_add] }
  let ℓV : Additive (Abelianization Q) →ₗ[ZMod 2] ZMod 2 :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (Abelianization.lift μ))
  have hℓV : ∀ x : Q, ℓV (Additive.ofMul (Abelianization.of x)) = ind (γ x * x⁻¹) := fun x => by
    change Multiplicative.toAdd (Abelianization.lift μ (Abelianization.of x)) = ind (γ x * x⁻¹)
    rw [Abelianization.lift_apply_of]
    rfl
  have hfin : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual (extraspecialQuadForm hE).polarBilin
    (extraspecialQuadForm_nondegenerate hE)).surjective ℓV
  obtain ⟨q₀, rfl⟩ := exists_ofMul_of u
  refine ⟨q₀, fun x => ?_⟩
  have key : γ x * x⁻¹ = ⁅q₀, x⁆ := by
    have h := LinearMap.congr_fun hu (Additive.ofMul (Abelianization.of x))
    rw [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
      polar_extraspecialQuadForm_apply, hℓV] at h
    have h' : ind ⁅q₀, x⁆ = ind (γ x * x⁻¹) := h
    by_contra hne
    have hc1 : ⁅q₀, x⁆ ∈ center Q := commutatorElement_mem_center hE q₀ x
    by_cases ha : γ x * x⁻¹ = 1
    · rw [ha, ind_one, ind_eq_zero_iff] at h'
      exact hne (ha.trans h'.symm)
    · by_cases hb : ⁅q₀, x⁆ = 1
      · rw [hb, ind_one, eq_comm, ind_eq_zero_iff] at h'
        exact ha h'
      · exact hne (eq_of_mem_center hE (hγ x) hc1 ha hb)
  calc γ x = (γ x * x⁻¹) * x := by group
    _ = ⁅q₀, x⁆ * x := by rw [key]
    _ = q₀ * x * q₀⁻¹ := by rw [commutatorElement_def]; group

end CFSG.EvenSporadicStandard.HNRecog.ML1
