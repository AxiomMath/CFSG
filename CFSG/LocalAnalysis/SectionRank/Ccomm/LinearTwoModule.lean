module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

public section

namespace CFSG.SectionRank.Ccomm

open Matrix

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

@[expose] noncomputable def glEquivOfBasis (b : Module.Basis (Fin 2) k V) :
    LinearMap.GeneralLinearGroup k V ≃* GL (Fin 2) k :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv

theorem glEquivOfBasis_val (b : Module.Basis (Fin 2) k V) (g : LinearMap.GeneralLinearGroup k V) :
    ((glEquivOfBasis b g : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      LinearMap.toMatrix b b (g : V →ₗ[k] V) :=
  rfl

theorem perfect_linear_two_basics_module (hV : Module.finrank k V = 2)
    (J : Subgroup (LinearMap.GeneralLinearGroup k V)) [Group.IsPerfect J] (hJ : J ≠ ⊥) :
    (∀ g ∈ J, LinearMap.det (g : V →ₗ[k] V) = 1) ∧
      (∀ L : Submodule k V, Module.finrank k L = 1 →
        ∃ g ∈ J, ¬ L.map (g : V →ₗ[k] V) ≤ L) ∧
      (∀ g : J, g ∈ Subgroup.center J ↔
        ∃ c : k, ((g : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) = c • LinearMap.id) ∧
      Nat.card (Subgroup.center J) ≤ 2 := by
  have : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  set τ := glEquivOfBasis b with hτ
  set J' := J.map τ.toMonoidHom with hJ'
  have : Group.IsPerfect J' := Group.IsPerfect.map _
  have hJ'ne : J' ≠ ⊥ := by
    rw [hJ', Ne, Subgroup.map_eq_bot_iff_of_injective J (f := τ.toMonoidHom) τ.injective]
    exact hJ
  obtain ⟨hdet, heig, hcen, hcard⟩ := perfect_linear_two_basics J' hJ'ne
  let eJ : J ≃* J' := J.equivMapOfInjective τ.toMonoidHom τ.injective
  have heJ : ∀ g : J, ((eJ g : J') : GL (Fin 2) k) = τ g := fun _ => rfl
  have hcenJ : ∀ g : J, g ∈ Subgroup.center J ↔ eJ g ∈ Subgroup.center J' := by
    intro g
    constructor
    · intro hg
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro h
      obtain ⟨h, rfl⟩ := eJ.surjective h
      rw [← map_mul, ← map_mul, hg h]
    · intro hg
      rw [Subgroup.mem_center_iff] at hg ⊢
      intro h
      apply eJ.injective
      rw [map_mul, map_mul]
      exact hg (eJ h)
  refine ⟨fun g hg => ?_, fun L hL => ?_, fun g => ?_, ?_⟩
  · have h := hdet (τ g) (Subgroup.mem_map_of_mem _ hg)
    rw [hτ, glEquivOfBasis_val, LinearMap.det_toMatrix] at h
    exact h
  · obtain ⟨⟨v, hvL⟩, hv0, hspan⟩ := finrank_eq_one_iff'.1 hL
    have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
    obtain ⟨g', hg'J, hg'⟩ := heig (b.repr v) (by
      intro h
      apply hv0'
      have h0 : b.repr v = 0 := by
        ext i
        exact congrFun h i
      simpa using h0)
    obtain ⟨g, hgJ, rfl⟩ := Subgroup.mem_map.1 hg'J
    refine ⟨g, hgJ, fun hle => ?_⟩
    have hgv : (g : V →ₗ[k] V) v ∈ L := hle (Submodule.mem_map_of_mem hvL)
    obtain ⟨c, hc⟩ := hspan ⟨_, hgv⟩
    have hc' : c • v = (g : V →ₗ[k] V) v := congrArg Subtype.val hc
    apply hg' c
    rw [MulEquiv.coe_toMonoidHom, glEquivOfBasis_val, LinearMap.toMatrix_mulVec_repr, ← hc',
      map_smul, Finsupp.coe_smul]
  · rw [hcenJ, hcen, heJ, glEquivOfBasis_val]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, (LinearMap.toMatrix b b).injective ?_⟩
      rw [hc, map_smul, LinearMap.toMatrix_id]
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_smul, LinearMap.toMatrix_id]⟩
  · calc Nat.card (Subgroup.center J) = Nat.card (Subgroup.center J') :=
          Nat.card_congr (Subgroup.centerCongr eJ).toEquiv
      _ ≤ 2 := hcard

end CFSG.SectionRank.Ccomm
