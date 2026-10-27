module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGU

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB

theorem Ivk93Cfg.exists_unitary {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {q : ℕ}
    {L L' : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))}
    (h : Ivk93Cfg x q L L') :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M₁ M₂ : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  have hrange : φ.range = projSpecial hud (hypForm hud r ε) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hypModelEquiv hud (θ y)).2
    · intro hz
      obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
      refine ⟨θ.symm w, ?_⟩
      rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
      rfl
  have : φ.range.Normal := by
    rw [hrange]
    infer_instance
  have hK₁ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  have hK₂ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁ hK₂
  refine ⟨hud, A, ?_, _, _, hK₁.2, hK₂.2, fun k => h.ne ?_⟩
  · change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
    rw [hA, orderOf_injective φ hφ x, h.ord]
  · have h1 := subgroupOf_inj.mp k
    rw [inf_of_le_left hK₁.1, inf_of_le_left hK₂.1] at h1
    exact map_injective hφ h1

theorem ivk93_u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93Empty (fun X _ => LieModel X .PSU 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have : Finite (StatedProj (StatedSU (2 * 1 + 1) (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  obtain ⟨hud, A, hA, M₁, M₂, h₁, h₂, hne⟩ :=
    (h.of_equiv (J' := StatedProj (StatedSU (2 * 1 + 1) (p ^ f) K)) φ).exists_unitary hp hf hK
      le_rfl le_rfl
  have : Finite K := hud.finite
  have hdim : finrank K (HypIndex 1 1 → K) = 3 := UnitaryHigher.finrank_hypIndex_fun
  rcases unitary_dim_of_two_pComponents hud hp2 (by omega) (hypForm_isSymm hud)
    (hypForm_separatingLeft hud) hA h₁ h₂ hne with h | ⟨k, hk⟩ <;> omega

end CFSG.GH74.GLS.IVK.Proofs2
