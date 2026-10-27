module

public import CFSG.LieType.Chevalley.C2E6MinusSixBase
public import CFSG.LieType.Chevalley.C2E6MinusSixWitt

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem map_symm_map (φ : QuadraticMap.IsometryEquiv Q Q) (V : Submodule (ZMod 2) X) :
    (V.map (φ.toLinearEquiv : X →ₗ[ZMod 2] X)).map (φ.symm.toLinearEquiv : X →ₗ[ZMod 2] X) = V := by
  have h := mapVertex_mapVertex (g := φ) (h := φ.symm) φ.symm_apply_apply
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have : (φ.symm.toLinearEquiv : X →ₗ[ZMod 2] X) ((φ.toLinearEquiv : X →ₗ[ZMod 2] X) u) = u :=
      φ.symm_apply_apply u
    rw [this]
    exact hu
  · intro hv
    exact ⟨φ v, ⟨v, hv, rfl⟩, φ.symm_apply_apply v⟩

theorem mem_vertexStabilizer_conj_iff (φ : QuadraticMap.IsometryEquiv Q Q)
    {S S' : Set (Submodule (ZMod 2) X)}
    (hS : ∀ U, U ∈ S' ↔ ∃ V ∈ S, U = V.map (φ.toLinearEquiv : X →ₗ[ZMod 2] X))
    (σ : Equiv.Perm QVertex) :
    σ ∈ vertexStabilizer S' ↔
      (inducedPerm φ)⁻¹ * σ * inducedPerm φ ∈ vertexStabilizer S := by
  set c := inducedPerm φ
  have hc := inducedPerm_mem_typeAut φ
  constructor
  · rintro ⟨hσ, hfix⟩
    refine ⟨typeAut.mul_mem (typeAut.mul_mem (typeAut.inv_mem hc) hσ) hc, fun y hy => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact hfix (c y) ((hS _).mpr ⟨y.1, hy, rfl⟩)
  · rintro ⟨hτ, hfix⟩
    have hσ : σ ∈ typeAut := by
      have := typeAut.mul_mem (typeAut.mul_mem hc hτ) (typeAut.inv_mem hc)
      have e : c * (c⁻¹ * σ * c) * c⁻¹ = σ := by group
      rwa [e] at this
    refine ⟨hσ, fun x hx => ?_⟩
    obtain ⟨V, hV, hxV⟩ := (hS x.1).mp hx
    have hy : (c⁻¹ x).1 ∈ S := by
      change (x.1.map (φ.symm.toLinearEquiv : X →ₗ[ZMod 2] X)) ∈ S
      rw [hxV, map_symm_map]
      exact hV
    have := hfix (c⁻¹ x) hy
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_apply_inv,
      Equiv.Perm.inv_eq_iff_eq, perm_apply_inv] at this
    exact this

theorem minus_six_opposite_flag_stabilizer :
    Nat.card (vertexStabilizer {(ZMod 2) ∙ e₁, Submodule.span (ZMod 2) {e₁, e₂},
      (ZMod 2) ∙ f₁, Submodule.span (ZMod 2) {f₁, f₂}}) = 6 ∧
    (∀ σ : Equiv.Perm QVertex, σ ∈ vertexStabilizer {(ZMod 2) ∙ e₁,
        Submodule.span (ZMod 2) {e₁, e₂}, (ZMod 2) ∙ f₁, Submodule.span (ZMod 2) {f₁, f₂}} ↔
      ∃ A : GL (Fin 2) (ZMod 2), σ = inducedPerm (tailIso A)) ∧
    (∀ (A : GL (Fin 2) (ZMod 2)) (x : X), tailIso A x =
      ![x 0, x 1, x 2, x 3, (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 * x 4 +
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1 * x 5,
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 * x 4 +
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1 * x 5]) ∧
    Nat.card (GL (Fin 2) (ZMod 2)) = 6 ∧
    Function.Injective (fun A : GL (Fin 2) (ZMod 2) => inducedPerm (tailIso A)) ∧
    (∀ σ ∈ vertexStabilizer {(ZMod 2) ∙ e₁, Submodule.span (ZMod 2) {e₁, e₂},
        (ZMod 2) ∙ f₁, Submodule.span (ZMod 2) {f₁, f₂}},
      ∃ g : QuadraticMap.IsometryEquiv Q Q, σ = inducedPerm g) ∧
    ∀ p L p' L' : Submodule (ZMod 2) X, IsTotallySingular L → IsTotallySingular L' →
      finrank (ZMod 2) p = 1 → finrank (ZMod 2) L = 2 → p ≤ L →
      finrank (ZMod 2) p' = 1 → finrank (ZMod 2) L' = 2 → p' ≤ L' → L ⊓ L' = ⊥ →
      (∀ x ∈ p, ∀ y ∈ p', x ≠ 0 → y ≠ 0 → QuadraticMap.polar Q x y ≠ 0) →
      Nat.card (vertexStabilizer {p, L, p', L'}) = 6 ∧
        ∀ σ ∈ vertexStabilizer {p, L, p', L'},
          ∃ g : QuadraticMap.IsometryEquiv Q Q, σ = inducedPerm g := by
  refine ⟨card_baseStabilizer, fun σ => mem_baseStabilizer_iff, fun A x => rfl,
    card_GL_two_zmod_two, inducedPerm_tailIso_injective, fun σ hσ => ?_, ?_⟩
  · obtain ⟨A, rfl⟩ := exists_tail_of_mem hσ
    exact ⟨tailIso A, rfl⟩
  intro p L p' L' hL hL' hp hL2 hpL hp' hL2' hpL' hLL hB
  obtain ⟨φ, h1, h2, h3, h4⟩ := exists_isometry_of_opposite hL hL' hp hL2 hpL hp' hL2' hpL' hLL hB
  have hS : ∀ U, U ∈ ({p, L, p', L'} : Set (Submodule (ZMod 2) X)) ↔
      ∃ V ∈ baseFlagSpaces, U = V.map (φ.toLinearEquiv : X →ₗ[ZMod 2] X) := by
    intro U
    simp only [baseFlagSpaces, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      exists_eq_left, h1, h2, h3, h4]
  have key := mem_vertexStabilizer_conj_iff φ hS
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hinv : ∀ τ : Equiv.Perm QVertex,
        (inducedPerm φ)⁻¹ * (inducedPerm φ * τ * (inducedPerm φ)⁻¹) * inducedPerm φ = τ := by
      intro τ
      group
    have hinv' : ∀ σ : Equiv.Perm QVertex,
        inducedPerm φ * ((inducedPerm φ)⁻¹ * σ * inducedPerm φ) * (inducedPerm φ)⁻¹ = σ := by
      intro σ
      group
    refine (Nat.card_congr (Equiv.mk
      (fun σ => ⟨(inducedPerm φ)⁻¹ * σ.1 * inducedPerm φ, (key σ.1).mp σ.2⟩ :
        vertexStabilizer {p, L, p', L'} → vertexStabilizer baseFlagSpaces)
      (fun τ => ⟨inducedPerm φ * τ.1 * (inducedPerm φ)⁻¹, (key _).mpr ((hinv τ.1).symm ▸ τ.2)⟩)
      (fun σ => Subtype.ext (hinv' σ.1)) (fun τ => Subtype.ext (hinv τ.1)))).trans
      card_baseStabilizer
  · obtain ⟨A, hA⟩ := exists_tail_of_mem ((key σ).mp hσ)
    refine ⟨φ.symm.trans ((tailIso A).trans φ), ?_⟩
    rw [inducedPerm_trans, inducedPerm_trans, inducedPerm_symm, ← hA]
    group

end CFSG.LieType.Chevalley.C2E6Overlap
