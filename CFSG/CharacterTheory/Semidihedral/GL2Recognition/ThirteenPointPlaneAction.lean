module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ThirteenPointCoordinatization

public section

namespace CFSG.Semidihedral.GL2Recognition

open Matrix CFSG.Assembly.LowTwoRank

section Transport

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

@[expose] def transportedPerm (f : Ω ≃ ProjPoint) : G →* Equiv.Perm ProjPoint :=
  (Equiv.permCongrHom f).toMonoidHom.comp (MulAction.toPermHom G Ω)

theorem transportedPerm_apply (f : Ω ≃ ProjPoint) (g : G) (u : Ω) :
    transportedPerm f g (f u) = f (g • u) := by
  simp [transportedPerm, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem transportedPerm_mem {f : Ω ≃ ProjPoint} {B : Set (Set Ω)}
    (hf : (fun b => f '' b) '' B = projLineSets)
    (hBG : ∀ g : G, ∀ b ∈ B, (fun u => g • u) '' b ∈ B) (g : G) :
    transportedPerm f g ∈ projCollineationGroup := by
  have hmaps : ∀ g : G, Set.MapsTo (fun S => (transportedPerm f g : ProjPoint → ProjPoint) '' S)
      projLineSets projLineSets := by
    intro g S hS
    rw [← hf] at hS ⊢
    obtain ⟨b, hb, rfl⟩ := hS
    refine ⟨(fun u => g • u) '' b, hBG g b hb, ?_⟩
    simp only
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun u _ => (transportedPerm_apply f g u).symm
  refine Set.InvOn.bijOn ⟨fun S _ => ?_, fun S _ => ?_⟩ (hmaps g) (hmaps g⁻¹)
  · simp only [Set.image_image, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply, Set.image_id']
  · simp only [Set.image_image, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply, Set.image_id']

end Transport

@[expose] noncomputable def statedSLThreeEquivStatedProj :
    SpecialLinearGroup (Fin 3) (ZMod 3) ≃* StatedProj (StatedSL 3 (ZMod 3)) :=
  (specialLinearGroupEquivStatedSL 3 (ZMod 3)).trans
    ((QuotientGroup.quotientMulEquivOfEq (by
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
      exact statedSL_three_inf_statedScalars)).trans QuotientGroup.quotientBot).symm

theorem thirteen_point_plane_action_classical_model {G : Type} [Group G]
    (hG : Nat.card G = 5616) {Ω : Type*} [MulAction G Ω] (hΩ : Nat.card Ω = 13)
    (hfaith : ∀ g : G, (∀ u : Ω, g • u = u) → g = 1) (B : Set (Set Ω))
    (hBG : ∀ g : G, ∀ b ∈ B, (fun u => g • u) '' b ∈ B) (h4 : ∀ b ∈ B, b.ncard = 4)
    (hu : ∀ x y : Ω, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b) :
    ∃ (f : Ω ≃ ProjPoint) (ψ : G ≃* SpecialLinearGroup (Fin 3) (ZMod 3)),
      (∀ (g : G) (u : Ω), (f (g • u)).1 =
        (f u).1.map (Matrix.toLin' (ψ g : Matrix (Fin 3) (Fin 3) (ZMod 3)))) ∧
      (fun b => f '' b) '' B = projLineSets ∧ StatedClassicalModel G .PSL 3 3 1 := by
  obtain ⟨⟨f, hf⟩, -, -, -⟩ := thirteen_point_four_block_plane_coordinatization hΩ B h4 hu
  let α : G →* projCollineationGroup :=
    (transportedPerm f).codRestrict projCollineationGroup (transportedPerm_mem hf hBG)
  have hα : ∀ g u, (α g : Equiv.Perm ProjPoint) (f u) = f (g • u) := fun g u =>
    transportedPerm_apply f g u
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro g hg
    refine hfaith g fun u => f.injective ?_
    rw [← hα, hg]
    rfl
  have hαbij : Function.Bijective α := hαinj.bijective_of_nat_card_le (by
    rw [hG, three_element_projective_plane_full_collineation_group.2.1])
  let ψ : G ≃* SpecialLinearGroup (Fin 3) (ZMod 3) :=
    (MulEquiv.ofBijective α hαbij).trans projCollineationEquiv.symm
  have hψ : ∀ g, projCollineationHom (ψ g) = α g := fun g => by
    rw [← projCollineationEquiv_apply]
    simp [ψ]
  refine ⟨f, ψ, fun g u => ?_, hf, ?_⟩
  · rw [← projCollineationHom_apply, hψ g, hα]
  · refine ⟨⟨Nat.prime_three, le_rfl, by decide, by decide, by decide⟩, ZMod 3, inferInstance,
      inferInstance, by rw [Nat.card_zmod, pow_one], ⟨ψ.trans statedSLThreeEquivStatedProj⟩⟩

end CFSG.Semidihedral.GL2Recognition
