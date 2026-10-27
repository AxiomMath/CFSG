module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

@[expose] def TransvectionModel {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W))
    (t : LinearMap.GeneralLinearGroup (ZMod 2) W) : Prop :=
  t ∈ H ∧ IsF2Transvection t ∧ t ∉ ⁅H, H⁆ ∧ (⁅H, H⁆).relIndex H = 2 ∧
    ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⁅H, H⁆ ∧ ⁅H, H⁆ ≠ ⊥ ∧
    ((Module.finrank (ZMod 2) W = 4 ∧ ∃ f : LinearMap.BilinForm (ZMod 2) W,
        f.Nondegenerate ∧ f.IsAlt ∧ H = bilinIsometryGroup f) ∨
      (∃ Q : QuadraticForm (ZMod 2) W, (QuadraticMap.polarBilin Q).Nondegenerate ∧
        H = orthGL Q) ∨
      (Even (Module.finrank (ZMod 2) W) ∧
        ((∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 1),
            H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (sumZeroRep (Module.finrank (ZMod 2) W + 1)).range) ∨
          ∃ β : W ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) W + 2) ⧸
              onesLine (Module.finrank (ZMod 2) W + 2),
            H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
              (heartRep (Module.finrank (ZMod 2) W + 2)).range)))

theorem transvectionModel_of_rep {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W] {M : Type*} [Group M]
    (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (L : Subgroup M) [L.Normal] (s : M)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ m : M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤)
    (htr : IsF2Transvection (ρ s))
    (hgen : ∀ T : Subgroup M, T.Normal → ρ.ker ≤ T → s ∈ T → T = ⊤)
    (hM : ⊤ ≤ L ⊔ Subgroup.zpowers s ⊔ ρ.ker)
    (hperf : L ≤ ⁅L, L⁆ ⊔ ρ.ker) (hL1 : ¬ L ≤ ρ.ker) (hs : ρ s ∉ L.map ρ) :
    L.map ρ = ⁅ρ.range, ρ.range⁆ ∧ TransvectionModel ρ.range (ρ s) := by
  have hperf' : ⁅L.map ρ, L.map ρ⁆ = L.map ρ := by
    apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun x hx y hy => by
        have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · calc L.map ρ ≤ (⁅L, L⁆ ⊔ ρ.ker).map ρ := Subgroup.map_mono hperf
        _ = ⁅L.map ρ, L.map ρ⁆ := by
          rw [Subgroup.map_sup, Subgroup.map_commutator,
            (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hne : L.map ρ ≠ ⊥ := fun h => hL1 (Subgroup.map_eq_bot_iff _ |>.mp h)
  have hidx := relIndex_map_eq_two ρ L s htr hM hs
  obtain ⟨hLeq, hshape⟩ := shape_of_perfect_index_two Module.finrank_pos ρ.range (L.map ρ)
    ⟨_, (by
      rintro _ ⟨g, -, rfl⟩
      exact isF2Transvection_conj htr g), range_eq_closure_conj ρ s hgen⟩
    (fun P hP => hirr P fun m w hw => hP (ρ m) ⟨m, rfl⟩ w hw)
    (Subgroup.map_le_range ρ L) hidx hperf' hne
  refine ⟨hLeq, ⟨s, rfl⟩, htr, ?_, ?_, ?_, ?_, hshape⟩
  · rw [← hLeq]; exact hs
  · rw [← hLeq]; exact hidx
  · rw [← hLeq]; exact hperf'
  · rw [← hLeq]; exact hne

theorem nonempty_mulEquiv_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : A →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nonempty (B ≃* C) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))⟩

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
