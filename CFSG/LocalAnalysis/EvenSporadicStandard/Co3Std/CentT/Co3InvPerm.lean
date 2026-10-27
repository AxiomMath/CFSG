module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.Co3Second
public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import CFSG.Sporadic.SmallOddCore.J2Local

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Certified


theorem co3P_inf_centralizer_cases {τ : Equiv.Perm (Fin 276)} (hτP : τ ∈ co3P)
    (hτ : orderOf τ = 2) :
    Nonempty (↥(co3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 276)))) ≃* ↥co3M) ∨
      Nonempty (↥(co3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 276)))) ≃* ↥co3M1) := by
  obtain ⟨-, -, -, hcl, -, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_co3_complete_inner_involution_classes
  have hrep : ∃ g ∈ co3P, ∃ r : Equiv.Perm (Fin 276), τ = g * r * g⁻¹ ∧
      ((co3P ⊓ centralizer ({r} : Set _) = co3M) ∨
        (co3P ⊓ centralizer ({r} : Set _) = co3M1)) := by
    by_cases h : ∃ g ∈ co3P, τ = g * co3Z * g⁻¹
    · obtain ⟨g, hg, rfl⟩ := h
      exact ⟨g, hg, co3Z, rfl, Or.inl co3M_eq_centralizer.symm⟩
    · have h' : ∃ g ∈ co3P, τ = g * co3Tt * g⁻¹ := by
        by_contra h''
        exact h ((hcl τ hτP hτ).2 h'')
      obtain ⟨g, hg, rfl⟩ := h'
      exact ⟨g, hg, co3Tt, rfl, Or.inr co3M1_eq_centralizer.symm⟩
  obtain ⟨g, hg, r, hτeq, hr⟩ := hrep
  have himg : (MulAut.conj g).toMonoidHom '' ({r} : Set (Equiv.Perm (Fin 276))) = {τ} := by
    rw [Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτeq]
  have hmap : (co3P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 276)))).map
      (MulAut.conj g).toMonoidHom = co3P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 276))) := by
    rw [CFSG.Sporadic.SmallOddCore.map_conj_inf_centralizer co3P hg
      ({r} : Set (Equiv.Perm (Fin 276))), himg]
  have e1 : ↥(co3P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 276)))) ≃*
      ↥((co3P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 276)))).map
        (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective (co3P ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 276))))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rcases hr with hM | hM1
  · exact Or.inl ⟨((MulEquiv.subgroupCongr hmap).symm.trans e1.symm).trans
      (MulEquiv.subgroupCongr hM)⟩
  · exact Or.inr ⟨((MulEquiv.subgroupCongr hmap).symm.trans e1.symm).trans
      (MulEquiv.subgroupCongr hM1)⟩

theorem co3M1_structure :
    ∃ N : Subgroup ↥co3M1, N.Normal ∧ Nonempty (↥N ≃* ↥NativeSporadic.M12) ∧
      Nat.card ↥co3M1 = 2 * 95040 := by
  refine ⟨co3L1, co3L1_normal, ?_, ?_⟩
  · exact ⟨(Subgroup.subgroupOfEquivOfLe (H := co3L) co3L_le_M1).trans co3LEquivM12⟩
  · have h := co3L1.card_mul_index
    rw [card_co3L1, co3L1_index] at h
    omega

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
