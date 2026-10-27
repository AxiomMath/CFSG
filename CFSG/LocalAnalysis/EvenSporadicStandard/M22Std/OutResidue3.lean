module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutPsu42
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutAlt8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutProp21

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSporadicStandard.M24Std
  CFSG.EvenSporadicStandard.M23Std

structure Fin77aOuterResidue₃ : Prop where
  fusion : Fin77aOuterSit fun X _ _ z => OuterFusion X z
  a6a6 : Fin77aOuterSit fun X _ _ _ => ¬ (Nonempty (egaLayer X ≃*
    alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
    ∃ f : X →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2)
  sp44 : Fin77aOuterSit fun X _ _ z => ¬ (LieModel (egaLayer X) .PSp 2 2 2 ∧
    z ∉ egaLayer X ⊔ centralizer (egaLayer X : Set X) ∧
    Nonempty (↥(egaLayer X ⊓ centralizer ({z} : Set X)) ≃* Equiv.Perm (Fin 6)))

theorem fin77aOuterRest₄_of_residue₃ (hP : Fin77aProp21K)
    (hR : Fin77aOuterResidue₃) : Fin77aOuterRest₄ := by
  intro G _ _ _ L z t T₁ F tb Q x L1 hS ⟨hz, hC⟩
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have hF := hR.fusion G L z t T₁ F tb Q x L1 hS hz hC
  have hz2 : (QuotientGroup.mk Sup.zX : Xbar L1) * QuotientGroup.mk Sup.zX = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk Sup.zX : Xbar L1)
    rwa [Sup.orderOf_zbar, sq] at this
  rcases Sup.prop21_outcome hP (Sup.isKGroupCat_xbar hS.std) hC with
    h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨⟨e⟩, h2⟩ | ⟨h1, h2⟩
  · exact not_mem_fusionZStar hF h
  · exact hR.a6a6 G L z t T₁ F tb Q x L1 hS hz hC ⟨h1, h2⟩
  · exact hR.sp44 G L z t T₁ F tb Q x L1 hS hz hC ⟨h1, h2, h3⟩
  · exact not_alt8_of_outerFusion hz2 hC hF e h2
  · exact not_psu42_of_outerFusion hz2 hC hF h1 h2

end CFSG.EvenSporadicStandard.M22Std
