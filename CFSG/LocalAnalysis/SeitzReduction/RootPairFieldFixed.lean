module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusStepA
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {k K : Type} [Field k] [CharP k 2] [Field K] [CharP K 2]

theorem map_rootPairSL2_eq_inf_fixed_of_charTwo (τ : Tag) (ι : k →+* K) (σ : K ≃+* K)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    (rootPairSL2 τ k β).map (adjointBaseChangeHom τ ι) =
      rootPairSL2 τ K β ⊓ MonoidHom.eqLocus (adjointBaseChangeHom τ σ.toRingHom)
        (MonoidHom.id (adjointGroup τ K)) := by
  apply Subgroup.ext
  intro R
  constructor
  · intro hR
    obtain ⟨R0, hR0, rfl⟩ := Subgroup.mem_map.1 hR
    change (R0 : ModGL τ k) ∈ rootSubgroup τ k β ⊔ rootSubgroup τ k (-β) at hR0
    rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at hR0
    obtain ⟨A0, hA0⟩ := hR0
    have hImage : (adjointBaseChangeHom τ ι R0 : ModGL τ K) =
        rootSL2 τ K β (Matrix.SpecialLinearGroup.map ι A0) := by
      rw [coe_adjointBaseChangeHom, ← hA0,
        CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo ι hβ]
    have hcoeff : Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map ι A0) =
        Matrix.SpecialLinearGroup.map ι A0 := by
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      change σ.toRingHom (ι ((A0 : Matrix (Fin 2) (Fin 2) k) i j)) =
        ι ((A0 : Matrix (Fin 2) (Fin 2) k) i j)
      rw [RingEquiv.toRingHom_eq_coe]
      exact (hfix _).2 ⟨_, rfl⟩
    constructor
    · change (adjointBaseChangeHom τ ι R0 : ModGL τ K) ∈
        rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)
      rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
      exact ⟨_, hImage.symm⟩
    · change adjointBaseChangeHom τ σ.toRingHom (adjointBaseChangeHom τ ι R0) =
        adjointBaseChangeHom τ ι R0
      apply Subtype.ext
      rw [coe_adjointBaseChangeHom]
      simp only [hImage]
      rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo σ.toRingHom hβ, hcoeff]
  · rintro ⟨hR, hRF⟩
    change (R : ModGL τ K) ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) at hR
    rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ] at hR
    obtain ⟨A, hA⟩ := hR
    change adjointBaseChangeHom τ σ.toRingHom R = R at hRF
    have hRFcoe := congrArg Subtype.val hRF
    rw [coe_adjointBaseChangeHom] at hRFcoe
    have hσA : Matrix.SpecialLinearGroup.map σ.toRingHom A = A := by
      apply (CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps τ K hβ).1
      rw [← CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo σ.toRingHom hβ, hA]
      exact hRFcoe
    obtain ⟨A0, hA0⟩ := CFSG.SeitzReduction.OmegaPilot.exists_map_eq_of_fixed ι hfix hσA
    let R0 : adjointGroup τ k := ⟨rootSL2 τ k β A0, rootSL2_mem_adjointGroup β A0⟩
    have hR0 : R0 ∈ rootPairSL2 τ k β := by
      change rootSL2 τ k β A0 ∈ rootSubgroup τ k β ⊔ rootSubgroup τ k (-β)
      rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ]
      exact ⟨_, rfl⟩
    refine Subgroup.mem_map.2 ⟨R0, hR0, ?_⟩
    apply Subtype.ext
    rw [coe_adjointBaseChangeHom]
    change baseChangeGL ι (rootSL2 τ k β A0) = (R : ModGL τ K)
    rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo ι hβ, hA0]
    exact hA

end CFSG.SeitzReduction.E8Pilot
