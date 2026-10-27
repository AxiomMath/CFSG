module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LargeExtraspecial.S45QOmega
public import CFSG.LargeExtraspecial.BridgeForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Module CFSG.Open CFSG.ABGLocalTools

theorem omegaPlus8Simple : OmegaPlus8Simple := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) with hQdef
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have hdim : finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by simp
  obtain ⟨W, hW, hWQ⟩ := CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (K := ZMod 2) 4
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_three_hypPairs hQ (T := W) (by omega) hWQ
  have hs := LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_hypPairs hQ (by omega) h₁₂ h₁₃
    h₂₃
  have hna := LargeExtraspecial.S45Q.nonabelianSylowTwo_omegaGroup hQ (by omega)
  let F : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 4) (ZMod 2) (ZMod 2)
  have hF : ∀ v, timmesfeldPlusForm 4 (F v) = Q v := fun v => by
    rw [hQdef, CFSG.LieType.Universal.Spin.quadPlus_apply]
    rfl
  have hO : TauCeti.QuadraticMap.orthogonalGroup Q = timmesfeldIsometries (⇑Q) := by
    ext g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  have hΩ := CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ
    (show 6 ≤ finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) by omega)
  have hmap : (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ).map
      (LargeExtraspecial.Bridge.conjLinearEquiv F).toMonoidHom = timmesfeldOmegaPlus 4 := by
    rw [← hΩ, Subgroup.map_commutator, hO, LargeExtraspecial.Bridge.isometries_map F hF]
    rfl
  let e := LargeExtraspecial.Bridge.equivOfMapEq _ hmap
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  have : Finite (Fin 4 ⊕ Fin 4 → ZMod 2) := Module.finite_of_finite (ZMod 2)
  have : Finite ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    Finite.of_injective (fun g : (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] _ => (g : _ → _))
      fun g₁ g₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ)
  obtain ⟨hPX, hP2, hPi⟩ := isSylowOf_iff.mp hP
  obtain ⟨a, ha, b, hb, hab⟩ := hna P hPX hP2 hPi
  refine ⟨e ⟨a, hPX ha⟩, e ⟨b, hPX hb⟩, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

end CFSG.ComponentClassification.AS81
