module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.YLevel
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitarySplit

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Open CFSG.AGLEmbedding CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

variable {Y : Type} [Group Y]

theorem false_of_split_unitary_field_cube {Rb : Sylow 3 Y}
    {Y₀ : Subgroup Y} [Finite Y] (h : ReducedNongeneration 3 Y Rb Y₀) {K E : Subgroup Y}
    [K.Normal] (hK : Open.IsQuasisimple K) (hER : E ≤ (Rb : Subgroup Y))
    (hEN : E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hEKC : ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    {ℓ f : ℕ} {F : Type} [Field F] (hU : UnitaryFieldData ℓ f F) (hq3 : 3 ∣ ℓ ^ f + 1)
    (hq8 : ℓ ^ f ≠ 8) (e : K ⧸ Subgroup.center K ≃* unitaryPSU hU 3)
    (hsplit : ∃ (α : MulAut (unitaryPSU hU 3)) (σ : F ≃+* F)
      (A : Subgroup (MulAut (unitaryPSU hU 3))), orderOf σ = 3 ∧
        SplitDataU hU σ A ((E.map (modelAct K e)).map (MulAut.conj α).toMonoidHom)) : False := by
  classical
  obtain ⟨α, σ, A, hσ, hd⟩ := hsplit
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hEp : IsPGroup 3 E := isPGroup_three_of_le hEa.2 le_rfl
  set B : Subgroup (MulAut (unitaryPSU hU 3)) := E.map (modelAct K e) with hB
  have hBp : IsPGroup 3 (B.map (MulAut.conj α).toMonoidHom) := by
    rw [hB, Subgroup.map_map]
    exact hEp.map _
  have : Finite (B.map (MulAut.conj α).toMonoidHom) := by
    rw [hB, Subgroup.map_map]
    exact Finite.of_surjective
      (fun x : E => (⟨((MulAut.conj α).toMonoidHom.comp (modelAct K e)) x, x, x.2, rfl⟩ :
        E.map ((MulAut.conj α).toMonoidHom.comp (modelAct K e))))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨s, hs⟩ := (IsPGroup.iff_card).1 hBp
  have hbot : B ≠ ⊥ := by
    intro hb
    exact hEKC ((le_centralizer_of_modelAct_trivial hperf e hb).trans le_sup_right)
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have : s = 0 := by omega
    rw [this, pow_zero] at hs
    apply hbot
    have h1 : Nat.card (B.map (MulAut.conj α).toMonoidHom) = 1 := hs
    have : B.map (MulAut.conj α).toMonoidHom = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    rw [← Subgroup.map_bot (MulAut.conj α).toMonoidHom] at this
    exact Subgroup.map_injective (MulAut.conj α).injective this
  have hgenα := closure_hyperplane_fixed_eq_top_u hU hq3 hq8 hσ hd hs1 hs
  have hgenB := closure_hyperFixed_of_conj α B hgenα
  have hgenK := closure_hyperplane_quot_of_model (K := K) (E := E) e hgenB
  have hgen := hyperGen_of_generation K E hK hEa hgenK
  exact h.false_of_hyperGen hEa hEc hER hEN hgen

end CFSG.HardMathSupport.Foote.ModuleExclusions
