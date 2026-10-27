module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section D4Base


theorem rootNorm_D4_two {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    rootNorm Tag.D4 γ = 2 := by
  induction hγ with
  | basis j => revert j; decide +kernel
  | reflect i hv ih => rw [rootNorm_reflect, ih]

theorem cartanD4_connected (i j : Fin Tag.D4.rank) :
    Relation.ReflTransGen
      (fun a b : Fin Tag.D4.rank => Tag.D4.cartan a b = -1 ∧ Tag.D4.cartan b a = -1) i j := by
  have h1 : ∀ i : Fin Tag.D4.rank, Relation.ReflTransGen
      (fun a b : Fin Tag.D4.rank => Tag.D4.cartan a b = -1 ∧ Tag.D4.cartan b a = -1) i ⟨2, by decide⟩ := by
    intro i
    fin_cases i
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
  have h2 : ∀ j : Fin Tag.D4.rank, Relation.ReflTransGen
      (fun a b : Fin Tag.D4.rank => Tag.D4.cartan a b = -1 ∧ Tag.D4.cartan b a = -1) ⟨2, by decide⟩ j := by
    intro j
    fin_cases j
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by decide, by decide⟩
  exact (h1 i).trans (h2 j)

theorem isSimpleGroup_adjointGroup_D4 (K : Type) [Field K] [Finite K] :
    IsSimpleGroup ↥(adjointGroup Tag.D4 K) := by
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.D4 K) := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
      (CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus (K := K)
        (by norm_num : 3 ≤ 4))
      (CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.thetaOmega_surjective K) ?_
    obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.exists_ne_one_adjointGroup_D4 K
    obtain ⟨x, rfl⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.thetaOmega_surjective K c
    exact ⟨x, hc⟩
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem IsMaxHeightRoot.commute_xPar_of_cone {τ : Tag} {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hpos : 0 < height γ)
    {K : Type} [Field K] (a b : K) :
    Commute (xPar (rootOperatorFamily τ) θ a) (xPar (rootOperatorFamily τ) γ b) := by
  by_cases hγθ : γ = θ
  · subst hγθ
    rw [Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
  · have hne : (⟨θ, hθ.1⟩ : Root τ) ≠ ⟨γ, hγ⟩ := fun h => hγθ (congrArg Subtype.val h).symm
    have hc := commContained_pos K ⟨θ, hθ.1⟩ ⟨γ, hγ⟩ hθ.height_pos hpos hne
    have hempty : (⨆ (δ : Root τ) (_ : ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
        δ.1 = m • θ + n • γ), (rootOperatorFamily τ).rootSubgroup K δ) = ⊥ := by
      refine eq_bot_iff.2 (iSup₂_le fun δ hδ => ?_)
      exfalso
      obtain ⟨m, n, hm, hn, hδe⟩ := hδ
      have h1 := hθ.2 δ.1 δ.2
      rw [hδe, height_add_eq] at h1
      have e1 : height (m • θ) = m * height θ := by simp [height, Finset.mul_sum]
      have e2 : height (n • γ) = n * height γ := by simp [height, Finset.mul_sum]
      rw [e1, e2] at h1
      have h3 : (1 : ℤ) ≤ m := by exact_mod_cast hm
      have h4 : (1 : ℤ) ≤ n := by exact_mod_cast hn
      nlinarith [hθ.height_pos]
    have hx := hc _ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup ⟨θ, hθ.1⟩ a) _
      ((rootOperatorFamily τ).eltElement_mem_rootSubgroup ⟨γ, hγ⟩ b)
    rw [hempty, Subgroup.mem_bot] at hx
    rw [xPar_of_isRoot hθ.1, xPar_of_isRoot hγ]
    exact commutatorElement_eq_one_iff_commute.1 (by rw [commutatorElement_def]; exact hx)

theorem commutator_xPar_D4_neighbour {K : Type} [Field K] :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      ⁅xPar (rootOperatorFamily Tag.D4) (Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1) a,
          xPar (rootOperatorFamily Tag.D4) (Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1) b⁆ =
        xPar (rootOperatorFamily Tag.D4)
          (Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1 +
            Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1) ((ε : K) * a * b) := by
  refine ⟨1, Or.inl rfl, fun a b => ?_⟩
  have hc : RootOps.repCheck Tag.D4 2 0 [(1, 1, 5, 1)] = true := by decide +kernel
  have h := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := Tag.D4) (K := K) hc a b
  have e2 : (Tag.rootCertificate Tag.D4).root 2 =
      Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1 := by decide
  have e0 : (Tag.rootCertificate Tag.D4).root 0 =
      Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 := by decide
  have e5 : (Tag.rootCertificate Tag.D4).root 5 =
      Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1 +
        Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) 1 := by decide
  rw [e2, e0] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one, e5] at h
  rw [h]

end D4Base

end CFSG.LieType.SeitzGeneration.ExcWideThree
