module

public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

noncomputable abbrev graphP (L : Type) [Field L] : ModGL Tag.E6 L :=
  diagramMap TwistTag.E6 L

section E6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def GraphCentralizerEmpty (S : LangSetup .E6 L p) (D₁ : Subgroup (ModGL .E6 L)) : Prop :=
  ∀ w ∈ adjointGroup .E6 L, ¬ ∀ x ∈ rigidTestSet S D₁,
    Commute (w * graphP L) x

theorem setupRigid_of_descends_E6 (S : LangSetup .E6 L p) (hd : S.Descends)
    (hF : ∀ D₁ : Subgroup (ModGL .E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      NoFrobeniusInner S D₁)
    (hI : ∀ D₁ : Subgroup (ModGL .E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      CentralizerTrivial S D₁)
    (hIg : ∀ D₁ : Subgroup (ModGL .E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      GraphCentralizerEmpty S D₁) : SetupRigid S := by
  obtain ⟨K, _, _, _, e, hq, he⟩ := hd
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K L
  refine setupRigid_of_model_gen S hp₀ hf hK hq e he
    {z | z ∈ adjointGroup .E6 L ∨ ∃ w ∈ adjointGroup .E6 L, z = w * graphP L}
    (fun α => ?_) hF (fun D₁ hD₁ hc z hz hzc x => ?_)
  · obtain ⟨g, a, σ, ε, hα⟩ :=
      (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 α
    refine ⟨(g : ModGL .E6 K) * rootDiagUnit .E6 a * exactQ .E6 K ε, σ, ?_, fun h => ?_⟩
    · have hga : baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) ∈
          adjointGroup .E6 L := by
        rw [map_mul, baseChangeGL_rootDiagUnit]
        exact mul_mem (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
          (torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _))
      have hg0 := S.D.g0_mem
      have hP : ∀ x ∈ adjointGroup .E6 L,
          graphP L * x * (graphP L)⁻¹ ∈ adjointGroup .E6 L :=
        fun x hx => E6GraphLevi.diagramMap_conj_mem_adjointGroup' hx
      fin_cases ε
      · left
        have hQ : exactQ .E6 K ((0 : Fin 2) : ℕ) = 1 := pow_zero (graphP K)
        simp only [Fin.val_zero] at hQ ⊢
        rw [hQ, mul_one]
        exact mul_mem (mul_mem (inv_mem hg0) hga) hg0
      · right
        refine ⟨S.D.g0⁻¹ * baseChangeGL (algebraMap K L) ((g : ModGL .E6 K) * rootDiagUnit .E6 a) *
          (graphP L * S.D.g0 * (graphP L)⁻¹), ?_, ?_⟩
        · exact mul_mem (mul_mem (inv_mem hg0) hga) (hP _ hg0)
        · have hQ : exactQ .E6 K ((1 : Fin 2) : ℕ) = graphP K := pow_one (graphP K)
          have hbc : baseChangeGL (algebraMap K L) (graphP K) = graphP L :=
            baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6
          simp only [Fin.val_one] at hQ ⊢
          rw [hQ, map_mul, hbc]
          group
    · rw [hα h, mul_inv_rev, mul_inv_rev]
      group
  · rcases hz with hz | ⟨w, hw, rfl⟩
    · rw [hI D₁ hD₁ hc z hz hzc]
      exact Commute.one_left _
    · exact absurd hzc (hIg D₁ hD₁ hc w hw)

end E6

end CFSG.HardMathSupport.Timmesfeld.LangTorus
