module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.ModR

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.Quasithin.SmithC27

@[expose] def SimpleStmt (Y : Type) [Group Y] : Prop :=
  ∀ R : Subgroup Y, R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)) →
    LeviStructure (⊤ : Subgroup Y) R ∧
      ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) ≠ ⊤ →
        ∀ x : Y, (∀ r ∈ R, x * r = r * x) → x ∈ R)

theorem leviStructure_improper {Y : Type} [Group Y] [Finite Y] (hq : CFSG.IsQuasisimple Y)
    (hZ : Subgroup.center Y = ⊥) (hcl : IsClassicalTwoOrG2 Y) {R : Subgroup Y}
    (hR : R = pCoreOf 2 ((⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y)))
    (htop : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) = ⊤) :
    LeviStructure (⊤ : Subgroup Y) R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq' : CFSG.IsQuasisimple ↥(⊤ : Subgroup Y) :=
    isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
  have hR2 : IsPGroup 2 R := by rw [hR]; exact pCoreOf_isPGroup 2 _
  have hN : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (R : Set Y) := by
    intro x _
    have : x ∈ (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) := by rw [htop]; exact trivial
    exact this.2
  have hRbot : R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have := mem_center_of_mem_inf_of_quasisimple (C := ⊤) (R := R) hq' hR2 hN
      (c := ⟨r, trivial⟩) hr
    have h2 : r ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff] at this ⊢
      intro g
      exact congrArg Subtype.val (this ⟨g, trivial⟩)
    rw [hZ] at h2
    exact h2
  subst hRbot
  have hclTop : IsClassicalTwoOrG2 (↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y)) := by
    have e1 : ↥(⊤ : Subgroup Y) ⧸ Subgroup.center ↥(⊤ : Subgroup Y) ≃*
        Y ⧸ Subgroup.center Y := quotCenterCongr Subgroup.topEquiv
    have e2 : Y ⧸ Subgroup.center Y ≃* Y :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact isClassicalTwoOrG2_of_mulEquiv (e1.trans e2).symm hcl
  refine ⟨1, fun _ => ⊤, ⊥, le_rfl, bot_le, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact ⟨le_inf le_top hN, hq', hclTop, bot_le⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · rw [htop]
    simp

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
