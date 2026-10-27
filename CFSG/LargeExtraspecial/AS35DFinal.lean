module

public import CFSG.LargeExtraspecial.AS35DMain
public import CFSG.LargeExtraspecial.AS35DSixThreeE
public import CFSG.LargeExtraspecial.AS35DSixFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S14

@[expose] def AschbacherSecFiveSixRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    3 ≤ S.width → (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) →
    (∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t) →
    IsSimpleGroup S.zGen → centralizer (S.zGen : Set G) = ⊥ → S.zGen ⊔ S.QG = ⊤ →
    (∃ H : Subgroup G, S.IsHSet H) →
    (∀ H : Subgroup G, S.IsHStar H → S.IsAFive H ∧
      ∀ g ∈ H, g ∉ S.M → H = S.QG ⊔ S.Qa g ∧ ¬ IsConj S.z (S.z * (g * S.z * g⁻¹))) →
      (∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
        (S.width = 4 ∧ Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2))

theorem secFiveSixResidual_of (h22 : AschbacherTwoTwoStmt) (h75 : AschbacherTIInput)
    (hRest : AschbacherSecFiveSixRest) : AschbacherSecFiveSixResidual := by
  intro G _ _ S ih hn hW hO hsimp hC htop
  have hM : S.M ≠ ⊤ := by
    intro hM
    have hzC : S.z ∈ centralizer (S.zGen : Set G) := mem_centralizer_iff.mpr fun x _ =>
      (S.mem_M_iff.mp (hM ▸ mem_top x))
    rw [hC, mem_bot] at hzC
    exact S.z_ne_one hzC
  refine hRest G S ih hn hW hO hsimp hC htop
    (sixThreeStmt_of h22 G S hn hW hO (S.exists_inf_Qa_ne_bot h75 hn hM)) fun H hH => ?_
  obtain ⟨g, hgH, hgM⟩ := Set.not_subset.mp hH.1.2.2
  refine ⟨(S.sixFour h22 hW hH hgH hgM).1, fun g' hg'H hg'M => ?_⟩
  exact (S.sixFour h22 hW hH hg'H hg'M).2

theorem aschbacherHypCore_of (hW2 : AschbacherWidthTwoResidual)
    (h22 : AschbacherTwoTwoStmt) (h75 : AschbacherTIInput) (hRest : AschbacherSecFiveSixRest) :
    AschbacherHypCore :=
  aschbacherHypCore_of_secFiveSix hW2 (secFiveSixResidual_of h22 h75 hRest)

theorem aschbacherMainStmt_of_residuals (hW2 : AschbacherWidthTwoResidual)
    (h22 : AschbacherTwoTwoStmt) (h75 : AschbacherTIInput) (hRest : AschbacherSecFiveSixRest) :
    AschbacherMainStmt :=
  aschbacherMainStmt_of hW2 (secFiveSixResidual_of h22 h75 hRest)

end S14

end CFSG.LargeExtraspecial
