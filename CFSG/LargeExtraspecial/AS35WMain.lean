module

public import CFSG.LargeExtraspecial.AS35DMain
public import CFSG.LargeExtraspecial.AS35WSect
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35W

@[expose] def GH74List (X : Type) [Group X] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (Blueprint.LieModel X .G2 0 p f ∨ Blueprint.LieModel X .trialityD4 0 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel X .PSp 2 p f) ∨
    (∃ f : ℕ, Blueprint.LieModel X .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧
      Blueprint.LieModel X .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧
      Blueprint.LieModel X .PSU 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ Blueprint.LieModel X .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ Blueprint.LieModel X .PSU 5 p f) ∨
    (Blueprint.LieModel X .PSL 2 2 3 ∨ Blueprint.LieModel X .PSL 2 2 4 ∨
      Blueprint.LieModel X .PSL 3 2 2 ∨ Blueprint.LieModel X .twistedB2 0 2 3) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (Blueprint.NativeSporadic.IsSporadic X .M12 ∨ Blueprint.NativeSporadic.IsSporadic X .M22 ∨
      Blueprint.NativeSporadic.IsSporadic X .M23 ∨ Blueprint.NativeSporadic.IsSporadic X .J1 ∨
      Blueprint.NativeSporadic.IsSporadic X .J2 ∨ Blueprint.NativeSporadic.IsSporadic X .J3 ∨
      Blueprint.NativeSporadic.IsSporadic X .McL ∨ Blueprint.NativeSporadic.IsSporadic X .Ly)

@[expose] def GH74Models : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    3 ≤ Open.twoRank G →
    (∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
    GH74List G

@[expose] def GH74W2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X], 3 ≤ Open.twoRank X → GH74List X → W2Good X

@[expose] def RankTwoW2Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], Open.twoRank X ≤ 2 →
    ∀ z : X, ¬ W2Data X z

end AS35W

namespace S14

theorem aschbacherWidthTwoResidual_of_inspection (hGH : AS35W.GH74Models)
    (hR2 : AS35W.RankTwoW2Input) (hL : AS35W.GH74W2Input) : AschbacherWidthTwoResidual := by
  intro G _ _ S hw hW hO hsimp hC htop g₁ g₂
  have : S.zGen.Normal := S.zGen_normal
  have hzL : S.z ∈ S.zGen := S.z_mem_zGen
  have hD := S.w2Data_of_normal hzL hw hW hO hC
  have hconj : ∀ g : G, ∃ l : S.zGen, g * S.z * g⁻¹ = (l : G) * S.z * (l : G)⁻¹ := by
    intro g
    have hg : g ∈ S.zGen ⊔ S.QG := by rw [htop]; exact Subgroup.mem_top g
    obtain ⟨y, hy, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨y, hy⟩, ?_⟩
    have hqz : q * S.z * q⁻¹ = S.z := by
      rw [S.mem_M_iff.mp (S.QG_le_M hq), mul_inv_cancel_right]
    calc y * q * S.z * (y * q)⁻¹ = y * (q * S.z * q⁻¹) * y⁻¹ := by group
      _ = y * S.z * y⁻¹ := by rw [hqz]
  obtain ⟨l₁, hl₁⟩ := hconj g₁
  obtain ⟨l₂, hl₂⟩ := hconj g₂
  rw [hl₁, hl₂]
  have hnab : ∃ a b : S.zGen, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hzC : S.z ∈ centralizer (S.zGen : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (hab ⟨l, hl⟩ ⟨S.z, hzL⟩)
    rw [hC, Subgroup.mem_bot] at hzC
    exact S.z_ne_one hzC
  by_cases hr : 3 ≤ Open.twoRank S.zGen
  · have hgen := S.gen4_of_normal hzL hw hW hO hC
    have hlist : AS35W.GH74List S.zGen := hGH S.zGen hnab hr hgen
    have hc := hL S.zGen hr hlist _ hD l₁ l₂
    rw [← Subgroup.orderOf_coe] at hc
    simpa using hc
  · exact absurd hD (hR2 S.zGen (by omega) _)

end S14

end CFSG.LargeExtraspecial
