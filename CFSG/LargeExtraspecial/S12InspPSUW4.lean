module

public import CFSG.LargeExtraspecial.S12InspP5Main
public import CFSG.LargeExtraspecial.S12InspFamER3b
public import CFSG.LargeExtraspecial.S12InspPSUMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Open

@[expose] def Insp4FischerResidual3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) → 25920 ∣ Nat.card S.Mbar →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 → ¬ S.IsNondeg12 g →
    fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

theorem insp4FischerResidual2_of_3 (h : Insp4FischerResidual3) : Insp4FischerResidual2 := by
  intro G _ _ _ S g t haQ hne hw hP hM ht htA hS hred hdeg hres
  rcases hres with hU | ⟨-, f, hsymm, hnd, hmodel⟩
  · exact h G S g t haQ hne hw hP hM ht htA hS hred hdeg hU
  have hf : CFSG.Fischer.Classification.IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff _).1 hmodel
  rcases CFSG.Fischer.Classification.R3_five_cases hf with ⟨h45, -⟩ | ⟨h36, -⟩
  · obtain ⟨ψ', hψ'⟩ := CFSG.Fischer.Classification.exists_mulEquiv_U2_four_of_ncard hf h45
    have himg : ψ '' (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) =
        CFSG.Fischer.Classification.D3 f := by
      ext q
      refine ⟨?_, fun hq => ⟨ψ.symm q, (hψ _).2 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply ψ q⟩⟩
      rintro ⟨x, hx, rfl⟩
      exact (hψ x).1 hx
    have hmodel' : fischerCentralQuotientModel
        (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
        (CFSG.Fischer.Classification.Unitary.SUm 4)
        (CFSG.Fischer.Classification.Unitary.TU 4) := by
      refine CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2.2 ⟨ψ.trans ψ', ?_⟩
      rw [MulEquiv.coe_trans, Set.image_comp, himg, hψ']
    exact h G S g t haQ hne hw hP hM ht htA hS hred hdeg hmodel'
  · exact (Setting.false_of_R3 r3SimpleInput haQ hne (by omega) ht htA le_rfl hf (fun _ => h36)
      ψ hψ).elim

@[expose] def Insp4FischerResidual4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → S.width = 4 →
    (∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) → 25920 ∣ Nat.card S.Mbar →
    t ∈ S.Lbar g → IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t →
    ¬ S.IsReducible12 → ¬ S.IsNondeg12 g →
    fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0) →
    (∀ y ∈ S.Xbar12 g, y ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) → y ^ 3 = 1 →
      y ≠ 1 → ∃ x ∈ S.Xbar12 g, x ∈ S.Lbar g ∧
        x ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧ x * y ≠ y * x) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

theorem insp4FischerResidual3_of_4 (h : Insp4FischerResidual4) : Insp4FischerResidual3 := by
  intro G _ _ _ S g t haQ hne hw hP hM ht htA hS hred hdeg hU
  by_cases hy : ∀ y ∈ S.Xbar12 g, y ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) →
      y ^ 3 = 1 → y ≠ 1 → ∃ x ∈ S.Xbar12 g, x ∈ S.Lbar g ∧
        x ∈ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧ x * y ≠ y * x
  · exact h G S g t haQ hne hw hP hM ht htA hS hred hdeg hU hy
  exfalso
  push Not at hy
  obtain ⟨y, hyX, hyK, hy3, hy1, hc⟩ := hy
  exact Setting.false_of_order_three_mem_fixSub12 haQ hne (by omega) ht htA
    (Setting.Xbar12_le_Mbar hyX) hyX hyK hy3 hy1 hc

end CFSG.LargeExtraspecial
