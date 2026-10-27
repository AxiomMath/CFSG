module

public import CFSG.LargeExtraspecial.S12FifteenB
public import CFSG.LargeExtraspecial.S12FourteenMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] def S12SpSixSpin (g : G) : Prop :=
  S.width = 4 ∧ S.Xbar12 g = S.Mbar ∧
    ∃ b : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2), (∀ x, b x x = 0) ∧
      (∀ x, (∀ y, b x y = 0) → x = 0) ∧ Nonempty (S.Xbar12 g ≃* s12SpIsometries b)

end Setting

@[expose] def Timmesfeld12_3InspectionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → 4 ≤ S.width → t ∈ S.Lbar g →
    IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 → S.S12Standing g t → ¬ S.IsReducible12 →
    ((S.IsNondeg12 g ∧ CFSG.Timmesfeld.Outcome (S.Xbar12 g)) ∨
      (¬ S.IsNondeg12 g ∧
        S12FischerConclusion (S.Xbar12 g) (Subtype.val ⁻¹' S.Ebar12 g))) →
    S.S12Case1 g t ∨ (S.IsNondeg12 g ∧ S.S12Case2 g t) ∨ S.S12IndexCert g ∨
      (¬ S.IsNondeg12 g ∧ S.S12FuseCert g t) ∨ S.S12GenCert g ∨ Nat.card (S.Lbar g) ≤ 4 ∨
      S.S12SpSixSpin g

@[expose] def S12SL4ModuleInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V],
    finrank (ZMod 2) V = 8 → ∀ H : Subgroup (V ≃ₗ[ZMod 2] V),
      Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ h ∈ H, ∀ v ∈ W, h v ∈ W

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] def S12GammaLResidual (g : G) (t : S.O) : Prop :=
  S.S12Standing g t ∧ S.S12Case1 g t ∧ ¬ S.IsReducible12 ∧
    (S.Xbar12 g).relIndex S.Mbar = 2 ∧
    Nonempty (S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin S.width) (ZMod 2)) ∧
    ((finrank (ZMod 2) (S.spanOrbitX12 g) = S.width ∧
        (∀ v ∈ S.spanOrbitX12 g, S.q v = 0) ∧
        (∀ w ∈ S.spanOrbitX12 g, w ≠ 0 →
          ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = w) ∧
        ∀ σ ∈ S.Mbar, σ ∉ S.Xbar12 g →
          S.spanOrbitX12 g ⊓
              (S.spanOrbitX12 g).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = ⊥ ∧
            S.spanOrbitX12 g ⊔
              (S.spanOrbitX12 g).map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = ⊤) ∨
      (S.width = 4 ∧ Nat.card (S.Lbar g) = 8 ∧ ∀ d ∈ S.Ebar12 g, d ∈ S.Lbar g → d = t))

variable {S} [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem isReducible12_of_SL4 (hSL : S12SL4ModuleInput) {g : G} (hn : S.width = 4)
    (hXM : S.Xbar12 g = S.Mbar)
    (φ : S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : S.IsReducible12 := by
  have hdim : finrank (ZMod 2) S.Qt = 8 := by rw [S.finrank_Qt_eq_two_mul_width, hn]
  set H := (S.Xbar12 g).map S.O.subtype
  have ψ : H ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((S.Xbar12 g).equivMapOfInjective S.O.subtype (subtype_injective _)).symm.trans φ
  obtain ⟨W, hW0, hWt, hWH⟩ := hSL S.Qt hdim H ⟨ψ⟩
  refine ⟨W, hW0, hWt, fun m v hv => hWH _ ?_ v hv⟩
  exact ⟨S.ρ m, hXM ▸ (⟨m, rfl⟩ : S.ρ m ∈ S.Mbar), rfl⟩

omit [IsSimpleGroup G] in
theorem timmesfeld_12_15 (hSL : S12SL4ModuleInput) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (hC1 : S.S12Case1 g t) :
    S.IsReducible12 ∨ S.S12GammaLResidual g t := by
  by_cases hred : S.IsReducible12
  · exact Or.inl hred
  obtain ⟨m, hm3, ⟨φ⟩, ⟨hL, hidx, hC⟩ | ⟨hm4, hL8, honly⟩⟩ := hC1.model
  · obtain ⟨hnm, hdim⟩ := case1_finrank haQ hne (by omega) hL hidx hC
    subst hnm
    by_cases hXM : S.Xbar12 g = S.Mbar
    · exact Or.inl (isReducible12_of_case1 haQ hne (by omega) hL hidx hC hXM)
    · obtain ⟨hind, hdim', hq, htr, hσ⟩ :=
        case1_gammaL_structure haQ hne (by omega) hC1 hL hidx hC hXM hred
      exact Or.inr ⟨hS, hC1, hred, hind, ⟨φ⟩, Or.inl ⟨hdim', hq, htr, hσ⟩⟩
  · subst hm4
    have hn4 : S.width = 4 := by
      have h1 := S.card_Lbar_ge haQ hne
      rw [hL8] at h1
      have h2 : S.width - 1 ≤ 3 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h1)
      omega
    by_cases hXM : S.Xbar12 g = S.Mbar
    · exact Or.inl (isReducible12_of_SL4 hSL hn4 hXM φ)
    · have φ' : S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin S.width) (ZMod 2) := by
        rw [hn4]
        exact φ
      exact Or.inr ⟨hS, hC1, hred, relIndex_Xbar12_eq_two hC1 hXM, ⟨φ'⟩,
        Or.inr ⟨hn4, hL8, honly⟩⟩

theorem timmesfeld_12_16 (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Timmesfeld12_3InspectionInput)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight ∨ S.S12GammaLResidual g t ∨ S.S12SpSixSpin g := by
  by_cases hred : S.IsReducible12
  · exact Or.inl hred
  have hS := (s12Standing_or hRI haQ hne hn ht htA).resolve_left hred
  have hcls :=
    (timmesfeld_12_3_classification hRI hARS hTri hFischer haQ hne hn ht htA).resolve_left hred
  have hn3 : 3 ≤ S.width := by omega
  rcases hInsp G S g t haQ hne hn ht htA hS hred hcls with hC1 | ⟨-, hC2⟩ | hI | ⟨hdeg, hF⟩ |
      hG | hL4 | hSp
  · rcases timmesfeld_12_15 hSL haQ hne hn hS hC1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases timmesfeld_12_14 h36 haQ hne hn hS hC2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inl (isReducible12_of_indexCert haQ hne hn3 ht htA hI)
  · exact Or.inl (isReducible12_of_fuseCert haQ hne hn3 ht htA hdeg hF)
  · exact Or.inl (isReducible12_of_genCert haQ hne hn hG)
  · exact (false_of_card_Lbar_le haQ hne hn hL4).elim
  · exact Or.inr (Or.inr (Or.inr hSp))

end Setting

end CFSG.LargeExtraspecial
