module

public import CFSG.GF2Type.Smith1979.W4C2Local
public import CFSG.GF2Type.Smith1979.W4C2Dual
public import CFSG.LargeExtraspecial.GLW4Elim
public import CFSG.LargeExtraspecial.GLW4Config
public import CFSG.LargeExtraspecial.GLRMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_data_w4 [IsSimpleGroup G] {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hw : S.width = 4) (hR : S.S12GammaLResidual g t)
    {A B : Submodule (ZMod 2) S.Qt} (hP : Pair S (S.Xbar12 g) A B)
    (hmap : ∀ σ ∈ S.Mbar, σ ∉ S.Xbar12 g →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    (haA : S.cl (g * S.z * g⁻¹) ∈ A)
    (hfus : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG →
      S.cl (k * S.z * k⁻¹) ∈ A ∨ S.cl (k * S.z * k⁻¹) ∈ B) : False := by
  obtain ⟨-, hC1, -, hind, ⟨φ⟩, -⟩ := hR
  have hcard : Nat.card (S.Lbar g) = 2 ^ (S.width - 1) := by
    obtain ⟨m, -, -, hm⟩ := hC1.model
    rcases hm with ⟨hL, hidx', hC⟩ | ⟨-, hL8, -⟩
    · obtain ⟨hnm, -⟩ := Setting.case1_finrank haQ hne (by omega) hL hidx' hC
      rw [hL, hnm]
    · rw [hL8, hw]
      norm_num
  have hD : Data S (S.Xbar12 g) A B g :=
    ⟨hP, by omega, Setting.Xbar12_le_Mbar, hind, hmap, haQ, hne, haA, hcard, hfus⟩
  obtain ⟨C⟩ := GLW4.nonempty_config_of_data hD ⟨φ⟩
  exact GLW4.false_of_config_four C hw

theorem false_of_s12GammaLResidual_w4 [IsSimpleGroup G]
    (hSL : S12SL4ModuleInput) {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hw : S.width = 4) (hR : S.S12GammaLResidual g t) : False := by
  obtain ⟨A, B, hP, hmap⟩ := exists_pair_of_residual_w4 hSL hw hR
  have hind : (S.Xbar12 g).relIndex S.Mbar = 2 := hR.2.2.2.1
  have hXM : S.Xbar12 g ≤ S.Mbar := Setting.Xbar12_le_Mbar
  have hloc := localTest_setting hP hw hXM hind hmap haQ hne
  have hfus : ∀ k : G, k * S.z * k⁻¹ ∈ S.QG →
      S.cl (k * S.z * k⁻¹) ∈ A ∨ S.cl (k * S.z * k⁻¹) ∈ B := by
    intro k hk
    by_cases hz : k * S.z * k⁻¹ = S.z
    · left
      rw [hz, S.cl_z]
      exact A.zero_mem
    · exact (localTest_setting hP hw hXM hind hmap hk hz).1
  rcases hR.2.2.2.2.2 with hfirst | ⟨-, hL8, honly⟩
  · rcases hloc.1 with hA | hB
    · exact false_of_data_w4 haQ hne hw hR hP hmap hA hfus
    · refine false_of_data_w4 haQ hne hw hR hP.symm ?_ hB fun k hk => (hfus k hk).symm
      intro σ hσ hσX
      have hσσ : σ * σ ∈ S.Xbar12 g := s12_mul_mem_of_relIndex_two hind hσ hσ hσX hσX
      have h1 := hP.map_A_eq hσσ
      rw [← hmap σ hσ hσX, ← Submodule.map_comp]
      exact h1
  · have hall : ∀ ℓ ∈ S.Lbar g, ℓ = 1 ∨ ℓ = t := by
      intro ℓ hℓ
      by_cases h1 : ℓ = 1
      · exact Or.inl h1
      · exact Or.inr (honly ℓ (Setting.mem_Ebar12_of_mem_Lbar hℓ (hloc.2 ℓ hℓ h1)) hℓ)
    have hsub : (S.Lbar g : Set S.O) ⊆ {1, t} := fun ℓ hℓ => by
      rcases hall ℓ hℓ with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h2 : Nat.card (S.Lbar g) ≤ 2 := by
      have h3 : Nat.card (S.Lbar g) = (S.Lbar g : Set S.O).ncard := Nat.card_coe_set_eq _
      rw [h3]
      calc (S.Lbar g : Set S.O).ncard ≤ ({1, t} : Set S.O).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le 1 {t}).trans (by rw [Set.ncard_singleton])
    omega

theorem not_s12GammaLResidual_of_four_le [IsSimpleGroup G]
    (hSL : S12SL4ModuleInput) {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) : ¬ S.S12GammaLResidual g t := by
  by_cases hw : S.width = 4
  · exact fun hR => false_of_s12GammaLResidual_w4 hSL haQ hne hw hR
  · exact Setting.not_s12GammaLResidual haQ hne (by omega)

theorem timmesfeld_12_16_of_four_le
    [IsSimpleGroup G] (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Timmesfeld12_3InspectionInput)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 4 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight := by
  rcases W4C1.timmesfeld_12_16_of_C1 (S := S) hRI hARS hTri hFischer hInsp h36 hSL haQ hne hn ht
    htA with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (not_s12GammaLResidual_of_four_le hSL haQ hne hn h).elim

theorem timmesfeld_12_16_w4
    [IsSimpleGroup G] (hRI : RootInvolutionComponentsInput.{0}) (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hFischer : S12FischerStatement)
    (hInsp : Timmesfeld12_3InspectionInput) (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hw : S.width = 4)
    {t : S.O} (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.IsReducible12 ∨ S.S12OmegaPlusEight :=
  timmesfeld_12_16_of_four_le hRI hARS hTri hFischer hInsp h36 hSL haQ hne (by omega) ht htA

end CFSG.GF2Type.Smith1979.W4C2
