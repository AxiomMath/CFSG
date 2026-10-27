module

public import CFSG.ClassicalInvolution.ModelFacts.TG3Common
public import CFSG.ClassicalInvolution.Uniform.U5Model
public import CFSG.ClassicalInvolution.ModelFacts.CF3All
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CSBase
public import CFSG.ClassicalInvolution.Q3.Q3DThm5
public import CFSG.ClassicalInvolution.Q3.Q3TAxis
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.ClassicalInvolution.Uniform.U5Alpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Reduction

variable {G X : Type} [Group G] [Finite G] [Group X]

theorem small_twin_reduction (ψ : G →* X) (hker : ψ.ker ≤ Subgroup.center G)
    {R₁ R₂ : Subgroup G} (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃))
    (hcommG : Commutes R₁ R₂) (hnc₁ : sl2Inv e₁ ∉ Subgroup.center G)
    (hnc₂ : sl2Inv e₂ ∉ Subgroup.center G)
    (h24₁ : Nat.card (R₁.map ψ) = 24) (h24₂ : Nat.card (R₂.map ψ) = 24) {z : X}
    (hz₁ : IsUniqueInvolution (R₁.map ψ) z) (hz₂ : IsUniqueInvolution (R₂.map ψ) z)
    {A : Subgroup X} (hA : IsElemAbelian2 A 2) (hAle : A ≤ R₁.map ψ ⊔ R₂.map ψ) :
    ∃ w ∈ A, w ≠ 1 ∧ w ≠ z ∧ ∃ r₁ ∈ R₁, ∃ r₂ ∈ R₂, ψ (r₁ * r₂) = w ∧
      r₁ * r₁ = sl2Inv e₁ ∧ r₂ * r₂ = sl2Inv e₂ := by
  classical
  have hodd := odd_natCard_galoisField_three
  obtain ⟨w, hwA, hw1, hwz⟩ := exists_mem_ne_of_card_four (z := z) hA
  have hcommψ : Commutes (R₁.map ψ) (R₂.map ψ) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcommG x hx y hy]
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commutes hcommψ (hAle hwA)
  obtain ⟨r₁, hr₁, rfl⟩ := ha
  obtain ⟨r₂, hr₂, rfl⟩ := hb
  obtain ⟨u₁, -⟩ := uniqueInvolution_map3 ψ e₁ h24₁
  obtain ⟨u₂, -⟩ := uniqueInvolution_map3 ψ e₂ h24₂
  have hψ₁ : ψ (sl2Inv e₁) = z := u₁.eq hz₁
  have hψ₂ : ψ (sl2Inv e₂) = z := u₂.eq hz₂
  have hw2 : w * w = 1 := hA.2 w hwA
  have hψw : ψ (r₁ * r₂) = w := by rw [map_mul, hab]
  have hcker : r₁ * r₂ * (r₁ * r₂) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hψw, hw2]
  have hcc : r₁ * r₂ * (r₁ * r₂) ∈ Subgroup.center G := hker hcker
  have hc_eq : r₁ * r₂ * (r₁ * r₂) = (r₁ * r₁) * (r₂ * r₂) := by
    have h1 : r₂ * r₁ = r₁ * r₂ := (hcommG r₁ hr₁ r₂ hr₂).symm
    calc r₁ * r₂ * (r₁ * r₂) = r₁ * (r₂ * r₁) * r₂ := by group
      _ = r₁ * (r₁ * r₂) * r₂ := by rw [h1]
      _ = (r₁ * r₁) * (r₂ * r₂) := by group
  have h22 : r₂ * r₂ ∈ R₂ := R₂.mul_mem hr₂ hr₂
  have h11 : r₁ * r₁ ∈ R₁ := R₁.mul_mem hr₁ hr₁
  have h1c : ∀ y ∈ R₁, (r₁ * r₁) * y = y * (r₁ * r₁) := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hcc y
    rw [hc_eq] at h
    have hyr₂ : y * (r₂ * r₂) = (r₂ * r₂) * y := hcommG y hy _ h22
    have h3 : ((r₁ * r₁) * y) * (r₂ * r₂) = (y * (r₁ * r₁)) * (r₂ * r₂) := by
      calc ((r₁ * r₁) * y) * (r₂ * r₂) = (r₁ * r₁) * (y * (r₂ * r₂)) := by group
        _ = (r₁ * r₁) * ((r₂ * r₂) * y) := by rw [hyr₂]
        _ = ((r₁ * r₁) * (r₂ * r₂)) * y := by group
        _ = y * ((r₁ * r₁) * (r₂ * r₂)) := h.symm
        _ = (y * (r₁ * r₁)) * (r₂ * r₂) := by group
    exact mul_right_cancel h3
  have h2c : ∀ y ∈ R₂, (r₂ * r₂) * y = y * (r₂ * r₂) := by
    intro y hy
    have h := Subgroup.mem_center_iff.mp hcc y
    rw [hc_eq] at h
    have hyr₁ : (r₁ * r₁) * y = y * (r₁ * r₁) := hcommG _ h11 y hy
    have h3 : (r₁ * r₁) * ((r₂ * r₂) * y) = (r₁ * r₁) * (y * (r₂ * r₂)) := by
      calc (r₁ * r₁) * ((r₂ * r₂) * y) = ((r₁ * r₁) * (r₂ * r₂)) * y := by group
        _ = y * ((r₁ * r₁) * (r₂ * r₂)) := h.symm
        _ = (y * (r₁ * r₁)) * (r₂ * r₂) := by group
        _ = ((r₁ * r₁) * y) * (r₂ * r₂) := by rw [hyr₁]
        _ = (r₁ * r₁) * (y * (r₂ * r₂)) := by group
    exact mul_left_cancel h3
  have hZ₁ := eq_one_or_eq_sl2Inv_of_central e₁ h11 h1c
  have hZ₂ := eq_one_or_eq_sl2Inv_of_central e₂ h22 h2c
  rcases hZ₁ with h₁ | h₁ <;> rcases hZ₂ with h₂ | h₂
  ·
    exfalso
    have hr₁' : r₁ = 1 ∨ r₁ = sl2Inv e₁ := by
      by_cases hr : r₁ = 1
      · exact Or.inl hr
      · right
        exact eq_sl2Inv_of_orderOf_eq_two hodd e₁ hr₁
          (orderOf_eq_prime (by rwa [pow_two]) hr)
    have hr₂' : r₂ = 1 ∨ r₂ = sl2Inv e₂ := by
      by_cases hr : r₂ = 1
      · exact Or.inl hr
      · right
        exact eq_sl2Inv_of_orderOf_eq_two hodd e₂ hr₂
          (orderOf_eq_prime (by rwa [pow_two]) hr)
    rcases hr₁' with rfl | rfl <;> rcases hr₂' with rfl | rfl
    · exact hw1 (by rw [← hab, map_one, one_mul])
    · exact hwz (by rw [← hab, map_one, one_mul, hψ₂])
    · exact hwz (by rw [← hab, map_one, mul_one, hψ₁])
    · exact hw1 (by rw [← hab, hψ₁, hψ₂, hz₁.sq])
  · exfalso
    apply hnc₂
    rw [← h₂, ← one_mul (r₂ * r₂), ← h₁, ← hc_eq]
    exact hcc
  · exfalso
    apply hnc₁
    rw [← h₁, ← mul_one (r₁ * r₁), ← h₂, ← hc_eq]
    exact hcc
  · exact ⟨w, hwA, hw1, hwz, r₁, hr₁, r₂, hr₂, hψw, h₁, h₂⟩

end Reduction

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem compGen3Twin_small_of_gen (𝓕 : Set (Subgroup G))
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hstruct : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)),
      R₁ ≠ R₂ → sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center G →
        Commutes R₁ R₂ ∧ sl2Inv e₁ ∉ Subgroup.center G ∧ sl2Inv e₂ ∉ Subgroup.center G)
    (hgen : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)),
      R₁ ≠ R₂ → sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center G →
        ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₁ = sl2Inv e₁ → r₂ * r₂ = sl2Inv e₂ →
          (⊤ : Subgroup G) ≤ Subgroup.centralizer ({sl2Inv e₁} : Set G) ⊔
            Subgroup.centralizer ({r₁ * r₂} : Set G) ⊔
            Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set G)) :
    CompGen3Twin (⟨G, 𝓕⟩ : Q3.CompData) := by
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hcomm z hz₁ hz₂ A hA hAle hzA
  obtain ⟨e₁⟩ := hsl2 R₁ hR₁
  obtain ⟨e₂⟩ := hsl2 R₂ hR₂
  have hcen := hker (twin_ratio_mem_ker ψ e₁ e₂ h24₁ h24₂ hz₁ hz₂)
  have hRne : R₁ ≠ R₂ := fun h => hne (by rw [h])
  obtain ⟨hcommG, hnc₁, hnc₂⟩ := hstruct R₁ hR₁ R₂ hR₂ e₁ e₂ hRne hcen
  obtain ⟨w, hwA, hw1, hwz, r₁, hr₁, r₂, hr₂, hψw, hr₁sq, hr₂sq⟩ :=
    small_twin_reduction ψ hker e₁ e₂ hcommG hnc₁ hnc₂ h24₁ h24₂ hz₁ hz₂ hA hAle
  have htop := hgen R₁ hR₁ R₂ hR₂ e₁ e₂ hRne hcen r₁ hr₁ r₂ hr₂ hr₁sq hr₂sq
  obtain ⟨u₁, -⟩ := uniqueInvolution_map3 ψ e₁ h24₁
  have hψ₁ : ψ (sl2Inv e₁) = z := u₁.eq hz₁
  have hmapC : ∀ g : G, (Subgroup.centralizer ({g} : Set G)).map ψ ≤
      Subgroup.centralizer ({ψ g} : Set X) ⊓ ψ.range := by
    intro g y hy
    obtain ⟨c, hc, rfl⟩ := hy
    refine Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨c, rfl⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hc]
  have hzw : z * w ≠ 1 := by
    intro h
    apply hwz
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hz₁.sq]
  calc ψ.range = (⊤ : Subgroup G).map ψ := MonoidHom.range_eq_map ψ
    _ ≤ (Subgroup.centralizer ({sl2Inv e₁} : Set G) ⊔ Subgroup.centralizer ({r₁ * r₂} : Set G) ⊔
        Subgroup.centralizer ({sl2Inv e₁ * (r₁ * r₂)} : Set G)).map ψ := Subgroup.map_mono htop
    _ ≤ _ := by
      rw [Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine (hmapC _).trans ?_
        rw [hψ₁]
        exact le_iSup₂_of_le z hzA (le_iSup_of_le hz₁.ne_one le_rfl)
      · refine (hmapC _).trans ?_
        rw [hψw]
        exact le_iSup₂_of_le w hwA (le_iSup_of_le hw1 le_rfl)
      · refine (hmapC _).trans ?_
        rw [map_mul, hψ₁, hψw]
        exact le_iSup₂_of_le (z * w) (A.mul_mem hzA hwA) (le_iSup_of_le hzw le_rfl)

theorem compGen3Twin_small_of_gen₂ (𝓕 : Set (Subgroup G))
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hstruct : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)),
      R₁ ≠ R₂ → sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center G →
        Commutes R₁ R₂ ∧ sl2Inv e₁ ∉ Subgroup.center G ∧ sl2Inv e₂ ∉ Subgroup.center G)
    (hgen : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ (e₁ : R₁ ≃* SL(2, 𝔽₃)) (e₂ : R₂ ≃* SL(2, 𝔽₃)),
      R₁ ≠ R₂ → sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ Subgroup.center G →
        ∀ r₁ ∈ R₁, ∀ r₂ ∈ R₂, r₁ * r₁ = sl2Inv e₁ → r₂ * r₂ = sl2Inv e₂ →
          Subgroup.centralizer ({sl2Inv e₁} : Set G) ⊔
            Subgroup.centralizer ({r₁ * r₂} : Set G) = ⊤) :
    CompGen3Twin (⟨G, 𝓕⟩ : Q3.CompData) :=
  compGen3Twin_small_of_gen 𝓕 hsl2 hstruct fun R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc r₁ hr₁ r₂ hr₂ h₁ h₂ =>
    le_trans (le_of_eq (hgen R₁ hR₁ R₂ hR₂ e₁ e₂ hne hc r₁ hr₁ r₂ hr₂ h₁ h₂).symm) le_sup_left

end Assembly

end CFSG.ClassicalInvolution.ModelFacts.TG3
