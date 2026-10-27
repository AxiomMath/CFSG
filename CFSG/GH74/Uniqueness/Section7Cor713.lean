module

public import CFSG.GH74.Uniqueness.Section7Cor713Solv
public import CFSG.GH74.Uniqueness.Section7Cor713Bender
public import CFSG.GH74.Uniqueness.Section7Cor713Data

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor713_nonsolvable
    (S : ZDSetup X Z M) (hT4b : Theorem4bStmt Z M) {F : Subgroup X}
    (hF : F ≠ ⊤) (hFM : ¬ F ≤ M) (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hns : ¬ Group.IsSolvable ↥(zHull Z F)) :
    (pPrimeCoreIn (zHull Z F) = (center ↥(zHull Z F)).map (zHull Z F).subtype ∧
        CFSG.BenderSuzuki.IsBenderGroup (↥(zHull Z F) ⧸ center ↥(zHull Z F)) ∧
        (∀ β₁ ∈ alphaOrbit M F, ∀ γ₁ ∈ alphaOrbit M F, β₁ ≠ γ₁ →
          ∀ β₂ ∈ alphaOrbit M F, ∀ γ₂ ∈ alphaOrbit M F, β₂ ≠ γ₂ →
            ∃ g ∈ zHull Z F, conjugate β₁ g = β₂ ∧ conjugate γ₁ g = γ₂) ∧
        ∀ β ∈ alphaOrbit M F, β ≠ M →
          (F : Set X) = (zHull Z F : Set X) * ((F ⊓ M ⊓ β : Subgroup X) : Set X)) ∧
      (∃ T : Sylow 2 (↥(zHull Z F) ⧸ center ↥(zHull Z F)),
        (M.comap (zHull Z F).subtype).map (QuotientGroup.mk' (center ↥(zHull Z F))) =
          normalizer ((T : Subgroup (↥(zHull Z F) ⧸ center ↥(zHull Z F))) :
            Set (↥(zHull Z F) ⧸ center ↥(zHull Z F)))) ∧
      (∀ y ∈ zHull Z F, orderOf y = 2 → y ∈ Z) ∧
      ∃ n : ℕ, 2 ≤ n ∧ (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).ncard = 2 ^ n - 1 := by
  obtain ⟨K, instK, ψ, T₀, hψ, hker, hK, hY, hcent, hinvZ⟩ :=
    S.cor713_exists_bender_quotient hT4b hF hFM hne hns
  have : Finite K := Finite.of_surjective ψ hψ
  obtain ⟨h2t, n, hn2, hcard⟩ := Cor713.bender_twoTransitive_and_card hK T₀
  have hcen : pPrimeCore 2 ↥(zHull Z F) = center ↥(zHull Z F) := by
    apply le_antisymm
    · intro o ho
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hcent o ho g).symm
    · intro c hc
      have hψc : ψ c ∈ center K := by
        rw [Subgroup.mem_center_iff]
        intro k
        obtain ⟨g, rfl⟩ := hψ k
        calc ψ g * ψ c = ψ (g * c) := (map_mul ψ g c).symm
          _ = ψ (c * g) := by rw [Subgroup.mem_center_iff.mp hc g]
          _ = ψ c * ψ g := map_mul ψ c g
      rw [center_eq_bot_of_isBenderGroup hK, Subgroup.mem_bot] at hψc
      rw [← hker]
      exact hψc
  have hkerc : ψ.ker = center ↥(zHull Z F) := hker.trans hcen
  have h2tr := S.cor713_twoTransitive_alphaOrbit hFM hne ψ hψ hY h2t
  have hY' : ∀ g : ↥(zHull Z F), ψ g ∈ normalizer ((T₀ : Subgroup K) : Set K) ↔
      g ∈ M.comap (zHull Z F).subtype := fun g => hY g
  refine ⟨⟨?_, ?_, h2tr, fun β hβ hβM => S.cor713_eq_mul_of_twoTransitive h2tr hβ hβM⟩, ?_, hinvZ,
    n, hn2, ?_⟩
  · rw [pPrimeCoreIn, hcen]
  · let e : ↥(zHull Z F) ⧸ center ↥(zHull Z F) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hkerc.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact isBenderGroup_of_mulEquiv e hK
  · exact Cor713.borel_witness ψ hψ hkerc hY'
  · have hset : Z ∩ ((F ⊓ M : Subgroup X) : Set X) = (Subtype.val : ↥(zHull Z F) → X) ''
        {y : ↥(zHull Z F) | y ∈ M.comap (zHull Z F).subtype ∧ orderOf y = 2} := by
      ext y
      constructor
      · rintro ⟨hyZ, hyFM⟩
        have hyF : y ∈ F := (Subgroup.mem_inf.mp hyFM).1
        have hyM : y ∈ M := (Subgroup.mem_inf.mp hyFM).2
        refine ⟨⟨y, Cor713.mem_zHull_of_mem hyZ hyF⟩, ⟨hyM, ?_⟩, rfl⟩
        rw [Subgroup.orderOf_mk]
        exact S.invariant.1 y hyZ
      · rintro ⟨g, ⟨hgM, hg2⟩, rfl⟩
        have hg2' : orderOf (g : X) = 2 := by rwa [Subgroup.orderOf_coe]
        exact ⟨hinvZ (g : X) g.2 hg2',
          Subgroup.mem_inf.mpr ⟨Cor713.zHull_le F g.2, hgM⟩⟩
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective,
      Cor713.ncard_involutions_eq ψ hψ hker (odd_card_pPrimeCore ↥(zHull Z F)) hcent hY', hcard]

theorem ZDSetup.cor713
    (S : ZDSetup X Z M) (hT4 : Theorem4Stmt Z M) : Cor713Stmt Z M := by
  intro F hF hFM hne
  refine ⟨S.not_zHull_le hFM hne, ?_⟩
  by_cases hsolv : Group.IsSolvable ↥(zHull Z F)
  · exact Or.inl ⟨hsolv, S.cor713_solvable hT4.2 hF hFM hne hsolv⟩
  · exact Or.inr (S.cor713_nonsolvable hT4.2 hF hFM hne hsolv).1

theorem ZDSetup.cor713Extra
    (S : ZDSetup X Z M) (hT4 : Theorem4Stmt Z M) : Cor713Extra Z M := by
  intro F hF hFM hne hns
  exact (S.cor713_nonsolvable hT4.2 hF hFM hne hns).2

end CFSG.GH74.Uniqueness
