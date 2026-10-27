module

public import CFSG.ClassicalInvolution.Phan.CoherentLeft
public import CFSG.ClassicalInvolution.Phan.PhanDn.MainA
public import CFSG.ClassicalInvolution.Phan.PhanDn.SimpleQn
public import CFSG.ClassicalInvolution.Phan.SuTwoSimple

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem exists_injective_phanD4_hom (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {G : Type} [Group G] (ι₁ ι₂ ι₃ : Su K 2 f 2 →* G) (θ₁₂ θ₁₃ θL : Su K 2 f 3 →* G)
    (h₁₂ : θ₁₂.comp (embSUid (unitaryInvolution K 2 f) 2) = ι₁ ∧
      θ₁₂.comp (embSUid (unitaryInvolution K 2 f) 0) = ι₂)
    (h₁₃ : θ₁₃.comp (embSUid (unitaryInvolution K 2 f) 2) = ι₁ ∧
      θ₁₃.comp (embSUid (unitaryInvolution K 2 f) 0) = ι₃)
    (h₂₃ : ∀ a b, ι₂ a * ι₃ b = ι₃ b * ι₂ a)
    (hL : θL.ker ≤ Subgroup.center (Su K 2 f 3))
    (h12 : θ₁₂.ker ≤ Subgroup.center (Su K 2 f 3))
    (hM : (B23 K 2 f).map θL = (B12 K 2 f).map θ₁₂)
    (hcomm : ∀ x ∈ (B12 K 2 f).map θL, ∀ y ∈ (B23 K 2 f).map θ₁₂, x * y = y * x)
    (h₀ : ∀ x ∈ (B12 K 2 f).map θL, ∀ b,
      x * ι₂ b = ι₂ b * x ∧ x * ι₃ b = ι₃ b * x)
    (hι₁ : Function.Injective ι₁) :
    ∃ φ : DΩ E 3 →* G, Function.Injective φ ∧
      φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2) = θ₁₂ ∧
      φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3) = θ₁₃ ∧
      φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 1) = ι₁ ∧
      φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 2) = ι₂ ∧
      φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 3) = ι₃ ∧
      (φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 0)).range = (B12 K 2 f).map θL ∧
      (φ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 0 1)).range = θL.range := by
  obtain ⟨θ01, -, hrange01, hB12eq, -, hcomp01⟩ :=
    exists_glue_left (X := G) (p := 2) (f := f) (θ₁ := θL) (θ₂ := θ₁₂) hK hL h12 hM hcomm
  have hmem : ∀ z : Su K 2 f 2,
      θ01 (embSUid (unitaryInvolution K 2 f) 2 z) ∈ (B12 K 2 f).map θL := by
    intro z
    rw [← hB12eq]
    exact Subgroup.mem_map_of_mem θ01
      (show embSUid (unitaryInvolution K 2 f) 2 z ∈ B12 K 2 f from ⟨z, rfl⟩)
  have hedge : ∀ i j : Fin 4, i < j → CFSG.StandardType.ggCoxeterMatrixD 4 i j = 3 →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by
    intro i j hij hM
    rw [CFSG.StandardType.ggCoxeterMatrixD_apply, CartanMatrix.D_four] at hM
    fin_cases i <;> fin_cases j <;>
      first
        | decide
        | exact absurd hM (by decide)
        | exact absurd hij (by decide)
  have hedge2 : ∀ i j : Fin 4, CFSG.StandardType.ggCoxeterMatrixD 4 i j = 2 →
      (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨
        (i = 3 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by
    intro i j hM
    rw [CFSG.StandardType.ggCoxeterMatrixD_apply, CartanMatrix.D_four] at hM
    fin_cases i <;> fin_cases j <;>
      first
        | decide
        | exact absurd hM (by decide)
  let Fam : PhanFamilyE K 2 f (CFSG.StandardType.ggCoxeterMatrixD 4) G :=
    { ι := ![θ01.comp (embSUid (unitaryInvolution K 2 f) 2), ι₁, ι₂, ι₃]
      θ := ![![1, θ01, 1, 1], ![1, 1, θ₁₂, θ₁₃], ![1, 1, 1, 1], ![1, 1, 1, 1]]
      left := by
        intro i j hij hMij
        rcases hedge i j hij hMij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact h₁₂.1
        · exact h₁₃.1
      right := by
        intro i j hij hMij
        rcases hedge i j hij hMij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcomp01.trans h₁₂.1
        · exact h₁₂.2
        · exact h₁₃.2
      comm := by
        intro i j hMij a b
        rcases hedge2 i j hMij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (h₀ _ (hmem a) b).1
        · exact (h₀ _ (hmem a) b).2
        · exact ((h₀ _ (hmem b) a).1).symm
        · exact h₂₃ a b
        · exact ((h₀ _ (hmem b) a).2).symm
        · exact (h₂₃ b a).symm }
  have hU : (stdFamilyΩ E 3 le_rfl hK hq).IsUniversal :=
    isUniversal_stdFamilyΩ_of_dChamberSystem (E := E) (m := 3) le_rfl hK hq
      (stdFamilyΩ_good E 3 le_rfl hK hq)
      (dChamberSystemConnected_holds K f hK hq 3 le_rfl)
      (dChamberSystemSimplyTwoConnected_holds K f hK hq 3 le_rfl)
  obtain ⟨ψ, hψι, hψθ⟩ := hU G Fam
  have hψ12 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 2) = θ₁₂ :=
    hψθ 1 2 (by decide) (by decide)
  have hψ13 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 1 3) = θ₁₃ :=
    hψθ 1 3 (by decide) (by decide)
  have hψι0 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 0) =
      θ01.comp (embSUid (unitaryInvolution K 2 f) 2) := hψι 0
  have hψι1 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 1) = ι₁ := hψι 1
  have hψι2 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 2) = ι₂ := hψι 2
  have hψι3 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 3) = ι₃ := hψι 3
  have hψ01 : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).θ 0 1) = θ01 :=
    hψθ 0 1 (by decide) (by decide)
  have hinj : Function.Injective ψ := by
    haveI : IsSimpleGroup (DΩ E 3) :=
      isSimpleGroup_orthDerived_Qn E (n := 4) (by decide) le_rfl
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff ψ).mp hbot
    · exfalso
      have htriv : ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 1) = 1 := by
        ext a
        have ha : (stdFamilyΩ E 3 le_rfl hK hq).ι 1 a ∈ ψ.ker := by
          rw [htop]
          exact Subgroup.mem_top _
        simpa [MonoidHom.mem_ker] using ha
      have hι1one : ι₁ = 1 := by
        rw [← hψι1]
        exact htriv
      haveI := isSimpleGroup_Su_two hK hq
      obtain ⟨a, ha⟩ := exists_ne (1 : Su K 2 f 2)
      exact ha (hι₁ (by rw [hι1one]; simp))
  refine ⟨ψ, hinj, hψ12, hψ13, hψι1, hψι2, hψι3, ?_, ?_⟩
  · calc (ψ.comp ((stdFamilyΩ E 3 le_rfl hK hq).ι 0)).range
        = (θ01.comp (embSUid (unitaryInvolution K 2 f) 2)).range := by rw [hψι0]
      _ = (embSUid (unitaryInvolution K 2 f) 2).range.map θ01 :=
          MonoidHom.range_comp θ01 (embSUid (unitaryInvolution K 2 f) 2)
      _ = (B12 K 2 f).map θ01 := rfl
      _ = (B12 K 2 f).map θL := hB12eq
  · rw [hψ01]
    exact hrange01

end CFSG.ClassicalInvolution.PhanDn

end
