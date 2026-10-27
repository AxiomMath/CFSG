module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.RecipeFieldOmega
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Abstract

variable {M : Type*} [Group M]

theorem triality_pow_mem {N : Subgroup M} [N.Normal] {θ ρ ι c : M} {k : ℕ} (hρρ : ρ * ρ = 1)
    (hρθ : ρ * θ * ρ = θ⁻¹) (hθ3 : θ ^ 3 = 1) (hρc : ρ * c = c * ρ) (hι : ι ∈ N)
    (hcomm : ρ * (ι * (θ ^ k * c)) * ρ⁻¹ * (ι * (θ ^ k * c))⁻¹ ∈ N) : θ ^ k ∈ N := by
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
  have h1 : ρ * θ ^ k * ρ⁻¹ = (θ ^ k)⁻¹ := by
    have : ρ * θ ^ k * ρ⁻¹ = (ρ * θ * ρ⁻¹) ^ k := (conj_pow ..).symm
    rw [this, hρinv, hρθ, inv_pow]
  have h2 : ρ * c * ρ⁻¹ = c := by
    rw [hρinv, hρc, mul_assoc, hρρ, mul_one]
  have e : ρ * (ι * (θ ^ k * c)) * ρ⁻¹ * (ι * (θ ^ k * c))⁻¹ =
      (ρ * ι * ρ⁻¹) * ((θ ^ k)⁻¹ * (θ ^ k)⁻¹) * ι⁻¹ := by
    calc ρ * (ι * (θ ^ k * c)) * ρ⁻¹ * (ι * (θ ^ k * c))⁻¹
        = (ρ * ι * ρ⁻¹) * (ρ * θ ^ k * ρ⁻¹) * (ρ * c * ρ⁻¹) * (c⁻¹ * (θ ^ k)⁻¹ * ι⁻¹) := by group
      _ = _ := by rw [h1, h2]; group
  rw [e] at hcomm
  have hρι : ρ * ι * ρ⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance ι hι ρ
  have hT : (θ ^ k)⁻¹ * (θ ^ k)⁻¹ ∈ N := by
    have := N.mul_mem (N.mul_mem (N.inv_mem hρι) hcomm) hι
    simpa [mul_assoc] using this
  have hT' : (θ ^ k)⁻¹ * (θ ^ k)⁻¹ = θ ^ k := by
    have hinv : (θ ^ (2 * k))⁻¹ = θ ^ k := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, hθ3, one_pow]
    rw [← mul_inv_rev, ← pow_add, ← two_mul, hinv]
  rwa [hT'] at hT

theorem pow_mem_of_mul_pow_eq_one {N : Subgroup M} [N.Normal] {ι x : M} {m : ℕ} (hι : ι ∈ N)
    (h : (ι * x) ^ m = 1) : x ^ m ∈ N := by
  have h1 : (QuotientGroup.mk (ι * x) : M ⧸ N) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ι).2 hι, one_mul]
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← h1, ← QuotientGroup.mk_pow, h]
  rfl

end Abstract

@[expose] def CentralMod {R : Type} [Group R] (I : Set (MulAut R)) (α : MulAut R) : Prop :=
  ∀ γ : MulAut R, γ * α * γ⁻¹ * α⁻¹ ∈ I

@[expose] def OddAutCentral (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ α : MulAut R, α ^ p = 1 → CentralMod I α → ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, α = u * f

theorem centralMod_innSet_congr {R Γ : Type} [Group R] [Group Γ] (E : R ≃* Γ) {α : MulAut R}
    (h : CentralMod (LargeEvenInnSet R) α) (γ : MulAut Γ) :
    γ * MulAut.congr E α * γ⁻¹ * (MulAut.congr E α)⁻¹ ∈ inner Γ := by
  have := (mem_innSet_iff_congr E _).1 (h (MulAut.congr E.symm γ))
  have e : MulAut.congr E (MulAut.congr E.symm γ) = γ := by ext x; simp [MulAut.congr_apply]
  simpa only [map_mul, map_inv, e] using this

theorem congr_congr_symm' {R Γ : Type} [Group R] [Group Γ] (E : R ≃* Γ) (γ : MulAut Γ) :
    MulAut.congr E (MulAut.congr E.symm γ) = γ := by
  ext x; simp [MulAut.congr_apply]

theorem exists_inn_mul_of_congr {R Γ : Type} [Group R] [Group Γ] (E : R ≃* Γ) {α : MulAut R}
    {ι f' : MulAut Γ} (F : Set (MulAut R)) (hι : ι ∈ inner Γ)
    (hf : ∃ f ∈ F, MulAut.congr E f = f') (h : MulAut.congr E α = ι * f') :
    ∃ u ∈ LargeEvenInnSet R, ∃ f ∈ Subgroup.closure F, α = u * f := by
  obtain ⟨f, hf, rfl⟩ := hf
  refine ⟨MulAut.congr E.symm ι, ?_, f, Subgroup.subset_closure hf, ?_⟩
  · rw [mem_innSet_iff_congr E, congr_congr_symm']
    exact hι
  · apply (MulAut.congr E).injective
    rw [map_mul, congr_congr_symm', h]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem oddAutCentral_omegaPlusFour (hT : PlusFourTrialityInput) :
    OddAutCentral 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro hs hna α hα hcent
  have h14 : 1 ≤ 4 := by norm_num
  obtain ⟨θ, hθ3, hρθ, hφθ, hgen, huniq, -⟩ := hT K
  have hρρ := AutOm.plusRefl_mul_self (K := K) h14
  obtain ⟨ι, hι, k, c, hc0, hαι⟩ := hgen (MulAut.congr (plusEquiv h14) α)
  have hc : c ∈ AutOm.plusCompl h14 := hc0
  have hNn : (inner (matrixDerived (coordinateQuadPlus 4 K))).Normal := inner_normal _
  have hcomm := centralMod_innSet_congr (plusEquiv h14) hcent (AutOm.plusRefl h14)
  rw [hαι] at hcomm
  have hρc := (commute_plusRefl_of_mem_plusCompl h14 hc).eq
  have hθk : θ ^ k = 1 :=
    ((huniq k 1 (one_mem _) (by simpa using triality_pow_mem (N := inner _) hρρ hρθ hθ3 hρc hι hcomm))).1
  have hmain : ∃ τ : K ≃+* K, MulAut.congr (plusEquiv h14) α = ι * AutOm.fieldAutP 4 τ := by
    have hα3 : (MulAut.congr (plusEquiv h14) α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
    rw [hαι, hθk, one_mul] at hα3 ⊢
    obtain ⟨σ, rfl | rfl⟩ := hc
    · exact ⟨σ, rfl⟩
    ·
      have h3 := hα3
      have hx3 := pow_mem_of_mul_pow_eq_one (N := inner _) hι h3
      have hcom' : Commute (AutOm.plusRefl (K := K) h14) (AutOm.fieldAutP 4 σ) :=
        AutOm.plusRefl_mul_fieldAutP h14 σ
      have e3 : (AutOm.plusRefl h14 * AutOm.fieldAutP 4 σ) ^ 3 =
          AutOm.plusRefl h14 * AutOm.fieldAutP 4 (σ ^ 3) := by
        rw [hcom'.mul_pow, map_pow]
        have : AutOm.plusRefl (K := K) h14 ^ 3 = AutOm.plusRefl h14 := by
          rw [pow_succ, pow_two, hρρ, one_mul]
        rw [this]
      rw [e3] at hx3
      have hmem : AutOm.plusRefl h14 * AutOm.fieldAutP 4 (σ ^ 3) ∈ AutOm.plusCompl h14 :=
        ⟨σ ^ 3, Or.inr rfl⟩
      have h1 := (huniq 0 _ hmem (by simpa using hx3)).2
      refine ⟨(σ ^ 3)⁻¹ * σ, ?_⟩
      have hρ' : AutOm.plusRefl h14 = (AutOm.fieldAutP 4 (σ ^ 3))⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [hρ', map_mul, map_inv]
  obtain ⟨τ, hτ⟩ := hmain
  exact exists_inn_mul_of_congr (plusEquiv h14) _ hι
    (exists_mem_field_congr_plusEquiv (K := K) h14 τ) hτ

section Canon


theorem canonOddAutCentral {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (OddAutCentral p) := by
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨ht, hr, rfl⟩ := hD
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hr
    subst ht
    subst hr
    intro Q h
    have h4 : ¬ ((4 : ℕ) = 3) := by norm_num
    simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h4] at h ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := h
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hF, hfin, hK, hQ, oddAutCentral_omegaPlusFour plusFourTrialityInput_holds⟩
  · refine (canonOddAut hp hp2 hlab hD).mono ?_
    intro R _ I F h hs hna α hα _
    exact h hs hna α hα

end Canon

end FP

end CFSG.LocalAnalysis.GLTheoremA
