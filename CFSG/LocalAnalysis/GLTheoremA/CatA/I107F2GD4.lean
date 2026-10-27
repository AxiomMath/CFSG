module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2GNot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Assembly CFSG.StandardType CFSG.StandardType.RecipeFieldOmega
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace OR107

theorem card_le_of_triality {A G : Type*} [Group A] [Group G] [IsCyclic G]
    {Inn : Subgroup A} [Inn.Normal] {θ ρ : A} (φ : G →* A)
    (hθ3 : θ ^ 3 = 1) (hρρ : ρ * ρ = 1) (hρθ : ρ * θ * ρ = θ⁻¹)
    (hφθ : ∀ σ, θ * φ σ = φ σ * θ) (hρφ : ∀ σ, ρ * φ σ = φ σ * ρ)
    (hgen : ∀ α : A, ∃ ι ∈ Inn, ∃ k : ℕ, ∃ σ : G,
      α = ι * (θ ^ k * φ σ) ∨ α = ι * (θ ^ k * (ρ * φ σ)))
    (huniq : ∀ (k : ℕ) (σ : G), θ ^ k * (ρ * φ σ) ∈ Inn → ρ * φ σ = 1)
    {E : Subgroup A} (hE : ∀ e ∈ E, e ^ 3 = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ Inn) * 3 ^ ((if 3 ∣ Nat.card G then 1 else 0) + 1) := by
  have hform : ∀ e : A, e ^ 3 = 1 → ∃ ι ∈ Inn, ∃ k : ℕ, ∃ σ : G, e = ι * (θ ^ k * φ σ) := by
    intro e he
    obtain ⟨ι, hι, k, σ, h | h⟩ := hgen e
    · exact ⟨ι, hι, k, σ, h⟩
    · subst h
      have h3 := FP.pow_mem_of_mul_pow_eq_one (N := Inn) hι he
      rw [triality_cube k hρρ hρθ (hφθ σ) (hρφ σ), ← map_pow φ σ 3] at h3
      have hρ : ρ = φ ((σ ^ 3)⁻¹) := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_left (huniq k (σ ^ 3) h3)
      exact ⟨ι, hι, k, (σ ^ 3)⁻¹ * σ, by rw [hρ, map_mul]⟩
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
  have hθc : ∀ α : A, ((α * θ * α⁻¹ : A) : A ⧸ Inn) = (θ : A ⧸ Inn) ∨
      ((α * θ * α⁻¹ : A) : A ⧸ Inn) = ((θ⁻¹ : A) : A ⧸ Inn) := by
    intro α
    obtain ⟨ι, hι, k, σ, rfl | rfl⟩ := hgen α
    · left
      have hc : Commute (θ ^ k * φ σ) θ :=
        (Commute.pow_self θ k).mul_left (show Commute θ (φ σ) from hφθ σ).symm
      have e1 : ι * (θ ^ k * φ σ) * θ * (ι * (θ ^ k * φ σ))⁻¹ =
          ι * ((θ ^ k * φ σ) * θ * (θ ^ k * φ σ)⁻¹) * ι⁻¹ := by group
      rw [e1, hc.mul_inv_cancel, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv Inn ι,
        (QuotientGroup.eq_one_iff ι).2 hι, one_mul, inv_one, mul_one]
    · right
      have hφ : φ σ * θ * (φ σ)⁻¹ = θ := (show Commute θ (φ σ) from hφθ σ).symm.mul_inv_cancel
      have hρ' : ρ * θ * ρ⁻¹ = θ⁻¹ := by rw [hρinv, hρθ]
      have e1 : ι * (θ ^ k * (ρ * φ σ)) * θ * (ι * (θ ^ k * (ρ * φ σ)))⁻¹ =
          ι * (θ ^ k * (ρ * (φ σ * θ * (φ σ)⁻¹) * ρ⁻¹) * (θ ^ k)⁻¹) * ι⁻¹ := by group
      have e2 : θ ^ k * θ⁻¹ * (θ ^ k)⁻¹ = θ⁻¹ := by group
      rw [e1, hφ, hρ', e2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv Inn ι,
        (QuotientGroup.eq_one_iff ι).2 hι, one_mul, inv_one, mul_one]
  haveI hNq : (Subgroup.zpowers (θ : A ⧸ Inn)).Normal := by
    constructor
    intro n hn y
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    induction y using QuotientGroup.induction_on with
    | H α =>
      rw [← conj_zpow]
      apply Subgroup.zpow_mem
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rcases hθc α with h | h
      · rw [h]
        exact Subgroup.mem_zpowers _
      · rw [h, QuotientGroup.mk_inv]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup A,
      N = (Subgroup.zpowers (θ : A ⧸ Inn)).comap (QuotientGroup.mk' Inn) := ⟨_, rfl⟩
  haveI hN : N.Normal := by
    rw [hNdef]
    exact hNq.comap _
  have hInnN : Inn ≤ N := fun x hx => by
    rw [hNdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hθN : θ ∈ N := by
    rw [hNdef]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  have hc : Nat.card ↥(E ⊓ N) ≤ Nat.card ↥(E ⊓ Inn) * 3 := by
    have h := card_le_card_inf_mul_of_le_comap Nat.prime_three (J := Inn) (g := θ) (E := E ⊓ N)
      (hNdef ▸ inf_le_right) (fun e he => hE e (Subgroup.mem_inf.mp he).1)
    rwa [inf_assoc, inf_eq_right.mpr hInnN] at h
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := G)
  have hb : Nat.card E ≤ Nat.card ↥(E ⊓ N) * 3 ^ (if 3 ∣ Nat.card G then 1 else 0) := by
    split_ifs with h3
    · rw [pow_one]
      refine card_le_card_inf_mul_of_le_comap Nat.prime_three (g := φ σ₀) ?_ hE
      intro e he
      obtain ⟨ι, hι, k, σ, rfl⟩ := hform e (hE e he)
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀ σ)
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff ι).2 (hInnN hι), (QuotientGroup.eq_one_iff _).2 (N.pow_mem hθN k),
        one_mul, one_mul, map_zpow, QuotientGroup.mk_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m
    · rw [pow_zero, mul_one]
      have hEN : E ≤ N := by
        intro e he
        obtain ⟨ι, hι, k, σ, rfl⟩ := hform e (hE e he)
        have he3 := hE _ he
        rw [← mul_assoc] at he3 ⊢
        refine mul_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
          (N.mul_mem (hInnN hι) (N.pow_mem hθN k)) ?_ he3
        rw [← map_pow, pow_card_eq_one', map_one]
      rw [inf_eq_left.mpr hEN]
  calc Nat.card E ≤ Nat.card ↥(E ⊓ N) * 3 ^ (if 3 ∣ Nat.card G then 1 else 0) := hb
    _ ≤ Nat.card ↥(E ⊓ Inn) * 3 * 3 ^ (if 3 ∣ Nat.card G then 1 else 0) :=
        Nat.mul_le_mul_right _ hc
    _ = Nat.card ↥(E ⊓ Inn) * 3 ^ ((if 3 ∣ Nat.card G then 1 else 0) + 1) := by ring

end OR107

section OmegaPlusFour

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_le_omegaPlusFour {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (E : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K)))) (hE : ∀ e ∈ E, e ^ 3 = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ inner (matrixDerived (coordinateQuadPlus 4 K))) *
      3 ^ ((if 3 ∣ n then 1 else 0) + 1) := by
  have h14 : 1 ≤ 4 := by norm_num
  obtain ⟨θ, hθ3, hρθ, hφθ, hgen, huniq, -⟩ := plusFourTrialityInput_holds K
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  haveI : (inner (matrixDerived (coordinateQuadPlus 4 K))).Normal := inner_normal _
  have h := OR107.card_le_of_triality (Inn := inner _) (AutOm.fieldAutP 4) hθ3
    (AutOm.plusRefl_mul_self h14) hρθ hφθ (AutOm.plusRefl_mul_fieldAutP h14) ?_ ?_ hE
  · rwa [FP.natCard_ringEquiv_of_card hK] at h
  · intro α
    obtain ⟨ι, hι, k, c, hc, rfl⟩ := hgen α
    obtain ⟨σ, rfl | rfl⟩ := hc
    · exact ⟨ι, hι, k, σ, Or.inl rfl⟩
    · exact ⟨ι, hι, k, σ, Or.inr rfl⟩
  · intro k σ h
    exact (huniq k _ ⟨σ, Or.inr rfl⟩ h).2

theorem outRankP_omegaPlusFour {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    OutRankP ⟨LargeEvenLieTag.D, 4, n⟩ 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
      (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro _ _ E hE
  have h14 : 1 ≤ 4 := by norm_num
  let χ := MulAut.congr (plusEquiv (K := K) h14)
  let E' := E.map χ.toMonoidHom
  have hE' : ∀ e ∈ E', e ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE.2 e he, map_one]
  have hL : ∀ y, y ∈ Subgroup.closure (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega
      (LargeEvenQPlus K 4))) ∪ Set.range (MulAut.conj : _ →* MulAut (LargeEvenProj (LargeEvenOmega
      (LargeEvenQPlus K 4))))) ↔ χ y ∈ inner (matrixDerived (coordinateQuadPlus 4 K)) := by
    intro y
    constructor
    · intro hy
      have hle : Subgroup.closure (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega
          (LargeEvenQPlus K 4))) ∪ Set.range (MulAut.conj : _ →* MulAut (LargeEvenProj
          (LargeEvenOmega (LargeEvenQPlus K 4))))) ≤
          (inner (matrixDerived (coordinateQuadPlus 4 K))).comap χ.toMonoidHom := by
        rw [Subgroup.closure_le]
        rintro z (hz | hz)
        · exact Subgroup.mem_comap.mpr ((mem_innSet_iff_congr _ z).1 hz)
        · exact Subgroup.mem_comap.mpr ((mem_innSet_iff_congr _ z).1 hz)
      exact Subgroup.mem_comap.mp (hle hy)
    · intro hy
      exact Subgroup.subset_closure (Or.inl ((mem_innSet_iff_congr _ y).2 hy))
  have hmap : (E ⊓ Subgroup.closure (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega
      (LargeEvenQPlus K 4))) ∪ Set.range (MulAut.conj : _ →* MulAut (LargeEvenProj (LargeEvenOmega
      (LargeEvenQPlus K 4)))))).map χ.toMonoidHom =
      E' ⊓ inner (matrixDerived (coordinateQuadPlus 4 K)) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, ⟨hyE, hyL⟩, rfl⟩
      exact ⟨⟨y, hyE, rfl⟩, (hL y).1 hyL⟩
    · rintro ⟨⟨y, hyE, rfl⟩, hx⟩
      exact ⟨y, ⟨hyE, (hL y).2 hx⟩, rfl⟩
  have h := card_le_omegaPlusFour hK E' hE'
  rw [← hmap, Subgroup.card_map_of_injective χ.injective,
    Subgroup.card_map_of_injective χ.injective] at h
  have hbonus : outBonus107 ⟨LargeEvenLieTag.D, 4, n⟩ 3 = (if 3 ∣ n then 1 else 0) + 1 := by
    simp [outBonus107]
  rw [hbonus]
  exact h

end OmegaPlusFour

theorem outRankP_D4 {n : ℕ} :
    Rk2LabelAll ⟨LargeEvenLieTag.D, 4, n⟩ (OutRankP ⟨LargeEvenLieTag.D, 4, n⟩ 3) := by
  intro Q h
  have h4 : ¬ ((4 : ℕ) = 3) := by norm_num
  simp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, if_neg h4] at h ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  exact ⟨K, hF, hfin, hK, hQ, outRankP_omegaPlusFour hK⟩

theorem outRankP_holds
    {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Rk2LabelAll lab (OutRankP lab p) := by
  by_cases hD : lab.tag = LargeEvenLieTag.D ∧ lab.rank = 4 ∧ p = 3
  · obtain ⟨ht, hr, rfl⟩ := hD
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hr
    subst ht
    subst hr
    exact outRankP_D4
  · exact outRankP_of_notD4 hlab hp hp2 hD

theorem outRank107_holds :
    OutRank107 :=
  fun _ hlab _ hp hp2 => outRankP_holds hlab hp hp2

end CFSG.LocalAnalysis.GLTheoremA
