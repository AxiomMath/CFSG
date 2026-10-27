module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviKernel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviRead

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Module LinearMap CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

@[expose] noncomputable def chartOfSurjective {X : Type*} [Group X] {r : ℕ}
    (ρ : X →* StatedSp r K) (hρ : Function.Surjective ρ) :
    X ⧸ ρ.ker ≃* StatedProj (StatedSp r K) :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).trans (spProjEquivCharTwo K r).symm

theorem ker_props_of_surjective_sp (hq4 : 4 ≤ Nat.card K) {X : Type*} [Group X] [Finite X]
    {r : ℕ} (hr : 1 ≤ r) (ρ : X →* StatedSp r K) (hρ : Function.Surjective ρ) :
    (∀ M : Subgroup X, M.Normal → ρ.ker ≤ M → M = ρ.ker ∨ M = ⊤) ∧
      ∀ M : Subgroup X, M.Normal → IsPGroup 2 M → M ≤ ρ.ker := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  have : IsSimpleGroup (X ⧸ ρ.ker) := MulEquiv.isSimpleGroup (chartOfSurjective ρ hρ)
  have hnc : ∃ a b : X ⧸ ρ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_statedProj_statedSp hq4 hr
    refine ⟨(chartOfSurjective ρ hρ).symm a, (chartOfSurjective ρ hρ).symm b, fun h => hab ?_⟩
    have h' := congrArg (chartOfSurjective ρ hρ) h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  refine ⟨fun M hM hle => eq_or_eq_top_of_simple_quotient M hM hle, fun M hM hMp => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_of_isPGroup_of_simple hnc hMp

section TypeA

theorem spLeviData_of_rangeChart (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N
      hXN).ker)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K (range N)
      (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal →
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker ≤ M →
        M = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker ∨ M = ⊤)
    (hab₂ : (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker = ⊤ ∨
      ∃ a b : ↥X ⧸ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker,
        a * b ≠ b * a)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn) X
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker)
    (h₂ : IsEmpty (↥X ⧸ (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N
      hXN).ker ≃* StatedProj (StatedSp r K)))
    (hU : ∀ v, v ∈ range N ↔ ∀ x ∈ ρ.ker ⊓
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker,
        projLift (exists_coordinateQuadPlus_ne_zero (by omega))
          (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v) :
    SpLeviData (plusFieldPart hf hK hn) X := by
  set hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega) with hQdef
  set N₂ := (kerQuotHom hQ X N hXN).ker with hN₂
  obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂) := by
    rw [hρker]
    exact isPGroup_ker_inf_ker hQ X N hXN
  have hR : IsPGroup 2 ↥(ρ.ker ⊓ N₂ ⊓ ⊤) := by rwa [inf_top_eq]
  have hRn : (ρ.ker ⊓ N₂ ⊓ ⊤).Normal := by
    rw [inf_top_eq]
    infer_instance
  have hN : ∀ N' ∈ ({ρ.ker, N₂, ⊤} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N' := by
    intro N' hN' M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hle₁ M hM hMp
    · exact le_of_isPGroup_of_eq_or_top hq₂ hab₂ M hM hMp
    · exact le_top
  have hU' : ∀ v, v ∈ range N ↔ ∀ x ∈ ρ.ker ⊓ N₂ ⊓ ⊤,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v := by
    intro v
    rw [hU v, inf_top_eq]
  have hXU : ∀ x ∈ X, ∀ u ∈ range N, projLift hQ x u ∈ range N := fun x hx =>
    mem_range_of_commute (hXN x hx)
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn) X ρ.ker :=
    spLeviSection_of_trace_restrict hQ _ (fun g => orthAutFieldPart_kappa _ _ g)
      (exists_kappa_eq_plus hn) (range N) hXU
      (fun g hgX => mapsTo_of_fixedSpace_eq hQ ρ.ker N₂ ⊤ hN hR hRn (range N) hU' g hgX) hr ρ hρ
      htr
  exact spLeviData_two_of_isEmpty_mulEquiv _ hq4 ρ.ker N₂ h12 hq₁ hq₂ hs₁ hs₂ hr
    (chartOfSurjective ρ hρ) h₂

end TypeA

section TypeBC

theorem spLeviData_of_kerQuotChart (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hNN : ∀ v, N (N v) = 0)
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (N₂ : Subgroup ↥X) [N₂.Normal] (h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn) X N₂)
    (h₂ : IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K))) :
    SpLeviData (plusFieldPart hf hK hn) X := by
  obtain ⟨hq₁, -⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn) X ρ.ker :=
    spLeviSection_of_kerQuot_plus hf hK hn hr N hNN hXN ρ hρ htr
  exact spLeviData_two_of_isEmpty_mulEquiv _ hq4 ρ.ker N₂ h12 hq₁ hq₂ hs₁ hs₂ hr
    (chartOfSurjective ρ hρ) h₂

end TypeBC

end CFSG.SeitzReduction.OmegaPilot
