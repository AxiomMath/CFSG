module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

section Conj

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_of_conj_gen (S : LangSetup τ L p) {K : Type} [Field K] [Finite K]
    [Algebra K L] {p₀ fK : ℕ} (hp₀ : p₀.Prime) (hf : 1 ≤ fK) (hK : Nat.card K = p₀ ^ fK)
    [ExpChar L p₀] (C : Subgroup (ModGL τ K)) (e : C ≃* S.Γ)
    (he : ∀ h : C, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    (Y0 Ycl : Set (ModGL τ L))
    (hnf : ∀ α : MulAut C, ∃ (y : ModGL τ K) (σ : K ≃+* K),
      baseChangeGL (algebraMap K L) y ∈ Y0 ∧ ∀ h : C,
        (α h : ModGL τ K) = y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹)
    (hreal : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      ∀ j : ℕ, j < fK → ∀ y : ModGL τ K, baseChangeGL (algebraMap K L) y ∈ Y0 →
      ∀ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
        Units.map (entrywiseHom (iterateFrobenius L p₀ j)) S.D.g0 →
      (∀ x ∈ rigidTestSet S D₁,
        z * Units.map (entrywiseHom (iterateFrobenius L p₀ j)) x * z⁻¹ = x) →
      ∃ w ∈ Ycl, ∀ x : S.Γ,
        z * Units.map (entrywiseHom (iterateFrobenius L p₀ j)) (x : ModGL τ L) * z⁻¹ =
          w * x * w⁻¹)
    (hI : ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      ∀ w ∈ Ycl, (∀ x ∈ rigidTestSet S D₁, Commute w x) → ∀ x : S.Γ, Commute w (x : ModGL τ L)) :
    SetupRigid S := by
  classical
  intro D₁ hD₁E hD₁c δ _ hfixD hfixX
  obtain ⟨y, σ, hyY, hy⟩ := hnf ((e.trans δ).trans e.symm)
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') S.D.g0 := ⟨_, rfl⟩
  have hδx : ∀ x : S.Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) =
        S.D.g0 * (e h : ModGL τ L) * S.D.g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  have hfix : ∀ x ∈ rigidTestSet S D₁, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁E hx
    have h1 : δ ⟨x, hxΓ⟩ = ⟨x, hxΓ⟩ := by
      rcases hx with hx | hx
      · exact hfixX ⟨x, hxΓ⟩ hx
      · exact hfixD ⟨x, hxΓ⟩ hx
    have h2 := hδx ⟨x, hxΓ⟩
    rw [h1] at h2
    exact h2.symm
  rw [hσ'] at hz hfix hδx
  obtain ⟨w, hwY, hw⟩ := hreal D₁ hD₁E hD₁c j hj y hyY z hz hfix
  have hwc : ∀ x ∈ rigidTestSet S D₁, Commute w x := by
    intro x hx
    have h1 := hfix x hx
    have h2 : ∀ x ∈ rigidTestSet S D₁, w * x * w⁻¹ = x := by
      intro x hx
      have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁E hx
      rw [← hw ⟨x, hxΓ⟩]
      exact hfix x hx
    show w * x = x * w
    calc w * (x : ModGL τ L) = w * x * w⁻¹ * w := by group
      _ = x * w := by rw [h2 x hx]
  have hwΓ := hI D₁ hD₁E hD₁c w hwY hwc
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hw x, MulAut.one_apply]
  have := (hwΓ x).eq
  calc w * (x : ModGL τ L) * w⁻¹ = x * w * w⁻¹ := by rw [this]
    _ = x := by group

end Conj

end CFSG.HardMathSupport.Timmesfeld.LangTorus
