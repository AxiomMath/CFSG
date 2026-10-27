module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore perfectCore_eq_self_of_perfect)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open scoped commutatorElement

section Commutant

variable {K : Type} [Field K] {d : ℕ} (N : (Fin d → K) →ₗ[K] (Fin d → K))

@[expose] def nilCommutant : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) where
  carrier := {g | ∀ x, g (N x) = N (g x)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    change g (h (N x)) = N (g (h x))
    rw [hh, hg]
  inv_mem' := by
    intro g hg x
    have h1 := hg (g⁻¹ x)
    have h2 : g (g⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have h3 : g⁻¹ (g (N (g⁻¹ x))) = N (g⁻¹ x) := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [h2] at h1
    rw [← h3, h1]

theorem mem_nilCommutant {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} : g ∈ nilCommutant N ↔ ∀ x, g (N x) = N (g x) :=
  Iff.rfl

@[expose] noncomputable def kerQuotHomLin :
    ↥(nilCommutant N) →* Module.End K (LinearMap.ker N ⧸ rangeInKer N) where
  toFun g := kerQuotMap N ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) fun x => (mem_nilCommutant N).mp g.2 x
  map_one' := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, kerQuotMap_mk']
    rfl
  map_mul' g h := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply,
      kerQuotMap_mk', kerQuotMap_mk', kerQuotMap_mk']
    rfl

theorem kerQuotHomLin_mk (g : ↥(nilCommutant N)) (z : LinearMap.ker N) :
    kerQuotHomLin N g (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(g : (Fin d → K) ≃ₗ[K] (Fin d → K)) z,
        mem_ker_of_commute (g := ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)))
          (fun x => (mem_nilCommutant N).mp g.2 x) z z.2⟩ :=
  kerQuotMap_mk' N _ (fun x => (mem_nilCommutant N).mp g.2 x) z

end Commutant

section Core

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Field K] in
theorem finite_linearEquiv_pi {K : Type} [Field K] [Finite K] {d : ℕ} :
    Finite ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  Finite.of_injective (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => (e : (Fin d → K) → (Fin d → K)))
    DFunLike.coe_injective

theorem kerQuotForm_kerQuotHomLin (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (g : ↥(nilCommutant N))
    (hg : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (p q : LinearMap.ker N ⧸ rangeInKer N) :
    kerQuotForm N hadj (kerQuotHomLin N g p) (kerQuotHomLin N g q) = kerQuotForm N hadj p q := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [kerQuotHomLin_mk, kerQuotHomLin_mk, kerQuotForm_mk, kerQuotForm_mk]
  exact polar_apply_of_mem_orth hg a b

variable [CharP K 2]

theorem kappa_projHom_eq_of_commute (hQ : ∃ v, Q v ≠ 0) (s : matrixIsometries Q)
    (y : CFSG.RankThree.Classical2.orthDerived Q)
    (hy : ∀ x, (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) (sNil s.val x) =
      sNil s.val ((y : (Fin d → K) ≃ₗ[K] (Fin d → K)) x)) :
    isometryConjugationHom Q s (projHom Q y) = projHom Q y := by
  apply projLiftHom_injective hQ
  rw [projLiftHom_apply, projLiftHom_apply, projLift_projHom]
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := (matrixLinearEquiv s.val).surjective v
  have h : projLift hQ (isometryConjugationHom Q s (projHom Q y)) (matrixLinearEquiv s.val w) =
      matrixLinearEquiv s.val (projLift hQ (projHom Q y) w) :=
    projLift_kappa_apply hQ (matrixIsometryInclusion Q s) (projHom Q y) w
  rw [h, projLift_projHom]
  have h1 := hy w
  rw [sNil_apply, sNil_apply, map_sub] at h1
  have h2 : matrixLinearEquiv s.val ((y : (Fin d → K) ≃ₗ[K] (Fin d → K)) w) =
      (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) (matrixLinearEquiv s.val w) := by
    have := congrArg (· + (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) w) h1
    simp only [sub_add_cancel] at this
    exact this.symm
  exact h2

end Core

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Field K] [CharP K 2] in
theorem exists_finset_card_four (hq4 : 4 ≤ Nat.card K) : ∃ t : Finset K, t.card = 4 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
    (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hq4)
  exact ⟨t, ht⟩

theorem exists_mem_range_quad_eq_one {N : (Fin d → K) →ₗ[K] (Fin d → K)}
    (hW : ∃ w ∈ LinearMap.range N, Q w ≠ 0) : ∃ w₁ ∈ LinearMap.range N, Q w₁ = 1 := by
  obtain ⟨w, hwW, hQw⟩ := hW
  refine ⟨(sqrtTwo K (Q w))⁻¹ • w, Submodule.smul_mem _ _ hwW, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul, ← mul_inv, sqrtTwo_mul_self, inv_mul_cancel₀ hQw]

theorem exists_core_kerQuotHom_eq (hQ : ∃ v, Q v ≠ 0)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) (hq4 : 4 ≤ Nat.card K)
    (s : matrixIsometries Q) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), Q w ≠ 0)
    (h : (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) →ₗ[K]
      (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)))
    (hh : ∀ p q, kerQuotForm _ (polar_sNil_left s hss) (h p) (h q) =
      kerQuotForm _ (polar_sNil_left s hss) p q) :
    ∃ x, kerQuotHom hQ (perfectCore (autFixSubgroup (isometryConjugationHom Q s))) (sNil s.val)
      (fun _ hx v => projLift_sNil_of_mem_core hQ s hx v) x = h := by
  classical
  have := finite_linearEquiv_pi (K := K) (d := d)
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  have hadj := polar_sNil_left s hss
  obtain ⟨w₁, hw₁, hQw₁⟩ := exists_mem_range_quad_eq_one hW
  have hβ := kerQuotForm_isAlt (sNil s.val) hadj
  have hβn := kerQuotForm_nondegenerate (sNil s.val) hadj hB
  obtain ⟨r, b, -, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  let G₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    TauCeti.QuadraticMap.orthogonalGroup Q ⊓ nilCommutant (sNil s.val)
  let φ₀ : ↥G₀ →* Module.End K (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) :=
    (kerQuotHomLin (sNil s.val)).comp (Subgroup.inclusion inf_le_right)
  have hφ₀ : ∀ (g : ↥G₀) u u', kerQuotForm _ hadj (φ₀ g u) (φ₀ g u') = kerQuotForm _ hadj u u' :=
    fun g u u' => kerQuotForm_kerQuotHomLin (sNil s.val) hadj _ g.2.1 u u'
  have hlift : ∀ f : (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)) →ₗ[K]
      (LinearMap.ker (sNil s.val) ⧸ rangeInKer (sNil s.val)),
      (∀ u u', kerQuotForm _ hadj (f u) (f u') = kerQuotForm _ hadj u u') → ∃ g, φ₀ g = f := by
    intro f hf
    obtain ⟨g, hgO, -, hg, hgf⟩ := exists_orth_lift_kerQuot (sNil s.val) hB hNN hadj hw₁ hQw₁ f hf
    exact ⟨⟨g, hgO, hg⟩, hgf⟩
  let ρ₀ := sympChart hβ hb φ₀ hφ₀
  have hρ₀ : Function.Surjective ρ₀ := sympChart_surjective hβ hb φ₀ hφ₀ hlift
  let G₁ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) := ⁅G₀, G₀⁆
  have hG₁Ω : G₁ ≤ CFSG.RankThree.Classical2.orthDerived Q :=
    Subgroup.commutator_mono inf_le_left inf_le_left
  have hG₁G₀ : G₁ ≤ G₀ := CFSG.Quasithin.A3.commutator_self_le G₀
  let ρ₁ : ↥G₁ →* StatedSp r K := ρ₀.comp (Subgroup.inclusion hG₁G₀)
  have hperf : Group.IsPerfect (StatedSp r K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp r K (Or.inl (exists_finset_card_four hq4))
  have hρ₁ : Function.Surjective ρ₁ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hperf.commutator_eq_top, commutator_def,
      Subgroup.commutator_le]
    intro A _ B _
    obtain ⟨gA, rfl⟩ := hρ₀ A
    obtain ⟨gB, rfl⟩ := hρ₀ B
    refine ⟨⟨⁅(gA : (Fin d → K) ≃ₗ[K] (Fin d → K)), (gB : (Fin d → K) ≃ₗ[K] (Fin d → K))⁆,
      Subgroup.commutator_mem_commutator gA.2 gB.2⟩, ?_⟩
    change ρ₀ (Subgroup.inclusion hG₁G₀ ⟨_, _⟩) = ⁅ρ₀ gA, ρ₀ gB⁆
    rw [← map_commutatorElement]
    rfl
  have hcore : (perfectCore (⊤ : Subgroup ↥G₁)).map ρ₁ = ⊤ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hρ₁]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hperf.commutator_eq_top)
  let ψ₁ : ↥G₁ →* matrixProjectiveDerived Q := (projHom Q).comp (Subgroup.inclusion hG₁Ω)
  have hH : (perfectCore (⊤ : Subgroup ↥G₁)).map ψ₁ ≤
      perfectCore (autFixSubgroup (isometryConjugationHom Q s)) := by
    refine le_perfectCore_of_perfect ?_ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact kappa_projHom_eq_of_commute hQ s _ fun x => (hG₁G₀ y.2).2 x
    · rw [← Subgroup.map_commutator, perfectCore_perfect]
  obtain ⟨gh, hgh⟩ := hlift h hh
  have hA : ρ₀ gh ∈ (perfectCore (⊤ : Subgroup ↥G₁)).map ρ₁ := by
    rw [hcore]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyA⟩ := hA
  refine ⟨⟨ψ₁ y, hH ⟨y, hy, rfl⟩⟩, ?_⟩
  have e1 : kerQuotHom hQ (perfectCore (autFixSubgroup (isometryConjugationHom Q s))) (sNil s.val)
      (fun _ hx v => projLift_sNil_of_mem_core hQ s hx v) ⟨ψ₁ y, hH ⟨y, hy, rfl⟩⟩ =
        φ₀ (Subgroup.inclusion hG₁G₀ y) := by
    refine kerQuotMap_congr' (sNil s.val) ?_
      (fun x => projLift_sNil_of_mem_core hQ s (hH ⟨y, hy, rfl⟩) x)
      (fun x => (mem_nilCommutant (sNil s.val)).mp (hG₁G₀ y.2).2 x)
    change ((projLift hQ (projHom Q (Subgroup.inclusion hG₁Ω y)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
      (Fin d → K) →ₗ[K] (Fin d → K)) = _
    rw [projLift_projHom]
    rfl
  rw [e1]
  have e2 : LinearMap.toMatrix b b (φ₀ (Subgroup.inclusion hG₁G₀ y)) =
      LinearMap.toMatrix b b h := by
    have h1 := congrArg (fun A : StatedSp r K =>
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hyA
    change LinearMap.toMatrix b b (φ₀ (Subgroup.inclusion hG₁G₀ y)) =
      LinearMap.toMatrix b b (φ₀ gh) at h1
    rw [h1, hgh]
  exact (LinearMap.toMatrix b b).injective e2

end Main

end CFSG.SeitzReduction.OmegaPilot
