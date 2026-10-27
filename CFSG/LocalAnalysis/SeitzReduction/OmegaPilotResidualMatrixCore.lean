module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixTwist

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)
open scoped commutatorElement

section GeneralRoot

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eq_eichler_of_commute_rootSylowSub [CharP F 2] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (hEΩ : ∀ u w, eichler Q u w ∈ orthDerived Q)
    {Z : V ≃ₗ[F] V} (hZO : Z ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hZ1 : Z ≠ 1)
    (hcomm : ∀ E ∈ rootSylowSub (Q := Q) P₁.e P₂.e, E ∈ orthDerived Q → Z * E = E * Z) :
    ∃ c : F, c ≠ 0 ∧ Z = eichler Q P₁.e (c • P₂.e) := by
  have hcommR : ∀ E ∈ rootSylowSub (Q := Q) P₁.e P₂.e, E ∈ orthDerived Q →
      ∀ x, Z (E x) = E (Z x) := by
    intro E hE hEΩ' x
    have h := congrArg (fun A : V ≃ₗ[F] V => A x) (hcomm E hE hEΩ')
    simpa only [LinearEquiv.mul_apply] using h
  obtain ⟨-, γ, -, x₀, -, hx₀, hZ⟩ := eq_smul_eichler_of_commute (φ := Z.toAddEquiv)
    (σ := RingEquiv.refl F) (μ := 1) (polarNondegOn_top hQ) h₁₂
    Submodule.mem_top Submodule.mem_top Submodule.mem_top Submodule.mem_top one_ne_zero
    (fun c x => by simp) (fun x => by simp [map_of_mem hZO]) (fun _ _ => Submodule.mem_top)
    (fun w _ hw x _ => hcommR _ (eichler_mem_rootSylowSub_left hw _) (hEΩ _ _) x)
  have hZ' : ∀ x, Z x = γ • eichler Q P₁.e x₀ x := fun x => hZ x Submodule.mem_top
  have hγ : γ = 1 := by
    apply eq_one_of_mul_self_eq_one
    have h1 := map_of_mem hZO (P₂.e + P₂.f)
    rw [hZ', map_smul_eq_sq, map_of_mem (eichler_mem_orthogonalGroup Q P₁.e x₀),
      QuadraticMap.map_add Q, P₂.Q_e, P₂.Q_f, P₂.polar_ef] at h1
    linear_combination h1
  have hZE : ∀ x, Z x = eichler Q P₁.e x₀ x := fun x => by rw [hZ', hγ, one_smul]
  have hx₀e : x₀ = polar Q x₀ P₂.f • P₂.e := by
    refine eq_smul_of_forall_commute_eichler hQ h₁₂ h₁₃ h₂₃ hx₀ fun w h2w h1w => ?_
    apply LinearEquiv.ext
    intro x
    have h := hcommR _ (eichler_mem_rootSylowSub_right h₁₂.ee h2w h1w) (hEΩ _ _) x
    simp only [LinearEquiv.mul_apply]
    rw [← hZE, ← hZE]
    exact h.symm
  refine ⟨polar Q x₀ P₂.f, fun h0 => hZ1 ?_, ?_⟩
  · apply LinearEquiv.ext
    intro x
    rw [hZE, hx₀e, h0, zero_smul, eichler_zero_right]
  · apply LinearEquiv.ext
    intro x
    rw [hZE, ← hx₀e]

theorem exists_eq_eichler_of_commute_sylow [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) (hEΩ : ∀ u w, eichler Q u w ∈ orthDerived Q)
    (U : Sylow 2 ↥(orthDerived Q)) {g : orthDerived Q} (hg1 : g ≠ 1)
    (hg : ∀ u ∈ (U : Subgroup ↥(orthDerived Q)), u * g = g * u) :
    ∃ x : V ≃ₗ[F] V, x ∈ orthDerived Q ∧ ∃ c : F, c ≠ 0 ∧
      (g : V ≃ₗ[F] V) = eichler Q (x P₁.e) (c • x P₂.e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun h : V ≃ₗ[F] V => (h : V → V))
    (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hR : IsPGroup 2 ((rootSylowSub (Q := Q) P₁.e P₂.e).subgroupOf (orthDerived Q)) :=
    (isPGroup_rootSylowSub (Q := Q) P₁.e P₂.e).comap_subtype
  obtain ⟨y, hy⟩ := exists_conj_mem_sylow hR U
  have hyO : (y : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ y.2
  set Z : V ≃ₗ[F] V := (y : V ≃ₗ[F] V)⁻¹ * g * y with hZdef
  have hZO : Z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (mul_mem (inv_mem hyO) (Subgroup.commutator_le_self _ g.2)) hyO
  have hZ1 : Z ≠ 1 := by
    intro h
    apply hg1
    apply Subtype.ext
    have : (g : V ≃ₗ[F] V) = y * Z * (y : V ≃ₗ[F] V)⁻¹ := by rw [hZdef]; group
    rw [this, h, mul_one, mul_inv_cancel]
    rfl
  obtain ⟨c, hc0, hc⟩ := eq_eichler_of_commute_rootSylowSub hQ h₁₂ h₁₃ h₂₃ hEΩ hZO hZ1
    fun E hE hEΩ' => by
      have h1 := hg _ (hy ⟨E, hEΩ'⟩ hE)
      have h2 := congrArg (fun A : orthDerived Q => (A : V ≃ₗ[F] V)) h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [hZdef]
      calc (y : V ≃ₗ[F] V)⁻¹ * g * y * E = (y : V ≃ₗ[F] V)⁻¹ * (g * (y * E * (y : V ≃ₗ[F] V)⁻¹)) * y := by group
        _ = (y : V ≃ₗ[F] V)⁻¹ * ((y * E * (y : V ≃ₗ[F] V)⁻¹) * g) * y := by rw [h2]
        _ = E * ((y : V ≃ₗ[F] V)⁻¹ * g * y) := by group
  refine ⟨y, y.2, c, hc0, ?_⟩
  have : (g : V ≃ₗ[F] V) = y * Z * (y : V ≃ₗ[F] V)⁻¹ := by rw [hZdef]; group
  rw [this, hc, eichler_conj hyO, map_smul]

end GeneralRoot

section Core

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem coe_commutatorElement' {G : Type*} [Group G] {H : Subgroup G} (a b : H) :
    ((⁅a, b⁆ : H) : G) = ⁅(a : G), (b : G)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

variable {S : similarityPairs Q} {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))

theorem commutator_autFixSubgroup_le [CharP K 2] (hQne : ∃ v, Q v ≠ 0) :
    ⁅autFixSubgroup (matrixProjectiveConjugationHom Q S),
      autFixSubgroup (matrixProjectiveConjugationHom Q S)⁆ ≤ descentImage e := by
  rw [Subgroup.commutator_le]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨E₁, rfl⟩ := projHom_surjective Q y₁
  obtain ⟨E₂, rfl⟩ := projHom_surjective Q y₂
  have hC : ∀ {E : orthDerived Q}, projHom Q E ∈ autFixSubgroup (matrixProjectiveConjugationHom Q S) →
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ pairCentralizer S := fun {E} hE =>
    ⟨Subgroup.commutator_le_self _ E.2, fun v =>
      (commute_of_kappa_projHom_eq hQne S (mem_autFixSubgroup.mp hE) v).symm⟩
  set h₁ := e ⟨_, hC hy₁⟩ with hh₁
  set h₂ := e ⟨_, hC hy₂⟩ with hh₂
  have hmem : ((⁅h₁, h₂⁆ : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) :
      pairFix S ≃ₗ[descentField S.val.right] pairFix S) ∈ pairDescentDerived hS := by
    rw [coe_commutatorElement']
    exact Subgroup.commutator_mem_commutator h₁.2 h₂.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  change projHom Q (descentDerivedExt e ⟨_, hmem⟩) = _
  rw [show ⁅projHom Q E₁, projHom Q E₂⁆ = projHom Q ⁅E₁, E₂⁆ from
    (map_commutatorElement (projHom Q) E₁ E₂).symm]
  congr 1
  apply Subtype.ext
  change ((e.symm (Subgroup.inclusion (Subgroup.commutator_le_self _) ⟨_, hmem⟩) :
    pairCentralizer S) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = _
  have hincl : Subgroup.inclusion (Subgroup.commutator_le_self _) ⟨_, hmem⟩ = ⁅h₁, h₂⁆ :=
    Subtype.ext rfl
  rw [hincl, map_commutatorElement, hh₁, hh₂, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply, coe_commutatorElement', coe_commutatorElement']

theorem perfectCore_autFixSubgroup_eq [CharP K 2] (hQne : ∃ v, Q v ≠ 0)
    (hJ : commutator ↥(pairDescentDerived hS) = ⊤) :
    perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S)) = descentImage e :=
  le_antisymm ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans
    (commutator_autFixSubgroup_le e hQne)) (descentImage_le_perfectCore e hJ)

theorem projHom_descentDerivedExt_injective [CharP K 2] (hQne : ∃ v, Q v ≠ 0) :
    Function.Injective ((projHom Q).comp (descentDerivedExt e)) := by
  refine (projHom_injective hQne).comp fun g₁ g₂ h => ?_
  have h1 := congrArg (fun A : orthDerived Q => (A : (Fin d → K) ≃ₗ[K] (Fin d → K))) h
  have h2 : e.symm (Subgroup.inclusion (Subgroup.commutator_le_self _) g₁) =
      e.symm (Subgroup.inclusion (Subgroup.commutator_le_self _) g₂) := Subtype.ext h1
  exact Subgroup.inclusion_injective _ (e.symm.injective h2)

@[expose] noncomputable def descentImageEquiv [CharP K 2] (hQne : ∃ v, Q v ≠ 0) :
    ↥(pairDescentDerived hS) ≃* ↥(descentImage e) :=
  MonoidHom.ofInjective (projHom_descentDerivedExt_injective e hQne)

theorem coe_descentImageEquiv [CharP K 2] (hQne : ∃ v, Q v ≠ 0) (g : pairDescentDerived hS) :
    ((descentImageEquiv e hQne g : descentImage e) : matrixProjectiveDerived Q) =
      projHom Q (descentDerivedExt e g) := rfl

end Core

end CFSG.SeitzReduction.OmegaPilot
