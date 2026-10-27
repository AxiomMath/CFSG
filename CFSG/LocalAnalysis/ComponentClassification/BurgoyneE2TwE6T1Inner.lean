module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Root
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (conjGL baseChangeGL_simpleRootSL2 trace_baseChangeGL
  ordinary_E_root_SL2_full_module_traces_all_characteristics)
open scoped MatrixGroups


theorem trace_entrywise_e6 {K : Type} [Field K] (δ : K ≃+* K) (y : ModGL TwistTag.E6.tag K) :
    LinearMap.trace K (RootModule TwistTag.E6.tag K)
        ((Units.map (entrywiseHom δ.toRingHom) y : ModGL TwistTag.E6.tag K) :
          Module.End K (RootModule TwistTag.E6.tag K)) =
      δ (LinearMap.trace K (RootModule TwistTag.E6.tag K)
        (y : Module.End K (RootModule TwistTag.E6.tag K))) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem exists_inndiag_of_odd_fix_traces {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hβ : Odd (orderOf β))
    (hfix : ∀ A : SL2 (fixSubfield σ), ∃ y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      β y = y ∧ LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) =
        LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((simpleRootSL2 TwistTag.E6.tag K (t1Node 3)
            (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
              ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) :
    ∃ (g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (b : Fin TwistTag.E6.tag.rank → Kˣ),
      (∀ i, b (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (b i)) ∧
      ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        (β h : ModGL TwistTag.E6.tag K) =
          ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b) * h *
            ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b)⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hσσ : σ * σ = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, show p ^ f * p ^ f = Fintype.card K by
      rw [← Nat.card_eq_fintype_card, hK, sq]]
    exact FiniteField.pow_card c
  obtain ⟨-, -, -, -, -, hΔ, hδ, hNF, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨g, u, δ, hβeq⟩ := hNF β
  set d := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hd
  have hβapp : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (β h : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          (d * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * d⁻¹) *
            (g : ModGL TwistTag.E6.tag K)⁻¹ := by
    intro h
    rw [hβeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hδ]
  have htr : ∀ A : SL2 (fixSubfield σ), δ (LinearMap.trace K (RootModule TwistTag.E6.tag K)
      ((simpleRootSL2 TwistTag.E6.tag K (t1Node 3)
        (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
          ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) =
      LinearMap.trace K (RootModule TwistTag.E6.tag K)
        ((simpleRootSL2 TwistTag.E6.tag K (t1Node 3)
          (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
            ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) := by
    intro A
    obtain ⟨y, hy, hytr⟩ := hfix A
    rw [← hytr]
    have h1 := congrArg Subtype.val hy
    rw [hβapp] at h1
    have h2 := congrArg (fun z : ModGL TwistTag.E6.tag K =>
      LinearMap.trace K (RootModule TwistTag.E6.tag K)
        (z : Module.End K (RootModule TwistTag.E6.tag K))) h1
    rw [← trace_entrywise_e6 δ]
    calc _ = LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((((g : ModGL TwistTag.E6.tag K) * d) *
            Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.E6.tag K) *
            ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ : ModGL TwistTag.E6.tag K) :
              Module.End K (RootModule TwistTag.E6.tag K)) := by
          rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj]
      _ = _ := by
          rw [show ((g : ModGL TwistTag.E6.tag K) * d) *
              Units.map (entrywiseHom δ.toRingHom) (y : ModGL TwistTag.E6.tag K) *
                ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ =
              (g : ModGL TwistTag.E6.tag K) * (d * Units.map (entrywiseHom δ.toRingHom)
                (y : ModGL TwistTag.E6.tag K) * d⁻¹) * (g : ModGL TwistTag.E6.tag K)⁻¹ by group]
          exact h2
  have hc1 : ∀ A : SL2 K, conjGL (1 : GL (Fin 2) K) A = A := fun A =>
    Subtype.ext (by simp [conjGL])
  have hcl := (ordinary_E_root_SL2_full_module_traces_all_characteristics TwistTag.E6.tag
    (Or.inl rfl)).2 (fixSubfield σ) K (t1Node 3) 1 1
  have hsub : {x : K | ∃ A : SL2 (fixSubfield σ), x = LinearMap.trace K
      (RootModule TwistTag.E6.tag K) ((1 * simpleRootSL2 TwistTag.E6.tag K (t1Node 3)
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A)) * 1⁻¹ :
          ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))} ⊆
      (RingHom.eqLocusField δ.toRingHom (RingHom.id K) : Set K) := by
    rintro _ ⟨A, rfl⟩
    rw [hc1, one_mul, inv_one, mul_one]
    exact htr A
  have hle := Subfield.closure_le.2 hsub
  rw [hcl] at hle
  have hδk : ∀ c, σ c = c → δ c = c := fun c hc => hle ⟨⟨c, hc⟩, rfl⟩
  have hδσ : δ ∈ Subgroup.zpowers σ :=
    CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hδk
  have hδδ : δ * δ = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hδσ
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hσσ, one_zpow]
  have hδ1 : δ = 1 := by
    have hn : δ ^ orderOf β = 1 := by
      rw [← hΘ β g u δ hβeq, ← map_pow, pow_orderOf_eq_one, map_one]
    obtain ⟨m, hm⟩ := hβ
    rw [hm, pow_succ, pow_mul, sq, hδδ, one_pow, one_mul] at hn
    exact hn
  subst hδ1
  refine ⟨g, compatDiag TwistTag.E6 σ.toRingHom u, compatDiag_perm u, fun h => ?_⟩
  rw [hβapp, show Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL TwistTag.E6.tag K) =
    h from Units.ext (entrywise_id _), hd]
  group

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
