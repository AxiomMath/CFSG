module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6C4Sub
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2DiagSub
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E6C4

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open CFSG.ComponentClassification.CatLeafProof (rootChar_single')
open CFSG.RankThree.Chevalley (conjGL baseChangeGL_simpleRootSL2 trace_baseChangeGL
  ordinary_E_root_SL2_full_module_traces_all_characteristics)
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K]

omit
  [Finite K] in
theorem rootChar_eq_one_of_commute {e : Fin TwistTag.E6.tag.rank → Kˣ}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (h : Commute (rootDiagUnit TwistTag.E6.tag e) (pinnedX TwistTag.E6.tag K γ 1)) :
    rootChar e γ = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX e hγ (1 : K)
  rw [h.eq, mul_inv_cancel_right, mul_one] at h1
  exact Units.ext (pinnedX_injective TwistTag.E6.tag K γ h1).symm

omit
  [Finite K] in
theorem eq_one_of_commute_pair {e : Fin TwistTag.E6.tag.rank → Kˣ}
    (a : Fin TwistTag.E6.foldedTag.rank)
    (h : TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a)
    (hc : Commute (rootDiagUnit TwistTag.E6.tag e)
      (xUnit TwistTag.E6.tag K (TwistTag.E6.orbitMin a) 1 *
        xUnit TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1)) :
    e (TwistTag.E6.orbitMin a) = 1 ∧ e (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) = 1 := by
  set i := TwistTag.E6.orbitMin a with hi
  set j := TwistTag.E6.perm i with hj
  set d := rootDiagUnit TwistTag.E6.tag e with hd
  have hconj : d * (xUnit TwistTag.E6.tag K i 1 * xUnit TwistTag.E6.tag K j 1) * d⁻¹ =
      xUnit TwistTag.E6.tag K i (e i : K) * xUnit TwistTag.E6.tag K j (e j : K) := by
    calc d * (xUnit TwistTag.E6.tag K i 1 * xUnit TwistTag.E6.tag K j 1) * d⁻¹ =
        (d * pinnedX TwistTag.E6.tag K (Pi.single i 1) 1 * d⁻¹) *
          (d * pinnedX TwistTag.E6.tag K (Pi.single j 1) 1 * d⁻¹) := by
          rw [pinnedX_single, pinnedX_single]
          group
      _ = _ := by
          rw [hd, rootDiagUnit_conj_pinnedX e (isRoot_single _ i),
            rootDiagUnit_conj_pinnedX e (isRoot_single _ j), rootChar_single', rootChar_single',
            mul_one, mul_one, pinnedX_single, pinnedX_single]
  rw [hc.eq, mul_inv_cancel_right] at hconj
  rcases orbit_pair_or_single a with ⟨-, -, hword⟩ | ⟨h', -, -⟩
  · have hp := pair_eq_pair hword (Ne.symm h) hconj
    exact ⟨Units.ext hp.1.symm, Units.ext hp.2.symm⟩
  · exact absurd h' h

omit
  [Finite K] in
theorem twE6Untwist_commute_simpleRootSL2 (μ : Kˣ) (B : SL2 K) :
    Commute (twE6Untwist μ) (simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ B) := by
  have h3 : twE6Tuple μ ⟨3, by decide⟩ = 1 := rfl
  have hle : (simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩).range ≤
      Subgroup.centralizer {twE6Untwist μ} := by
    rw [range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · have h := rootDiagUnit_conj_pinnedX (twE6Tuple μ)
        (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩) c
      rw [rootChar_single', h3, Units.val_one, one_mul, pinnedX_single] at h
      rw [twE6Untwist]
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    · have h := rootDiagUnit_conj_pinnedX (twE6Tuple μ)
        (IsRoot.neg (isRoot_single TwistTag.E6.tag ⟨3, by decide⟩)) c
      rw [rootChar_neg', rootChar_single', h3, inv_one, Units.val_one, one_mul,
        pinnedX_neg_single] at h
      rw [twE6Untwist]
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle ⟨B, rfl⟩)).symm

omit [Finite K] in
theorem simpleRootSL2_mem_twE6C4Sub (σ : K ≃+* K) (μ : Kˣ) (A : SL2 (fixSubfield σ)) :
    simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
      (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) ∈ twE6C4Sub σ μ := by
  have hS : simpleRootSL2 TwistTag.E6.tag (fixSubfield σ) ⟨3, by decide⟩ A ∈
      rootGenerated (fixSubfield σ) := by
    refine rootPair_le_rootGenerated e6Alpha4_check ?_
    rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
    exact ⟨A, rfl⟩
  have hM : simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
      (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) ∈ twE6C4Image σ := by
    rw [← baseChangeGL_simpleRootSL2]
    exact ⟨_, hS, rfl⟩
  refine ⟨_, hM, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
    ← (twE6Untwist_commute_simpleRootSL2 μ _).eq, inv_mul_cancel_left]

omit
  [Finite K] in
theorem trace_entrywise (δ : K ≃+* K) (y : ModGL TwistTag.E6.tag K) :
    LinearMap.trace K (RootModule TwistTag.E6.tag K)
        ((Units.map (entrywiseHom δ.toRingHom) y : ModGL TwistTag.E6.tag K) :
          Module.End K (RootModule TwistTag.E6.tag K)) =
      δ (LinearMap.trace K (RootModule TwistTag.E6.tag K)
        (y : Module.End K (RootModule TwistTag.E6.tag K))) := by
  rw [units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem eq_one_of_odd_fix_twE6C4Sub {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) {μ : Kˣ}
    (hμ : σ (μ : K) = -μ) {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hβ : Odd (orderOf β))
    (hfix : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ twE6C4Sub σ μ → β x = x) : β = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (show 1 ≤ f * 2 by omega) (by rw [hK, ← pow_mul])
    rw [ringChar.eq K p]
    exact hp2
  have hk2 := ringChar_fixSubfield_ne_two hK2 σ
  have hσσ : σ * σ = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, show p ^ f * p ^ f = Fintype.card K by
      rw [← Nat.card_eq_fintype_card, hK, sq]]
    exact FiniteField.pow_card c
  have hJC := twE6C4Sub_le_graphFixedRootGroup hK2 σ hμ
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
  have hδk : ∀ c, σ c = c → δ c = c := by
    have htr : ∀ A : SL2 (fixSubfield σ), δ (LinearMap.trace K (RootModule TwistTag.E6.tag K)
        ((simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
          (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
            ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))) =
        LinearMap.trace K (RootModule TwistTag.E6.tag K)
          ((simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
            (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A) :
              ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) := by
      intro A
      have hJ := simpleRootSL2_mem_twE6C4Sub σ μ A
      have h1 := congrArg Subtype.val (hfix ⟨_, hJC hJ⟩ hJ)
      rw [hβapp] at h1
      have h2 := congrArg (fun y : ModGL TwistTag.E6.tag K =>
        LinearMap.trace K (RootModule TwistTag.E6.tag K)
          (y : Module.End K (RootModule TwistTag.E6.tag K))) h1
      simp only [Units.val_mul, LinearMap.trace_conj] at h2
      rw [← trace_entrywise δ]
      calc _ = LinearMap.trace K (RootModule TwistTag.E6.tag K)
            ((((g : ModGL TwistTag.E6.tag K) * d) *
              Units.map (entrywiseHom δ.toRingHom) (simpleRootSL2 TwistTag.E6.tag K
                ⟨3, by decide⟩ (Matrix.SpecialLinearGroup.map
                  (algebraMap (fixSubfield σ) K) A)) *
              ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ : ModGL TwistTag.E6.tag K) :
                Module.End K (RootModule TwistTag.E6.tag K)) := by
            rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj]
        _ = _ := by
            rw [show ((g : ModGL TwistTag.E6.tag K) * d) * Units.map (entrywiseHom δ.toRingHom)
                (simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ (Matrix.SpecialLinearGroup.map
                  (algebraMap (fixSubfield σ) K) A)) * ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ =
                (g : ModGL TwistTag.E6.tag K) * (d * Units.map (entrywiseHom δ.toRingHom)
                  (simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
                    (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A)) * d⁻¹) *
                  (g : ModGL TwistTag.E6.tag K)⁻¹ by group]
            exact congrArg (fun y : ModGL TwistTag.E6.tag K =>
              LinearMap.trace K (RootModule TwistTag.E6.tag K)
                (y : Module.End K (RootModule TwistTag.E6.tag K))) h1
    have hcl := (ordinary_E_root_SL2_full_module_traces_all_characteristics TwistTag.E6.tag
      (Or.inl rfl)).2 (fixSubfield σ) K ⟨3, by decide⟩ 1 1
    have hsub : {x : K | ∃ A : SL2 (fixSubfield σ), x = LinearMap.trace K
        (RootModule TwistTag.E6.tag K) ((1 * simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩
          (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) K) A)) * 1⁻¹ :
            ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K))} ⊆
        (RingHom.eqLocusField δ.toRingHom (RingHom.id K) : Set K) := by
      rintro _ ⟨A, rfl⟩
      rw [conjGL_one', one_mul, inv_one, mul_one]
      exact htr A
    have hle := Subfield.closure_le.2 hsub
    rw [hcl] at hle
    intro c hc
    exact hle ⟨⟨c, hc⟩, rfl⟩
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
  have hβapp' : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (β h : ModGL TwistTag.E6.tag K) = ((g : ModGL TwistTag.E6.tag K) * d) * h *
        ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ := by
    intro h
    rw [hβapp, show Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL TwistTag.E6.tag K) =
      h from Units.ext (entrywise_id _)]
    group
  set t := twE6Untwist μ with ht
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le _ _ _ g.2).1
  set g' : adjointGroup TwistTag.E6.tag K :=
    rootDiagAut TwistTag.E6.tag K (twE6Tuple μ) ⟨g, hgC⟩ with hg'
  have hg'coe : (g' : ModGL TwistTag.E6.tag K) = t * g * t⁻¹ := by
    rw [hg', coe_rootDiagAut]
    rfl
  have htd : t * d = d * t := by
    rw [ht, twE6Untwist, hd, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hx' : t * ((g : ModGL TwistTag.E6.tag K) * d) * t⁻¹ =
      (g' : ModGL TwistTag.E6.tag K) * d := by
    rw [hg'coe]
    calc t * ((g : ModGL TwistTag.E6.tag K) * d) * t⁻¹ = t * g * t⁻¹ * (t * d) * t⁻¹ := by group
      _ = t * g * t⁻¹ * d := by rw [htd]; group
  have hcommM : ∀ m ∈ twE6C4Image σ, Commute ((g' : ModGL TwistTag.E6.tag K) * d) m := by
    intro m hm
    have hj : t⁻¹ * m * t ∈ twE6C4Sub σ μ := ⟨m, hm, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h1 := congrArg Subtype.val (hfix ⟨_, hJC hj⟩ hj)
    rw [hβapp'] at h1
    have hc : Commute ((g : ModGL TwistTag.E6.tag K) * d) (t⁻¹ * m * t) := by
      calc ((g : ModGL TwistTag.E6.tag K) * d) * (t⁻¹ * m * t) =
          ((g : ModGL TwistTag.E6.tag K) * d) * (t⁻¹ * m * t) *
            ((g : ModGL TwistTag.E6.tag K) * d)⁻¹ * ((g : ModGL TwistTag.E6.tag K) * d) := by
            group
        _ = (t⁻¹ * m * t) * ((g : ModGL TwistTag.E6.tag K) * d) := by rw [h1]
    rw [← hx']
    have e : m = t * (t⁻¹ * m * t) * t⁻¹ := by group
    rw [e]
    exact (Commute.conj_iff t).2 hc
  obtain ⟨f₀, hf₀⟩ := exists_rootDiagUnit_eq_of_commute_subfield (τ := TwistTag.E6.tag)
    (Or.inl rfl) hK2 hk2 (fixSubfield σ).subtype (g := g')
    (a := compatDiag TwistTag.E6 σ.toRingHom u) e6GammaC4
    (fun y hy => mem_rootFinset.1 (e6GammaC4_check y hy y.1 (by simp)).1)
    (fun y hy v hv => hcommM _ ⟨v, rootPair_le_rootGenerated (e6GammaC4_check y hy) hv, rfl⟩)
    12 (fun α hα => e6GammaC4_reg α (mem_rootFinset.2 hα))
  set e := f₀ * compatDiag TwistTag.E6 σ.toRingHom u with he
  have hxe : (g' : ModGL TwistTag.E6.tag K) * d = rootDiagUnit TwistTag.E6.tag e := by
    rw [hf₀, hd, he, rootDiagUnit_mul]
  have hgd : (g : ModGL TwistTag.E6.tag K) * d = rootDiagUnit TwistTag.E6.tag e := by
    have h1 : (g : ModGL TwistTag.E6.tag K) * d = t⁻¹ * (rootDiagUnit TwistTag.E6.tag e) * t := by
      rw [← hxe, ← hx']
      group
    rw [h1, ht, twE6Untwist, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    rw [mul_comm (twE6Tuple μ)⁻¹ e, mul_assoc, inv_mul_cancel, mul_one]
  have hcommE : ∀ m ∈ twE6C4Image σ, Commute (rootDiagUnit TwistTag.E6.tag e) m := by
    intro m hm
    rw [← hxe]
    exact hcommM m hm
  have hmemK : ∀ v ∈ rootGenerated (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype v ∈ twE6C4Image σ := fun v hv => ⟨v, hv, rfl⟩
  have he4 : e ⟨3, by decide⟩ = 1 := by
    have hv : xUnit TwistTag.E6.tag (fixSubfield σ) ⟨3, by decide⟩ 1 ∈
        rootGenerated (fixSubfield σ) := by
      refine rootPair_le_rootGenerated e6Alpha4_check (Subgroup.mem_sup_left ?_)
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    have h := hcommE _ (hmemK _ hv)
    rw [baseChangeGL_xUnit, map_one, ← pinnedX_single] at h
    have h1 := rootChar_eq_one_of_commute (isRoot_single _ _) h
    rwa [rootChar_single'] at h1
  have hθ : rootChar e e6Theta = 1 := by
    have hv : pinnedX TwistTag.E6.tag (fixSubfield σ) e6Theta 1 ∈
        rootGenerated (fixSubfield σ) :=
      rootPair_le_rootGenerated e6Theta_check
        (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, rfl⟩))
    have h := hcommE _ (hmemK _ hv)
    rw [baseChangeGL_pinnedX, map_one] at h
    exact rootChar_eq_one_of_commute (mem_rootFinset.1 (e6Theta_check e6Theta (by simp)).1) h
  have hpair : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ ⟨1, by decide⟩ → j ≠ ⟨3, by decide⟩ →
      e j = 1 := by
    intro j hj1 hj3
    obtain ⟨a, h, ha, hj | hj⟩ := e6_pair_cover j hj1 hj3 <;>
    · have hv := xUnit_mul_xUnit_mem_rootGenerated (K := fixSubfield σ) a h (orbitSign_one ha) 1
      have hc := hcommE _ (hmemK _ hv)
      rw [map_mul, baseChangeGL_xUnit, baseChangeGL_xUnit, map_one] at hc
      have := eq_one_of_commute_pair a h hc
      rw [hj]
      first | exact this.1 | exact this.2
  have hne1 : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ ⟨1, by decide⟩ → e j = 1 := by
    intro j hj
    by_cases hj3 : j = ⟨3, by decide⟩
    · rw [hj3]
      exact he4
    · exact hpair j hj hj3
  have he1 : e ⟨1, by decide⟩ ^ 2 = 1 := by
    have hprod : rootChar e e6Theta = e ⟨1, by decide⟩ ^ (e6Theta ⟨1, by decide⟩) := by
      refine Finset.prod_eq_single _ (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
      rw [hne1 b hb, one_zpow]
    have h2 : e6Theta ⟨1, by decide⟩ = 2 := by decide
    rw [hprod, h2, zpow_two] at hθ
    rw [sq]
    exact hθ
  have he2 : rootDiagUnit TwistTag.E6.tag e * rootDiagUnit TwistTag.E6.tag e = 1 := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
    congr 1
    funext j
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases hj : j = ⟨1, by decide⟩
    · rw [hj, ← sq]
      exact he1
    · rw [hne1 j hj, one_mul]
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hβapp', hβapp', hgd]
    calc rootDiagUnit TwistTag.E6.tag e * (rootDiagUnit TwistTag.E6.tag e *
          (h : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag e)⁻¹) *
          (rootDiagUnit TwistTag.E6.tag e)⁻¹ =
        (rootDiagUnit TwistTag.E6.tag e * rootDiagUnit TwistTag.E6.tag e) * h *
          (rootDiagUnit TwistTag.E6.tag e * rootDiagUnit TwistTag.E6.tag e)⁻¹ := by group
      _ = h := by rw [he2, one_mul, inv_one, mul_one]
  exact eq_one_of_odd_of_mem_zpowers (α := β) (by rw [sq]; exact hβ2) (by
    rcases hβ with ⟨m, hm⟩
    exact ⟨m, hm⟩) (mem_zpowers β)

end CFSG.ComponentClassification.Burgoyne.E2
