module

public import CFSG.LieType.Chevalley.TwistedE6EvenCoverLifts
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverCommuting

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6Cover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover CFSG.LocalAnalysis.ComponentInitial

theorem heightSet_pos {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.E6.tag h, IsRoot TwistTag.E6.tag α ∧ 0 < height α :=
  fun _ hα => ⟨hα.1, hα.2.1⟩

theorem heightSet_permLattice
    {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.E6.tag h,
      permLattice TwistTag.E6.perm α ∈ heightSet TwistTag.E6.tag h :=
  fun _ hα => ⟨hα.1.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hα.2.1,
    by rw [height_permLattice]; exact hα.2.2⟩

theorem heightSet_closed {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.E6.tag h, ∀ β ∈ heightSet TwistTag.E6.tag h, ∀ a b : ℕ, 1 ≤ a →
      1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
        a • α + b • β ∈ heightSet TwistTag.E6.tag h := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.2.1, hβ.2.1, hα.2.2]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K →+* K}

theorem ker_eq_bot_of_graphFixedRootGroup
    (hσ : Function.Surjective σ) {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card (fixField σ) = 2 ^ f) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* graphFixedRootGroup TwistTag.E6 K σ) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := odd_card_torusParam (σ := σ) (by omega) hk
  have hχ : ∀ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β → 0 < height β →
      (rootChar K β).comp (torusLift σ) ≠ 1 := by
    intro β hβ hβp h1
    obtain ⟨t, ht⟩ := exists_foldChar_ne_one hk (exists_not_dvd_foldCoord hf hβ hβp)
    refine ht (Units.ext (Subtype.ext ?_))
    have h := congrArg (fun φ : (Fin TwistTag.E6.foldedTag.rank → (fixField σ)ˣ) →* Kˣ =>
      ((φ t : Kˣ) : K)) h1
    simp only [MonoidHom.comp_apply, rootChar_torusLift, coe_fixUnit, MonoidHom.one_apply,
      Units.val_one] at h
    exact h
  refine ker_eq_bot_of_coprime_central_series_of_commute η hη hC h2
    (U := graphFixedPosUnipotent TwistTag.E6 K σ)
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ)
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2) (not_dvd_index_graphFixedPosUnipotent 2 hσ)
    hT (fixedTorus σ) fixedTorus_mem_graphFixedRootGroup (fun t x hx => ?_)
    (maxHeight TwistTag.E6.tag).toNat
    (fun i => series TwistTag.E6.tag K i ⊓ twistedFixedGroup TwistTag.E6 K σ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun α => {g | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ g ∈ orbitGroup σ α})
    (fun α => {g | IsRoot TwistTag.E6.tag α ∧ 0 < height α ∧ g ∈ orbitGroup σ α})
    ?_ ?_ ?_ ?_
  ·
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨torusVec_conj_mem_rootSpan (torusLift σ t) (fun _ hα => hα.1) hx₁,
      ?_⟩
    exact mul_mem (mul_mem (fixedTorus_mem_twistedFixedGroup t) hx₂)
      (inv_mem (fixedTorus_mem_twistedFixedGroup t))
  ·
    rw [series, Nat.cast_zero, sub_zero, heightSeries_maxHeight_add_one, bot_inf_eq]
  ·
    rw [series, toNat_maxHeight, add_sub_cancel_left, heightSeries_one]
    rfl
  ·
    intro i _
    refine inf_le_inf_right _ ?_
    rw [series_succ, series_eq]
    exact heightSeries_antitone (by omega)
  ·
    intro i _ t x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨torusVec_conj_mem_heightSeries (torusLift σ t) hx₁,
      mul_mem (mul_mem (fixedTorus_mem_twistedFixedGroup t) hx₂)
        (inv_mem (fixedTorus_mem_twistedFixedGroup t))⟩
  ·
    intro i _ x hx g hg
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (mul_mem (inv_mem hx₂) (inv_mem hg₂)) hx₂) hg₂⟩
    rw [series_succ] at hx₁
    rw [series_eq]
    rw [← heightSeries_one] at hg₁
    have hc := commutator_heightSeries_le K (maxHeight TwistTag.E6.tag - i) 1
      (Subgroup.commutator_mem_commutator (inv_mem hx₁) (inv_mem hg₁))
    rwa [commutatorElement_def, inv_inv, inv_inv] at hc
  ·
    intro i _ x hx
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, pow_mem hx₂ 2⟩
    rw [series_succ] at hx₁
    rw [series_eq]
    exact sq_mem_heightSeries_succ hx₁
  ·
    intro i _ x hx hfix
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, hx₂⟩
    rw [series_succ] at hx₁
    rw [series_eq]
    exact mem_heightSeries_succ_of_forall_comp hT (torusLift σ) hχ hx₁ fun t => by
      have h := (Subgroup.mem_inf.1 (hfix t)).1
      rwa [series_eq] at h
  ·
    rintro α g ⟨hα, hαp, hg⟩
    refine orbitGroup_le_of_subset (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
      (fun β hβ => ?_) ⟨hα, hαp⟩ hg
    rw [← image_permLattice_posRoots TwistTag.E6]
    exact ⟨β, hβ, rfl⟩
  · rintro α g ⟨hα, hαp, hg⟩
    refine orbitGroup_le_of_subset (S := {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α})
      (fun β hβ => ?_) ⟨hα, hαp⟩ hg
    rw [← image_permLattice_posRoots TwistTag.E6]
    exact ⟨β, hβ, rfl⟩
  ·
    intro i _ j _ b hb₁ hb₂ _ _ hbT hZY
    change ∀ x ∈ series TwistTag.E6.tag K (i + 1) ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ y ∈ series TwistTag.E6.tag K (j + 1) ⊓ twistedFixedGroup TwistTag.E6 K σ, b x y = 0
    simp only [series_succ] at hb₁ hb₂ hbT ⊢
    refine form_eq_zero_of_orbitPairs hσ heightSet_pos heightSet_permLattice heightSet_closed
      heightSet_pos heightSet_permLattice heightSet_closed b hb₁ hb₂ fun α hα β hβ x hx y hy => ?_
    by_cases hβα : β ∈ TwistTag.E6.diagramOrbit α
    · have e := orbitGroup_congr (σ := σ) (TwistTag.E6.diagramOrbit_eq_of_mem hβα)
      rw [e] at hy
      exact hZY α x ⟨hα.1, hα.2.1, hx⟩ y ⟨hα.1, hα.2.1, hy⟩
    · have hsub := orbitGroup_le_of_subset (σ := σ) heightSet_permLattice hα
      have hsub' := orbitGroup_le_of_subset (σ := σ) heightSet_permLattice hβ
      exact form_orbit_eq_zero hf hk hα.1 hα.2.1 hβ.1 hβ.2.1 hβα b
        (fun x hx x' hx' y hy => hb₁ x (hsub hx) x' (hsub hx') y (hsub' hy))
        (fun x hx y hy y' hy' => hb₂ x (hsub hx) y (hsub' hy) y' (hsub' hy'))
        (fun t x hx y hy => hbT t x (hsub hx) y (hsub' hy)) x hx y hy
  ·
    rintro α a y ⟨hα, -, ha⟩ ⟨-, -, hy⟩
    exact lift_commute_orbitGroup hη hC hf hk hα a y ha hy

theorem twisted_E6_model
    {J : Type} [Group J] {f : ℕ} (hf : 1 ≤ f)
    (hJ : TwistedChevalleyModel J .E6 (2 ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K →+* K),
      Function.Surjective σ ∧ Nat.card (fixField σ) = 2 ^ f ∧
        Nonempty (J ≃* graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hJ
  obtain ⟨σ', hσ', -, -, -, k, hkset, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hK : Nat.card K = 2 ^ (2 * f) := by
    rw [hcard, ← pow_mul, mul_comm]
    rfl
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hcard σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ'
  rw [hσσ'] at hZ
  have hZ' : Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈
        Subgroup.center (graphFixedRootGroup TwistTag.E6 K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL TwistTag.E6.tag K) ∈
          ⁅twistedFixedGroup TwistTag.E6 K σ, twistedFixedGroup TwistTag.E6 K σ⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext
      (congrArg (Subtype.val : graphFixedRootGroup TwistTag.E6 K σ → ModGL TwistTag.E6.tag K) hcen))
  have hfix : fixField σ = k := by
    refine SetLike.ext' ?_
    rw [hkset]
    ext c
    rw [SetLike.mem_coe, mem_fixField, hσ, Set.mem_ofPred_eq]
  refine ⟨K, inferInstance, inferInstance, this, σ, ?_, by rw [hfix, hkcard], ⟨?_⟩⟩
  · rw [← hσσ']
    exact σ'.surjective
  · exact e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
      (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))

end CFSG.LieType.Chevalley.TwistedE6Cover

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley TwistedE6Cover

theorem twisted_E6_nonprime_even_field_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hf : 2 ≤ f) (hJ : LieModel J .twistedE6 0 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  have hX : TwistedChevalleyModel J .E6 (2 ^ f) := by
    rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
    · exact absurd hc (by decide)
    · exact hX.2
    · exact absurd hr (by decide)
    · exact absurd hs (by decide)
  obtain ⟨K, _, _, _, σ, hσ, hk, ⟨e⟩⟩ := twisted_E6_model (by omega) hX
  set η' : E →* graphFixedRootGroup TwistTag.E6 K σ := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_graphFixedRootGroup hσ hf hk η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Chevalley
