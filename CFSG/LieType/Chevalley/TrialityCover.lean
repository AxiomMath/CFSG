module

public import CFSG.LieType.Chevalley.TrialityCoverLifts
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverCommuting

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TwistedE6Cover
  CFSG.LocalAnalysis.ComponentInitial

theorem heightSet_pos {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.D4.tag h, IsRoot TwistTag.D4.tag α ∧ 0 < height α :=
  fun _ hα => ⟨hα.1, hα.2.1⟩

theorem heightSet_permLattice
    {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.D4.tag h,
      permLattice TwistTag.D4.perm α ∈ heightSet TwistTag.D4.tag h :=
  fun _ hα => ⟨hα.1.permLattice TwistTag.D4.cartan_perm, by rw [height_permLattice]; exact hα.2.1,
    by rw [height_permLattice]; exact hα.2.2⟩

theorem heightSet_closed {h : ℤ} :
    ∀ α ∈ heightSet TwistTag.D4.tag h, ∀ β ∈ heightSet TwistTag.D4.tag h, ∀ a b : ℕ, 1 ≤ a →
      1 ≤ b → IsRoot TwistTag.D4.tag (a • α + b • β) →
        a • α + b • β ∈ heightSet TwistTag.D4.tag h := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.2.1, hβ.2.1, hα.2.2]

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem odd_card_torus :
    Odd (Nat.card (Kˣ × (trialityFixedField K σ.toRingHom)ˣ)) := by
  rw [Nat.card_prod]
  exact (odd_card_units_of_charTwo K).mul (odd_card_units_of_charTwo _)

theorem ker_eq_bot_of_graphFixedRootGroup
    (hσ : σ ^ 3 = 1)
    (hlt : Nat.card (trialityFixedField K σ.toRingHom) < Nat.card K)
    (hk : 3 ≤ Nat.card (trialityFixedField K σ.toRingHom)) {n : ℕ} (hn : 3 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hsep : ∀ i j : Fin 6, i ≠ j → Separated σ i j)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := odd_card_torus σ
  have hχ : ∀ β : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag β → 0 < height β →
      (rootChar K β).comp (torusParam σ) ≠ 1 := fun β hβ hβp =>
    rootChar_comp_torusParam_ne_one σ hσ hlt hk hβ hβp
  refine ker_eq_bot_of_coprime_central_series_of_commute η hη hC h2
    (U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2) (not_dvd_index_graphFixedPosUnipotent 2
      σ.surjective) hT (trialityTorus σ) (trialityTorus_mem_graphFixedRootGroup σ hσ)
    (fun t x hx => ?_) (maxHeight TwistTag.D4.tag).toNat
    (fun i => series TwistTag.D4.tag K i ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun α => {g | IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧ g ∈ orbitGroup σ α})
    (fun α => {g | IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧ g ∈ orbitGroup σ α})
    ?_ ?_ ?_ ?_
  ·
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨torusVec_conj_mem_rootSpan (torusParam σ t) (fun _ hα => hα.1)
      hx₁, ?_⟩
    exact mul_mem (mul_mem (trialityTorus_mem_twistedFixedGroup σ hσ t) hx₂)
      (inv_mem (trialityTorus_mem_twistedFixedGroup σ hσ t))
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
    exact Subgroup.mem_inf.2 ⟨torusVec_conj_mem_heightSeries (torusParam σ t) hx₁,
      mul_mem (mul_mem (trialityTorus_mem_twistedFixedGroup σ hσ t) hx₂)
        (inv_mem (trialityTorus_mem_twistedFixedGroup σ hσ t))⟩
  ·
    intro i _ x hx g hg
    obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hg₁, hg₂⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (mul_mem (inv_mem hx₂) (inv_mem hg₂)) hx₂) hg₂⟩
    rw [series_succ] at hx₁
    rw [series_eq]
    rw [← heightSeries_one] at hg₁
    have hc := commutator_heightSeries_le K (maxHeight TwistTag.D4.tag - i) 1
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
    exact mem_heightSeries_succ_of_forall_comp hT (torusParam σ) hχ hx₁ fun t => by
      have h := (Subgroup.mem_inf.1 (hfix t)).1
      rwa [series_eq] at h
  ·
    rintro α g ⟨hα, hαp, hg⟩
    refine orbitGroup_le_of_subset σ (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α})
      (fun β hβ => ?_) ⟨hα, hαp⟩ hg
    rw [← image_permLattice_posRoots TwistTag.D4]
    exact ⟨β, hβ, rfl⟩
  · rintro α g ⟨hα, hαp, hg⟩
    refine orbitGroup_le_of_subset σ (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α})
      (fun β hβ => ?_) ⟨hα, hαp⟩ hg
    rw [← image_permLattice_posRoots TwistTag.D4]
    exact ⟨β, hβ, rfl⟩
  ·
    intro i _ j _ b hb₁ hb₂ _ _ hbT hZY
    change ∀ x ∈ series TwistTag.D4.tag K (i + 1) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ y ∈ series TwistTag.D4.tag K (j + 1) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
        b x y = 0
    simp only [series_succ] at hb₁ hb₂ hbT ⊢
    refine form_eq_zero_of_orbitPairs σ heightSet_pos heightSet_permLattice heightSet_closed
      heightSet_pos heightSet_permLattice heightSet_closed b hb₁ hb₂ fun α hα β hβ x hx y hy => ?_
    by_cases hβα : β ∈ TwistTag.D4.diagramOrbit α
    · have e : orbitGroup σ β = orbitGroup σ α := by
        rw [orbitGroup, orbitGroup, TwistTag.D4.diagramOrbit_eq_of_mem hβα]
      rw [e] at hy
      exact hZY α x ⟨hα.1, hα.2.1, hx⟩ y ⟨hα.1, hα.2.1, hy⟩
    · have hsub := orbitGroup_le_of_subset σ heightSet_permLattice hα
      have hsub' := orbitGroup_le_of_subset σ heightSet_permLattice hβ
      exact form_orbit_eq_zero σ hσ hsep hα.1 hα.2.1 hβ.1 hβ.2.1 hβα b
        (fun x hx x' hx' y hy => hb₁ x (hsub hx) x' (hsub hx') y (hsub' hy))
        (fun x hx y hy y' hy' => hb₂ x (hsub hx) y (hsub' hy) y' (hsub' hy'))
        (fun t x hx y hy => hbT t x (hsub hx) y (hsub' hy)) x hx y hy
  ·
    rintro α a y ⟨hα, -, ha⟩ ⟨-, -, hy⟩
    exact lift_commute_orbitGroup σ hη hC hσ hn hK (hsep 4 5 (by decide)) hα a y ha hy

theorem triality_model
    {J : Type} [Group J] {f : ℕ} (hf : 1 ≤ f)
    (hJ : TwistedChevalleyModel J .D4 (2 ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (σ : K ≃+* K),
      σ ^ 3 = 1 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧ Nat.card K = (2 ^ f) ^ 3 ∧
        Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f ∧
          Nonempty (J ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hJ
  obtain ⟨σ', hσ', hord, -, -, k, hkset, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two hf K hcard
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', hσ]
  have hK : Nat.card K = 2 ^ (3 * f) := by
    rw [hcard, ← pow_mul, mul_comm]
    rfl
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hperf := (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf K hcard σ hσ).2.2.1
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ'
  rw [hσσ'] at hZ
  have hZ' : Subgroup.center
      ↥⁅twistedFixedGroup TwistTag.D4 K σ, twistedFixedGroup TwistTag.D4 K σ⁆ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ := by
      rw [← hperf]
      exact x.2
    have hcen : (⟨x, hxC⟩ : graphFixedRootGroup TwistTag.D4 K σ) ∈
        Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hyH : (y : ModGL TwistTag.D4.tag K) ∈
          ⁅twistedFixedGroup TwistTag.D4 K σ, twistedFixedGroup TwistTag.D4 K σ⁆ := by
        rw [hperf]
        exact y.2
      have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨y, hyH⟩)
      exact Subtype.ext h1
    rw [hZ, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.2 (Subtype.ext
      (congrArg (Subtype.val : graphFixedRootGroup TwistTag.D4 K σ → ModGL TwistTag.D4.tag K)
        hcen))
  have h3 : σ' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ'
    rwa [hord] at h
  have hfix : trialityFixedField K σ'.toRingHom = k := by
    refine SetLike.ext' ?_
    rw [hkset]
    ext c
    rw [SetLike.mem_coe, mem_trialityFixedField, Set.mem_ofPred_eq]
    change σ' c = c ↔ _
    rw [hσ']
  subst hσσ'
  exact ⟨K, inferInstance, inferInstance, this, σ', h3, hσ', hcard, by rw [hfix, hkcard],
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans
      (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr hperf)))⟩⟩

end CFSG.LieType.Chevalley.TrialityCover

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley TrialityCover

theorem triality_nonprime_even_field_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hf : 2 ≤ f) (hJ : LieModel J .trialityD4 0 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  have hX : TwistedChevalleyModel J .D4 (2 ^ f) := by
    rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
    · exact absurd hc (by decide)
    · exact hX.2
    · exact absurd hr (by decide)
    · exact absurd hs (by decide)
  obtain ⟨K, _, _, _, σ, hσ, hq, hK, hk, ⟨e⟩⟩ := triality_model (by omega) hX
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK' : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hlt : Nat.card (trialityFixedField K σ.toRingHom) < Nat.card K := by
    rw [hk, hK']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk3 : 3 ≤ Nat.card (trialityFixedField K σ.toRingHom) := by omega
  have hsep : ∀ i j : Fin 6, i ≠ j → Separated σ i j := fun i j hij =>
    separated_of_ne σ hσ hlt hk3 (exists_norm_ne_one σ hq hK h4) hij
  set η' : E →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_graphFixedRootGroup σ hσ hlt hk3 (n := 3 * f) (by omega) hK' hsep
    η' (e.surjective.comp hη) (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Chevalley
