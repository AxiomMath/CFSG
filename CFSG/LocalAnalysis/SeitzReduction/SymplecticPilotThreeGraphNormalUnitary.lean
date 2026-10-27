module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective centralizerPerfectCore
  statedSpCongr coe_statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauMat coe_tauSp tauMat_apply)

section Abstract

theorem statedSpMap_tauSp {K₁ K₂ : Type} [Field K₁] [Field K₂] [CharP K₁ 2] [CharP K₂ 2]
    (ι : K₁ →+* K₂) (g : StatedSp 2 K₁) :
    statedSpMap ι 2 (tauSp g) = tauSp (statedSpMap ι 2 g) := by
  ext i j
  simp only [coe_statedSpMap, coe_tauSp]
  change ι (tauMat _ i j) = tauMat _ i j
  rw [tauMat_apply, tauMat_apply]
  simp [Matrix.GeneralLinearGroup.map, map_sub, map_mul]

theorem exists_conj_eq_of_range_eq_fixedSubgroup_two {k K₀ : Type} [Field k] [Finite k]
    [CharP k 2] [Field K₀] [Finite K₀] [CharP K₀ 2] (hcard : Nat.card K₀ = Nat.card k)
    {P : Type*} [Group P] {θ : MulAut P} (υ : StatedSp 2 k →* P) (hυ : Function.Injective υ)
    (hυr : υ.range = fixedSubgroup θ) (ε : StatedSp 2 K₀ →* P) (hε : Function.Injective ε)
    (hfix : ∀ x, θ (ε x) = ε x) :
    ∃ (y : P) (ι : K₀ ≃+* k) (κ : StatedSp 2 K₀ →* StatedSp 2 K₀),
      (κ = MonoidHom.id _ ∨ κ = tauSp) ∧ θ y = y ∧
        ∀ x, y * ε x * y⁻¹ = υ (statedSpMap (ι : K₀ →+* k) 2 (κ x)) := by
  obtain ⟨ι₀⟩ := nonempty_ringEquiv_of_natCard_eq' (A := K₀) (B := k) hcard
  have hle : ε.range ≤ υ.range := by
    rw [hυr]
    rintro _ ⟨x, rfl⟩
    exact hfix x
  have : Finite υ.range := Finite.of_surjective _ υ.rangeRestrict_surjective
  have hrange : ε.range = υ.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hε).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hυ).toEquiv,
      Nat.card_congr (statedSpCongr ι₀ 2).toEquiv]
  set δ₀ : StatedSp 2 K₀ ≃* StatedSp 2 k :=
    ((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hrange)).trans
      (MonoidHom.ofInjective hυ).symm with hδ₀def
  have hδ₀ : ∀ x, υ (δ₀ x) = ε x := by
    intro x
    have h1 := (MonoidHom.ofInjective hυ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε x))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hsfix : ∀ s, θ (υ s) = υ s := fun s => by
    have : υ s ∈ fixedSubgroup θ := hυr ▸ ⟨s, rfl⟩
    exact this
  obtain ⟨s, ρ, hsρ | hsρ⟩ :=
    F4Pilot.exists_eq_conj_mul_fieldSp_tauSp ((statedSpCongr ι₀ 2).symm.trans δ₀)
  · have hδ₀' : ∀ x, δ₀ x = s * statedSpMap ((ι₀.trans ρ : K₀ ≃+* k) : K₀ →+* k) 2 x * s⁻¹ := by
      intro x
      have h1 := hsρ (statedSpCongr ι₀ 2 x)
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      rw [h1, F4Pilot.fieldSp_eq_statedSpMap, F4Pilot.coe_statedSpCongr, F4Pilot.statedSpMap_comp]
      rfl
    refine ⟨(υ s)⁻¹, ι₀.trans ρ, MonoidHom.id _, Or.inl rfl, by rw [map_inv, hsfix], fun x => ?_⟩
    rw [← hδ₀, hδ₀', map_mul, map_mul, map_inv, MonoidHom.id_apply]
    group
  · have hδ₀' : ∀ x, δ₀ x =
        s * statedSpMap ((ι₀.trans ρ : K₀ ≃+* k) : K₀ →+* k) 2 (tauSp x) * s⁻¹ := by
      intro x
      have h1 := hsρ (statedSpCongr ι₀ 2 x)
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
      rw [h1, F4Pilot.fieldSp_eq_statedSpMap, F4Pilot.coe_statedSpCongr, ← statedSpMap_tauSp,
        F4Pilot.statedSpMap_comp]
      rfl
    refine ⟨(υ s)⁻¹, ι₀.trans ρ, tauSp, Or.inr rfl, by rw [map_inv, hsfix], fun x => ?_⟩
    rw [← hδ₀, hδ₀', map_mul, map_mul, map_inv]
    group

end Abstract

section Construct

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀]

variable [Finite G] in
theorem exists_param_of_proj_two {f r : ℕ} [Finite K₀] [CharP K₀ 2] (e : L ≃* StatedSp 3 K₀)
    (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (k : Fin 3) {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') {C₀ : GL (Fin r) K'} (hC : IsPrimeFormGram C₀)
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h (C₀ : Matrix (Fin r) (Fin r) K')),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →* E', ∀ g, π' (s g) = g)
    (hperf : Group.IsPerfect (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')))
    (μ : StatedSp 2 h.fixedField →* gramSU h (C₀ : Matrix (Fin r) (Fin r) K'))
    (hμ : Function.Injective ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)).comp μ))
    (hμr : ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)).comp μ).range =
        fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)))
    (hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G))
    (ρ' : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) →*
      primeFormP h (C₀ : Matrix (Fin r) (Fin r) K'))
    (hρs : Function.Surjective ρ')
    (hρker : ρ'.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))))
    (hρt : ∀ y, ρ' ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
      ⟨t, hN⟩ y) = primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (ρ' y)) :
    ∃ (ι : K₀ ≃+* h.fixedField) (κ : StatedSp 2 K₀ →* StatedSp 2 K₀)
      (Φ : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →* G),
      (κ = MonoidHom.id _ ∨ κ = tauSp) ∧ Φ.range = neighbourCore e k ∧ Φ.ker ≤ center (gramSU h (C₀
          : Matrix (Fin r) (Fin r) K')) ∧
      (∀ x : StatedSp 2 K₀, Φ (μ (statedSpMap (ι : K₀ →+* h.fixedField) 2 (κ x))) =
        ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp 3 K₀) : L) : G)) ∧
      ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x) := by
  have hK4 : 4 ≤ Nat.card K₀ := hKc ▸ four_le_two_pow hf
  have : Finite K' := h.finite
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)
    with hπdef
  set ε := complSpToNeighbourCore e hK4 (by omega : 1 ≤ 2) k with hεdef
  have hεinj : Function.Injective ε := complSpToNeighbourCore_injective e hK4 (by omega) k
  have hρεinj : Function.Injective (ρ'.comp ε) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : ε x ∈ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) := hρker hx
    have hxc : x ∈ center (StatedSp 2 K₀) := by
      rw [mem_center_iff]
      intro y
      apply hεinj
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hc (ε y)
    rw [center_statedSp_eq_bot 2] at hxc
    exact hxc
  have hfix : ∀ x, primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) ((ρ'.comp ε) x) =
      (ρ'.comp ε) x := by
    intro x
    rw [MonoidHom.comp_apply, ← hρt]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : ((ε x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G) ∈ L :=
      (e.symm _).2
    rw [← mem_centralizer_iff.1 htC _ hxL, mul_inv_cancel_right]
  obtain ⟨y, ι, κ, hκ, hy, hyε⟩ := exists_conj_eq_of_range_eq_fixedSubgroup_two
    (hKc.trans h.card_fixedField.symm) (π.comp μ) hμ hμr (ρ'.comp ε) hρεinj hfix
  set ρ₁ := (MulAut.conj y).toMonoidHom.comp ρ' with hρ₁def
  have hρ₁s : Function.Surjective ρ₁ := (MulAut.conj y).surjective.comp hρs
  have hρ₁ker : ρ₁.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) := by
    intro z hz
    apply hρker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact (MulAut.conj y).map_eq_one_iff.mp hz
  have hρ₁t : ∀ z, ρ₁ ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
      ⟨t, hN⟩ z) = primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (ρ₁ z) := by
    intro z
    rw [hρ₁def, MonoidHom.comp_apply, MonoidHom.comp_apply, hρt, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hy]
  have hρ₁ε : ∀ x, ρ₁ (ε x) = π (μ (statedSpMap (ι : K₀ →+* h.fixedField) 2 (κ x))) := by
    intro x
    rw [← MonoidHom.comp_apply π μ, ← hyε x]
    rfl
  clear_value ρ₁
  have : Group.IsPerfect (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := F4Pilot.exists_lift_of_central π (QuotientGroup.mk'_surjective _)
    hsplit ρ₁ hρ₁s hρ₁ker
  refine ⟨ι, κ, (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).subtype.comp Φ₀, hκ, ?_,
    ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  · intro g hg
    have hg₀ : Φ₀ g = 1 :=
      (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).subtype_injective
        (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact normOneScalars_le_center h _ _ h1
  · intro x
    have : Group.IsPerfect (StatedSp 2 K₀) := isPerfect_statedSp_of_four_le hK4 2
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp 2 K₀) hρ₁ker
      (φ := Φ₀.comp (μ.comp ((statedSpMap (ι : K₀ →+* h.fixedField) 2).comp κ)))
      (ψ := ε) (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hΦ₀, hρ₁ε])
    exact congrArg (fun F : StatedSp 2 K₀ →* centralizerPerfectCore
      (modelToG e (rootTorusSp K₀ k)) =>
        ((F x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G)) heq
  · intro x
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center
      (S := gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) hρ₁ker
      (φ := ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
        ⟨t, hN⟩).toMonoidHom.comp Φ₀)
      (ψ := Φ₀.comp (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h)).toMonoidHom)
      (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.coe_toMonoidHom, hρ₁t, hΦ₀, hΦ₀]
        change primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h)
          (x : primeFormP h (C₀ : Matrix (Fin r) (Fin r) K')) = _
        rw [primeFormFieldAut_mk]
        rfl)
    have h1 := congrArg (fun F : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →*
      centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) =>
        ((F x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G)) heq
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    exact h1

variable [Finite G]
  in
theorem exists_unitaryNeighbourParam_three {f : ℕ} [Finite K₀] [CharP K₀ 2]
    (hset : SeitzSetting G L) (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K₀)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin 3)
    (hk : RootKindSp e t f k .unitaryEven) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * 2)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
      (ι : K₀ ≃+* h.fixedField) (κ : StatedSp 2 K₀ →* StatedSp 2 K₀)
      (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G),
      (κ = MonoidHom.id _ ∨ κ = tauSp) ∧ Φ.range = neighbourCore e k ∧
      Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) ∧
      (∀ x : StatedSp 2 K₀,
        Φ (uModelSU h hC₀ (statedSpMap (ι : K₀ →+* h.fixedField) 2 (κ x))) =
          ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp 3 K₀) : L) : G)) ∧
      ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x) := by

  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, -, hρt⟩ :=
    exists_surjective_primeFormP_neighbourCore_unitary' hset hKc hf (by omega : 2 ≤ 2) e htC ht
      k rfl rfl (Or.inl rfl) hk hN
  obtain ⟨-, rfl, hJ⟩ : Sp2mKind.unitaryEven = .unitaryEven ∧ r = 2 * 2 ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = blockSwapJ r 2 := by
    rcases hcase with h1 | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * 2 = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  obtain ⟨ι, κ, Φ, hκ, hrange, hker, hN1, hN3⟩ := exists_param_of_proj_two e hKc hf htC k h' hC
    (gramSU_exists_section_of_central h' hC (by omega) hf) (isPerfect_gramSU h' hC (by omega))
    (uModelSU h' hJ) (uModelP_injective (h := h') (by omega) hJ)
    (range_uModelP (h := h') (by omega) hq hC hJ) hN ρ' hρs hρker hρt
  exact ⟨K', inferInstance, h', hk2, C₀, hC, hJ, ι, κ, Φ, hκ, hrange, hker, hN1, hN3⟩

end Construct

end CFSG.SeitzReduction.SymplecticPilot
