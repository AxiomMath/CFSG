module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L3Lin

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OddSelector.Catalog7L3

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem l3_inner_false [Finite A] (ha : orderOf a = 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL 3 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} (hρa : ρ a = conjAut 3 k B)
    (hsrc : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center L))) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hm3 : 3 ≤ 3 := le_rfl
  have h2 : conjAut 3 k (B ^ 2) = 1 := by
    rw [map_pow, ← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨μ, hμ⟩ := (conjAut_eq_one_iff hm3 _).mp h2
  have hB1 : ∀ c : kˣ, B ≠ GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    have h1 : ρ a = 1 := by rw [hρa, hc, conjAut_scalar]
    rw [← map_one ρ] at h1
    rw [hinj h1, orderOf_one] at ha
    omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := inner_component_lift hm3 B hL₁
  obtain ⟨r₀, hr₀⟩ := isSquare_of_sq_eq_scalar hμ
  have hr0 : r₀ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr₀
    exact μ.ne_zero hr₀
  set c₀ : kˣ := Units.mk0 r₀ hr0
  have hsq : B ^ 2 = GeneralLinearGroup.scalar (Fin 3) (c₀ ^ 2) := by
    rw [← hμ]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr₀, sq]
  obtain ⟨r, hr2, ⟨eX⟩, hXi⟩ := square_component_sl hm3 htwo hsq hB1 hXh
  obtain ⟨eL⟩ := mulEquiv_of_lift_injective hinj hmap hXi
  set eLS := eL.trans eX
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact not_rank_or_odd_center_of_sl_two hk2 eLS (Or.inr hZ)
  · have hker : eLS.symm.toMonoidHom.ker ≤ center (SpecialLinearGroup (Fin r) k) := by
      intro x hx
      have : x = 1 := eLS.symm.injective (by rw [map_one]; exact hx)
      rw [this]
      exact one_mem _
    have hns := not_small_source_of_sl_cover hr3 hℓ hℓ2 he hk eLS.symm.toMonoidHom hker
    rcases hsrc with ⟨p, f, hp2, hs⟩ | h7
    · exact false_of_not_small_source hns hp2 (Or.inl hs)
    · exact false_of_not_small_source hns (p := 3) (f := 1) (by norm_num) (Or.inr (Or.inl h7))

theorem l3_graph_field_false (ha : orderOf a = 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL 3 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 3) k} {σ : k ≃+* k} (hσ : σ ≠ 1)
    (hρa : ρ a = conjAut 3 k B * fieldAut 3 k σ * dualAut 3 k)
    (hsrc : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hα2 : (conjAut 3 k B * fieldAut 3 k σ * dualAut 3 k) ^ 2 = 1 := by
    rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨heven, hσx, H, hH⟩ :=
    UnitaryHigher.linear_graph_field_involution_descent hℓ he hk (le_refl 3) B σ hσ hα2
  have hg : 1 ≤ e / 2 := by obtain ⟨r, hr⟩ := heven; omega
  have hKe : Nat.card k = ℓ ^ (2 * (e / 2)) := by
    rw [hk]
    congr 1
    obtain ⟨r, hr⟩ := heven
    omega
  have hud : UnitaryFieldData ℓ (e / 2) k := ⟨hℓ, hg, hKe⟩
  have hσbar : ∀ x, σ x = hud.bar x := fun x => by rw [hσx, hud.bar_apply]
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hCN⟩ :=
    linear_graph_field_full_centralizer_rigidity hud (n := 3) (le_refl 3) σ hσbar
  set χ := conjAut 3 k H with hχ
  set β := fieldAut 3 k σ * dualAut 3 k with hβ
  set N := (unitarySU ℓ (e / 2) k 3).map (conjAut 3 k) with hNdef
  have hρa' : ρ a = χ * β * χ⁻¹ := by rw [hρa, hH]
  have hY : (OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {ρ a}).map
      (MulAut.conj χ⁻¹).toMonoidHom =
        OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {β} := by
    rw [map_conj_inner_inf_centralizer, hρa']
    congr 3
    group
  set L₀ := (L.map ρ).map (MulAut.conj χ⁻¹).toMonoidHom with hL₀def
  have hL₀ : CFSG.Assembly.IsComponentOf L₀
      (OuterAutomorphisms.inner (projectiveSL 3 k) ⊓ centralizer {β}) := by
    have := isComponentOf_map_conj hL₁ χ⁻¹
    rwa [hY] at this
  have := finite_mulAut_projectiveSL (k := k) 3
  have hL₀N : CFSG.Assembly.IsComponentOf L₀ N := by
    refine isComponentOf_of_normal_of_comm (le_inf hNinn hNC)
      (fun y hy => mem_normalizer_of_normal_subgroupOf hNC hNnormal hy.2) ?_ hL₀
    intro x _ hx y _ hy
    rw [hCN] at hx hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self β i j).eq
  have hK2 : Nat.card k = (ℓ ^ (e / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
  have eU : unitaryPSU hud 3 ≃* StatedProj (StatedSU 3 (ℓ ^ (e / 2)) k) :=
    unitaryPSUEquiv hud (by omega)
  have hnq : (3, ℓ ^ (e / 2)) ≠ (3, 2) := fun h => by
    have h2 := congrArg Prod.snd h
    simp only at h2
    have : ℓ ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self ℓ (by omega)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp this)
  have : IsSimpleGroup (StatedProj (StatedSU 3 (ℓ ^ (e / 2)) k)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k ℓ (e / 2) hK2 3
      (le_refl 3) hnq
  have : IsSimpleGroup (unitaryPSU hud 3) := eU.isSimpleGroup
  have hNs : IsSimpleGroup N := ι.symm.isSimpleGroup
  have hL₀eq : L₀ = N := eq_of_isComponentOf_simple hNs hL₀N
  have hLimg : L.map ρ = N.map (MulAut.conj χ).toMonoidHom := by
    rw [← hL₀eq, hL₀def, map_conj_inv_map_conj]
  have eL : L ≃* unitaryPSU hud 3 :=
    ((L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLimg).trans
      ((N.equivMapOfInjective _ (MulAut.conj χ).injective).symm))).trans ι.symm
  have hLnab : ∃ x y : L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := exists_ne_commute_of_isQuasisimple hL₁.2.2
    set eρ := L.equivMapOfInjective ρ hinj
    refine ⟨eρ.symm x, eρ.symm y, fun hc => hxy ?_⟩
    have := congrArg eρ hc
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  have : IsSimpleGroup L := eL.isSimpleGroup
  have eZ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_isSimpleGroup hLnab)).trans
      QuotientGroup.quotientBot
  set ψ := (eZ.trans (eL.trans eU)).symm with hψ
  rcases hsrc with ⟨p, f, hp2, hs⟩ | ⟨e7⟩
  ·
    have hk2 : (2 : k) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq k ℓ]; exact hℓ2)
    obtain ⟨a', b', ha', hb', hab'⟩ := OddClassSelector.exists_antifixed_sq_add_sq hud hℓ2
    have hsigU : CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ (e / 2) hud.card_eq_sq =
        CFSG.LieType.BorelTits.unitaryInvolution k ℓ (e / 2) :=
      RingEquiv.ext fun z => by
        rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply,
          CFSG.LieType.BorelTits.unitaryInvolution_apply]
    rw [hsigU] at ha' hb'
    have hSU : CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution k ℓ (e / 2)) 3 = StatedSU 3 (ℓ ^ (e / 2)) k :=
      CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK2 3
    obtain ⟨φq, hφq⟩ := OddClassSelector.exists_quaternion_statedProj hk2 _ (le_refl 3) hSU ha'
      hb' hab'
    exact not_psl_two_odd_of_quaternion (ψ.toMonoidHom.comp φq) (ψ.injective.comp hφq) hp2 hs
  ·
    have hdvd : ℓ ^ 3 ∣ Nat.card (L ⧸ center L) := by
      rw [← Nat.card_congr ψ.toEquiv]
      exact prime_cube_dvd_card_psu hℓ hg hK2 (le_refl 3)
    exact not_nonempty_iff.mpr (isEmpty_alternating_seven_of_dvd hℓ hℓ2 hdvd) e7

theorem l3_graph_form [Finite A] (ha : orderOf a = 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL 3 k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ) (inner (projectiveSL 3 k) ⊓ centralizer {ρ a}))
    (hsrc : (∃ p f : ℕ, p ≠ 2 ∧ StatedClassicalModel (L ⧸ center L) .PSL 2 p f) ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center L))) :
    ∃ B : GL (Fin 3) k, (B : Matrix (Fin 3) (Fin 3) k)ᵀ = B ∧
      ρ a = conjAut 3 k B * dualAut 3 k := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) (le_refl 3)
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exfalso
    rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      exact l3_inner_false ha hℓ hℓ2 he hk hinj hL₁ hρa hsrc hZ
    · rcases hsrc with ⟨p, f, hp2, hs⟩ | h7
      · exact field_case_false ha (le_refl 3) hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 (Or.inl hs)
      · exact field_case_false ha (le_refl 3) hℓ hℓ2 he hk hinj hL₁ hτ hρa (p := 3) (f := 1)
          (by norm_num) (Or.inr (Or.inl h7))
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 3 k B * dualAut 3 k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph (le_refl 3) B hα2 with hB | hB
      · exact ⟨B, hB, hρa⟩
      · exact (false_of_transpose_eq_neg htwo B hB).elim
    · exact (l3_graph_field_false ha hℓ hℓ2 he hk hinj hL₁ hτ hρa hsrc).elim

end CFSG.ComponentClassification.GSThmB.CF23I
