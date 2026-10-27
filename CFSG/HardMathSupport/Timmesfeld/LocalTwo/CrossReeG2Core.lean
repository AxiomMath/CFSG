module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeNF
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.ReeStabilizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.AlgebraicGroups

section ReeG2


theorem fieldCoreAt_reeGamma_G2 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {σ : K ≃+* K} (hδp : orderOf (ReeTag.G2.reeGammaFieldAut K a σ) = p) {b : ℕ}
    (hkcard : Nat.card (fixSubfield σ) = 3 ^ (2 * b + 1))
    (hfixed : ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (ReeTag.G2.reeGamma K a).subtype =
      (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype))
    (hdvd : p ∣ Nat.card ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus
      (MonoidHom.id _))) :
    FieldCoreAt p (ReeTag.G2.reeGammaFieldAut K a σ) := by
  classical
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set δ := ReeTag.G2.reeGammaFieldAut K a σ with hδ
  set J := δ.toMonoidHom.eqLocus (MonoidHom.id _) with hJ
  set k := fixSubfield σ with hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; exact (pow_pos (by norm_num) _).ne')
  have : CharP k ReeTag.G2.prime := by
    have : Fintype k := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.center_reeGamma_G2_eq_bot hK)
  have hFix : CFSG.Open.signalizerFixedSubgroup δ = J := Subgroup.ext fun _ => Iff.rfl
  let eC : J ≃* ReeTag.G2.reeGamma k b :=
    (((J).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr hfixed)).trans
    ((ReeTag.G2.reeGamma k b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.G2.tag) k.subtype)).symm
  have hZk : Subgroup.center (ReeTag.G2.reeGamma k b) = ⊥ :=
    (small_Ree_fixed_group_center_trivial b k hkcard).1
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hs, hn, -, hperf, hzero, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components b k hkcard
  have hZJ : Subgroup.center J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have : eC z ∈ Subgroup.center (ReeTag.G2.reeGamma k b) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := eC.surjective y
      rw [← map_mul, ← map_mul, hz y']
    rw [hZk, Subgroup.mem_bot] at this
    exact eC.injective (this.trans (map_one eC).symm)
  let eT : commutator J ≃* commutator (ReeTag.G2.reeGamma k b) :=
    ((commutator J).equivMapOfInjective eC.toMonoidHom eC.injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
  have : IsSimpleGroup (commutator (ReeTag.G2.reeGamma k b)) := hs
  have hZc : Subgroup.center (commutator (ReeTag.G2.reeGamma k b)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (commutator (ReeTag.G2.reeGamma k b))) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hn
      exact hxy ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y)) x)
  have hZ' : ∀ n ∈ commutator J, (∀ m ∈ commutator J, n * m = m * n) → n = 1 := by
    intro n hn' hc
    have : eT ⟨n, hn'⟩ ∈ Subgroup.center (commutator (ReeTag.G2.reeGamma k b)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨m, rfl⟩ := eT.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc m.1 m.2).symm
    rw [hZc, Subgroup.mem_bot] at this
    have h1 : (⟨n, hn'⟩ : commutator J) = 1 := eT.injective (this.trans (map_one eT).symm)
    exact congrArg Subtype.val h1
  set T : Subgroup Γ := (commutator J).map J.subtype with hT
  let eTT : commutator (ReeTag.G2.reeGamma k b) ≃* T :=
    eT.symm.trans ((commutator J).equivMapOfInjective J.subtype J.subtype_injective)
  have hTq : CFSG.IsQuasisimple T := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv eTT ?_
    refine isQuasisimple_of_simple_nonabelian fun hc => ?_
    obtain ⟨x, y, hxy⟩ := hn
    exact hxy (hc x y)
  have hTJ : ∀ t ∈ T, δ t = t := by
    rintro _ ⟨t', -, rfl⟩
    exact t'.2
  have hTn : ∀ f : Γ, δ f = f → ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    rintro f hf _ ⟨t', ht', rfl⟩
    refine ⟨(⟨f, hf⟩ : J) * t' * (⟨f, hf⟩ : J)⁻¹, ?_, rfl⟩
    exact (inferInstance : (commutator J).Normal).conj_mem t' ht' _
  have hCJ : ∀ z : Γ, δ z = z → (∀ t ∈ T, z * t = t * z) → z = 1 := by
    intro z hz hzc
    have h1 := eq_one_of_centralizes_commutator (G := J) hZJ hZ' (z := ⟨z, hz⟩)
      (fun t' ht' => Subtype.ext (hzc t'.1 ⟨t', ht', rfl⟩))
    exact congrArg Subtype.val h1
  have hcardT : Nat.card T = Nat.card (commutator (ReeTag.G2.reeGamma k b)) :=
    (Nat.card_congr eTT.toEquiv).symm
  have hJcard : Nat.card J = Nat.card (ReeTag.G2.reeGamma k b) := Nat.card_congr eC.toEquiv
  have hTp : ¬ Nat.Coprime p (Nat.card T) := by
    suffices hd : p ∣ Nat.card T from fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hd
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
      have hΓk : Nat.card (ReeTag.G2.reeGamma k 0) = 1512 := by
        rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq (a := 0) hkcard]
        norm_num
      rw [hΓk] at hJcard
      rw [hJcard] at hdvd
      have h3 : (1512 : ℕ) = 3 * 504 := by norm_num
      rw [h3] at hdvd
      rw [hcardT, h504]
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h) (by omega)
      · exact h
    · have htop := hperf hb1
      have : Nat.card (commutator (ReeTag.G2.reeGamma k b)) =
          Nat.card (ReeTag.G2.reeGamma k b) := by
        rw [Nat.card_congr (MulEquiv.subgroupCongr htop).toEquiv, Subgroup.card_top]
      rw [hcardT, this, ← hJcard]
      exact hdvd
  have hinner : ∀ ρ : k ≃+* k, ReeTag.G2.reeGammaFieldAut k b ρ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma k b) → ρ = 1 := by
    intro ρ hρ
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      exact CFSG.RankThree.Chevalley.ringEquiv_eq_one_of_card_eq_prime Nat.prime_three
        (by simpa using hkcard) ρ
    · obtain ⟨-, -, -, ⟨R, χ, -, hsec, -⟩, -, -⟩ :=
        small_Ree_outer_three_kernel_field_complement b hb1 k hkcard
      have h1 := hsec ρ
      rw [(QuotientGroup.eq_one_iff _).2 hρ, map_one] at h1
      exact h1.symm
  have hres : ∀ (x : Γ) (τ : K ≃+* K), δ x = x →
      (∀ j : Γ, δ j = j → x * ReeTag.G2.reeGammaFieldAutHom K a τ j * x⁻¹ = j) →
      τ ∈ Subgroup.zpowers σ := fun x τ hx hfix =>
    CFSG.SignalizerFunctorTheorem.CatalogBridge.ree_zpowers_of_inner_on_subfield σ hfixed hinner x
      τ hx hfix
  have hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : K ≃+* K),
      α = MulAut.conj x * (ReeTag.G2.reeGammaFieldAutHom K a) τ := fun α => by
    obtain ⟨x, τ, h⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.smallReeOuterIsField a ha K hK α
    exact ⟨x, τ, h⟩
  exact fieldCoreAt_of_normalForm hinj
    (fun u v => CFSG.ComponentClassification.UnbalancedCatalog.ringAut_commute u v)
    (ReeTag.G2.reeGammaFieldAutHom K a) hNF (σ := σ) hδp hTJ hTn hTq hTp hCJ hres

end ReeG2

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
