module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GTwE6Fix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.RecipeExcLang CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley

section TwE6


variable {K : Type} [Field K] [Finite K]

theorem twE6_fixGeom_model {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (κ : K ≃+* K) (σ₀ : fixSubfield κ ≃+* fixSubfield κ),
      Nat.card (fixSubfield κ) = (2 ^ (n / p)) ^ 2 ∧ (∀ c, σ₀ c = c ^ (2 ^ (n / p))) ∧
      IsSimpleGroup (LargeEvenCenterQuot
        (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)) ∧
      (∃ a b : LargeEvenCenterQuot
        (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom), a * b ≠ b * a) ∧
      ∃ θ₀ : ggFixDer f ≃* LargeEvenCenterQuot
          (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom),
        GGFixGeom (markIDImage (IsRoot TwistTag.E6.tag) K
            (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) f
          (markIDImage (IsRoot TwistTag.E6.tag) (fixSubfield κ)
            (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)) θ₀ := by
  classical
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  set Ψ := MulAut.congr (centerQuotEquivOfBot hZ) with hΨ
  obtain ⟨-, -, -, -, -, -, -, hNF, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hΘf : ∀ δ : RingAut K, Θ (fieldActor σ δ) = δ := fun δ =>
    hΘ _ 1 1 δ (by rw [map_one, map_one, one_mul, one_mul])
  have hinj : Function.Injective (fieldActorHom (t := TwistTag.E6) σ) := fun δ δ' h => by
    rw [← hΘf δ, ← hΘf δ']
    exact congrArg Θ h
  obtain ⟨σ', hσ'⟩ := hf
  have hfΨ : Ψ f = fieldActor σ σ' := by
    refine MulEquiv.ext fun h => ?_
    have h1 := congr_centerQuotEquivOfBot_mk hZ f h
    have h2 := hσ' h (fieldActor σ σ' h) (by beta_reduce; rw [coe_fieldActor]; rfl)
    exact congrArg (centerQuotEquivOfBot hZ) (h1.symm.trans h2)
  have hσ'p : orderOf σ' = p := by
    rw [← orderOf_injective _ hinj σ', fieldActorHom_apply, ← hfΨ, MulEquiv.orderOf_eq, hord]
  have hK2n : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, -⟩ := SteinbergBT.card_fixSubfield (p := 2) (f := 2 * n) Nat.prime_two
    (by omega) hK2n σ'
  rw [hσ'p] at hdvd
  have hpn : p ∣ n := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hdvd
  refine ⟨hpn, ?_⟩
  obtain ⟨d, hd⟩ := hpn
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      omega
    · exact h0
  have hnd : n / p = d := by rw [hd, Nat.mul_div_cancel_left d hp.pos]
  rw [hnd]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hn3 : 3 ≤ n := by
    rw [hd]
    exact le_trans hp3 (Nat.le_mul_of_pos_right p hd1)
  have hq3 : 3 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ n by omega))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card]; exact hK2n)
  have hK2dm : Nat.card K = 2 ^ (2 * d * p) := by
    rw [hK2n, hd]
    ring_nf
  have hpowK : ∀ c : K, c ^ 2 ^ (2 * d * p) = c := fun c => by
    rw [← hK2dm, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  set κ : K ≃+* K := iterateFrobeniusEquiv K 2 (2 * d) with hκdef
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * d) := fun c => by
    rw [hκdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  set ε : K ≃+* K := iterateFrobeniusEquiv K 2 (d * (p + 1)) with hεdef
  have hε : ∀ c, ε c = c ^ 2 ^ (d * (p + 1)) := fun c => by
    rw [hεdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσdp : ∀ c, σ c = c ^ 2 ^ (d * p) := fun c => by rw [hσ, hd, mul_comm]
  set σ₀ : fixSubfield κ ≃+* fixSubfield κ := iterateFrobeniusEquiv (fixSubfield κ) 2 d
    with hσ₀def
  have hσ₀' : ∀ c, σ₀ c = c ^ (2 ^ d) := fun c => by
    rw [hσ₀def, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ 2 ^ d := fun c => by
    rw [hσ₀' c, SubmonoidClass.coe_pow]
  obtain ⟨-, hκcard, hJle, hδord, hder, hJs, hJna, -, -, -, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd1
      hp3 (hp.odd_of_ne_two hp2) K hK2dm κ hκ σ hσdp σ₀ hσ₀ ε hε
  have hk₀ : Nat.card (fixSubfield κ) = (2 ^ d) ^ 2 := by rw [hκcard, ← pow_mul, mul_comm]
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  have hεp : orderOf ε = p := by rw [← orderOf_injective _ hinj ε, fieldActorHom_apply, hδord]
  haveI : IsCyclic (K ≃+* K) := FP.isCyclic_ringEquiv K
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun g : K ≃+* K => (g : K → K)) DFunLike.coe_injective
  have hzp : Subgroup.zpowers σ' = Subgroup.zpowers ε := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hσ'p, hεp]
  have hzpA : Subgroup.zpowers (Ψ f) = Subgroup.zpowers δ := by
    rw [hfΨ, hδdef, ← fieldActorHom_apply, ← fieldActorHom_apply, ← MonoidHom.map_zpowers,
      ← MonoidHom.map_zpowers, hzp]
  have hδmem : δ ∈ Subgroup.zpowers (Ψ f) := by
    rw [hzpA]
    exact Subgroup.mem_zpowers δ
  have hcommδ : ∀ Φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      Φ * Ψ f = Ψ f * Φ → Φ * δ = δ * Φ := by
    intro Φ hΦ
    have hle : Subgroup.zpowers (Ψ f) ≤ Subgroup.centralizer {Φ} :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hΦ.symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hδmem)).symm
  have hmapS : (ggFixSub f).map (centerQuotEquivOfBot hZ).toMonoidHom = ggFixSub (Ψ f) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : f g = g := mem_ggFixSub.1 hg
      rw [mem_ggFixSub]
      simp only [hΨ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.coe_toMonoidHom, hg']
    · intro hx
      refine ⟨(centerQuotEquivOfBot hZ).symm x, ?_, (centerQuotEquivOfBot hZ).apply_symm_apply x⟩
      rw [mem_ggFixSub] at hx
      refine mem_ggFixSub.2 ?_
      apply (centerQuotEquivOfBot hZ).injective
      rw [MulEquiv.apply_symm_apply]
      simp only [hΨ, MulAut.congr_apply, MulEquiv.trans_apply] at hx
      exact hx
  have hmapK : (ggFixDer f).map (centerQuotEquivOfBot hZ).toMonoidHom =
      (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    have hδeq : ggFixSub δ = MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id _) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [← hder, ← hδeq, ← ggFixSub_eq_of_zpowers_eq hzpA, ← hmapS]
    exact Subgroup.map_commutator _ _ _
  have hZ₀ := exceptional_fixed_center_trivial TwistTag.E6 (fixSubfield κ) σ₀
  let ιJ : graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom ≃*
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (fixSubfield κ).subtype)
      (baseChangeGL_injective _)
  let jJ : (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
        subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ :=
    Subgroup.subgroupOfEquivOfLe hJle
  let kK : ggFixDer f ≃* (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    ((ggFixDer f).equivMapOfInjective (centerQuotEquivOfBot hZ).toMonoidHom
      (centerQuotEquivOfBot hZ).injective).trans (MulEquiv.subgroupCongr hmapK)
  let θ₀ : ggFixDer f ≃* LargeEvenCenterQuot
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom) :=
    ((kK.trans jJ).trans ιJ.symm).trans (centerQuotEquivOfBot hZ₀).symm
  have hθ₀ : ∀ x : ggFixDer f, baseChangeGL (fixSubfield κ).subtype
      ((centerQuotEquivOfBot hZ₀ (θ₀ x) :
        graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom) :
          ModGL TwistTag.E6.tag (fixSubfield κ)) =
        ((centerQuotEquivOfBot hZ (x : LargeEvenCenterQuot
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) := by
    intro x
    have h1 : centerQuotEquivOfBot hZ₀ (θ₀ x) = ιJ.symm (jJ (kK x)) := by
      simp only [θ₀, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [h1]
    have h2 := congrArg Subtype.val (ιJ.apply_symm_apply (jJ (kK x)))
    exact h2
  haveI : IsSimpleGroup (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) := hJs
  let eR : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom) ≃*
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ :=
    (centerQuotEquivOfBot hZ₀).trans ιJ
  have hs₀ : IsSimpleGroup (LargeEvenCenterQuot
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom)) := eR.isSimpleGroup
  have hna₀ : ∃ a b : LargeEvenCenterQuot
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) σ₀.toRingHom), a * b ≠ b * a := by
    simp only [not_forall] at hJna
    obtain ⟨a, b, hab⟩ := hJna
    refine ⟨eR.symm a, eR.symm b, fun h => hab ?_⟩
    have h' := congrArg eR h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have hcommσ : (fixSubfield κ).subtype.comp σ₀.toRingHom =
      σ.toRingHom.comp (fixSubfield κ).subtype := by
    refine RingHom.ext fun c => ?_
    simp only [RingHom.comp_apply, Subfield.coe_subtype, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [hσ₀ c, hσdp]
    have hc : (c : K) ^ 2 ^ (2 * d) = c := by
      rw [← hκ]
      exact (mem_fixSubfield κ).1 c.2
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    have he : 2 ^ (d * p) = (2 ^ (2 * d)) ^ j * 2 ^ d := by
      rw [hj, ← pow_mul, ← pow_add]
      ring_nf
    rw [he, pow_mul, pow_pow_eq_self_of_pow_eq hc]
  have hκε : κ = ε * ε := RingEquiv.ext fun c => by
    change κ c = ε (ε c)
    rw [hκ, hε, hε, ← pow_mul, ← pow_add]
    have he : d * (p + 1) + d * (p + 1) = 2 * d * p + 2 * d := by ring
    rw [he, pow_add, pow_mul c (2 ^ (2 * d * p)) (2 ^ (2 * d)), hpowK]
  refine ⟨κ, σ₀, hk₀, hσ₀', hs₀, hna₀, θ₀, ?_, ?_⟩
  ·
    intro φ hφI hφf
    have hΦΘ := twE6_theta_eq_one_of_mem_markID σ Θ hΘ hφI
    obtain ⟨g₁, u, δ', hΦnf⟩ := hNF (Ψ φ)
    have hδ' : δ' = 1 := by
      rw [← hΘ _ g₁ u δ' hΦnf]
      exact hΦΘ
    have hb : IsCompatE6 σ.toRingHom (compatDiag TwistTag.E6 σ.toRingHom u) := fun i =>
      compatDiag_perm u i
    let w : twInndiagGroup K σ := ⟨(g₁ : ModGL TwistTag.E6.tag K) *
        rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u),
      mul_mem (graphFixedRootGroup_le_twInndiag σ g₁.2) (rootDiagUnit_mem_twInndiag hb)⟩
    have hwΦ : twConj K σ w = Ψ φ := by
      rw [hΦnf, hδ', fieldActor_one, mul_one]
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [coe_twConj, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_compatDiagAutHom]
      simp only [w]
      group
    have hwδ : twConj K σ w * δ = δ * twConj K σ w := by
      rw [hwΦ]
      exact hcommδ (Ψ φ) (by rw [← map_mul, ← map_mul, hφf])
    have hwε := twE6_entrywise_eq_of_commute hn hK hσ hq3 ε w hwδ
    have hwκ : Units.map (entrywiseHom κ.toRingHom) (w : ModGL TwistTag.E6.tag K) = w := by
      rw [hκε, units_map_entrywiseHom_mul_ringEquiv, hwε, hwε]
    obtain ⟨w₀, hw₀, hw₀w⟩ := exists_twInndiag_of_fixed hK κ hd1 hk₀ σ₀ hσ₀' hcommσ w.2 hwκ
    refine ⟨(MulAut.congr (centerQuotEquivOfBot hZ₀)).symm
      (twConj (fixSubfield κ) σ₀ ⟨w₀, hw₀⟩), twConj_mem_markID hd1 hk₀ σ₀ hσ₀' ⟨w₀, hw₀⟩,
      fun g hg => ?_⟩
    apply (centerQuotEquivOfBot hZ₀).injective
    apply Subtype.ext
    apply baseChangeGL_injective (fixSubfield κ).subtype
    rw [hθ₀]
    have hR : centerQuotEquivOfBot hZ₀ ((MulAut.congr (centerQuotEquivOfBot hZ₀)).symm
        (twConj (fixSubfield κ) σ₀ ⟨w₀, hw₀⟩) (θ₀ ⟨g, hg⟩)) =
        twConj (fixSubfield κ) σ₀ ⟨w₀, hw₀⟩ (centerQuotEquivOfBot hZ₀ (θ₀ ⟨g, hg⟩)) := by
      simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply]
    rw [hR, coe_twConj, map_mul, map_mul, map_inv, hθ₀ ⟨g, hg⟩, hw₀w]
    have h3 : centerQuotEquivOfBot hZ (φ g) = Ψ φ (centerQuotEquivOfBot hZ g) := by
      simp only [hΨ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change ((centerQuotEquivOfBot hZ (φ g) : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
      ModGL TwistTag.E6.tag K) = _
    rw [h3, ← hwΦ, coe_twConj]
  ·
    intro φ hφI hφf hfix
    have hΦΘ := twE6_theta_eq_one_of_mem_markID σ Θ hΘ hφI
    have hΦδ : Ψ φ * δ = δ * Ψ φ := hcommδ (Ψ φ) (by rw [← map_mul, ← map_mul, hφf])
    have hΦJ : ∀ j : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        j ∈ (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) → Ψ φ j = j := by
      intro j hj
      rw [← hmapK] at hj
      obtain ⟨x, hx, rfl⟩ := hj
      simp only [MulEquiv.coe_toMonoidHom, hΨ, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hfix x hx]
    have hΦN : Ψ φ ∈ Subgroup.centralizer
        (subfieldRootGroupInner TwistTag.E6 σ (fixSubfield κ) σ₀ :
          Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      refine MulEquiv.ext fun x => ?_
      simp only [MulAut.mul_apply, MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv,
        hΦJ j hj]
    have hΦz : Ψ φ ∈ Subgroup.zpowers δ := by
      rw [← hcent]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hΦδ, hΦN⟩
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hΦz
    have hεz : ε ^ z = 1 := by
      have h1 := congrArg Θ hz
      rw [hΦΘ, map_zpow, hδdef, hΘf] at h1
      exact h1
    apply Ψ.injective
    rw [map_one, ← hz, hδdef, ← fieldActorHom_apply, ← map_zpow, hεz, map_one]

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.T156

end
