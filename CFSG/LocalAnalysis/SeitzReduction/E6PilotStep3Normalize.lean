module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLeviTori

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

theorem exists_forall_eq_pow_two_pow {k : Type} [Field k] [Finite k] [CharP k 2]
    (σ : k ≃+* k) : ∃ i : ℕ, ∀ x, σ x = x ^ 2 ^ i := by
  let _ : Algebra (ZMod 2) k := ZMod.algebra k 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ' : k ≃ₐ[ZMod 2] k := AlgEquiv.ofRingEquiv (f := σ) (fun x => by
    have h : (σ.toRingHom.comp (algebraMap (ZMod 2) k) : ZMod 2 →+* k) =
        algebraMap (ZMod 2) k := RingHom.ext_zmod _ _
    exact congrArg (fun φ : ZMod 2 →+* k => φ x) h)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 k σ'
  refine ⟨i, fun x => ?_⟩
  have := hi x
  rw [Nat.card_zmod] at this
  exact this

section Extend


theorem exists_mulAut_fixedFieldInclusion_comm {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2]
    (σ : K₂ ≃+* K₂) [Finite (fixSubfield σ)] [CharP (fixSubfield σ) 2]
    (β : MulAut (adjointGroup .E6 (fixSubfield σ))) :
    ∃ βh : MulAut (adjointGroup .E6 K₂),
      ∀ x, βh (fixedFieldInclusion σ x) = fixedFieldInclusion σ (β x) := by
  obtain ⟨g, a, σ₁, ε, hβ⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) (fixSubfield σ)).2.2 β
  obtain ⟨i, hi⟩ := exists_forall_eq_pow_two_pow σ₁
  obtain ⟨σh, hσh⟩ : ∃ σh : K₂ ≃+* K₂, ∀ c, σh c = c ^ 2 ^ i :=
    ⟨iterateFrobeniusEquiv K₂ 2 i, fun c => iterateFrobeniusEquiv_def K₂ 2 i c⟩
  have hring : ((fixSubfield σ).subtype).comp σ₁.toRingHom =
      σh.toRingHom.comp (fixSubfield σ).subtype :=
    RingHom.ext fun c => by
      change ((σ₁ c : fixSubfield σ) : K₂) = σh (c : K₂)
      rw [hσh, hi]
      rfl
  set a' : Fin (Tag.rank .E6) → K₂ˣ :=
    fun j => Units.map ((fixSubfield σ).subtype : fixSubfield σ →+* K₂).toMonoidHom (a j) with ha'
  refine ⟨MulAut.conj (fixedFieldInclusion σ g) * exactNormalAut .E6 K₂ a' σh ε,
    fun x => Subtype.ext ?_⟩
  have hent : ∀ y : ModGL .E6 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype (Units.map (entrywiseHom σ₁.toRingHom) y) =
        Units.map (entrywiseHom σh.toRingHom) (baseChangeGL (fixSubfield σ).subtype y) := by
    intro y
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hring]
  have hQ : baseChangeGL (fixSubfield σ).subtype (exactQ .E6 (fixSubfield σ) ε) =
      exactQ .E6 K₂ ε := by
    change baseChangeGL (fixSubfield σ).subtype
        ((diagramMap .E6 (fixSubfield σ) : ModGL Tag.E6 (fixSubfield σ)) ^ (ε : ℕ)) =
      (diagramMap .E6 K₂ : ModGL Tag.E6 K₂) ^ (ε : ℕ)
    rw [map_pow, baseChangeGL_diagramMap]
  have hd : baseChangeGL (fixSubfield σ).subtype (rootDiagUnit .E6 a) = rootDiagUnit .E6 a' :=
    F4Pilot.baseChangeGL_rootDiagUnit_eq_map _ a
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, coe_fixedFieldInclusion, coe_fixedFieldInclusion,
    coe_fixedFieldInclusion, hβ x]
  simp only [map_mul, map_inv, hd, hQ, hent, mul_assoc]

end Extend

section Normalize


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mulEquiv_quotient_center_comp_fixedFieldInclusion (hset : StandardSetting G L)
    {K₂ : Type} [Field K₂] [Finite K₂] [CharP K₂ 2] {σ : K₂ ≃+* K₂} {f : ℕ}
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hk : Nat.card (fixSubfield σ) = 2 ^ f) (e : L ≃* adjointGroup .E6 (fixSubfield σ)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup .E6 K₂) (htM : t ∈ normalizer (M : Set G)) :
    ∃ Φ : adjointGroup .E6 K₂ ≃* M ⧸ center M, ∀ (x : adjointGroup .E6 (fixSubfield σ)) (m : M),
      (m : G) = ((e.symm x : L) : G) → Φ (fixedFieldInclusion σ x) = QuotientGroup.mk m := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP (fixSubfield σ) 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have : Finite (adjointGroup .E6 (fixSubfield σ)) := by
    have : Finite (ModGL Tag.E6 (fixSubfield σ)) := finite_modGL
    infer_instance
  obtain ⟨⟨σ', hσ'2, -, hσ'c, φ, hφ⟩, hML⟩ :=
    inf_centralizer_eq_of_mem_normalizer_E6_cover hset hk e ht hKt hMp hZ hK₂ eM htM
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ'c, hσ]
  rw [hσσ'] at hφ hσ'2
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [← RingAut.mul_apply, ← sq, hσ'2]
    rfl
  have htC : t ∈ centralizer (L : Set G) :=
    (hKt ▸ mem_zpowers t : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  have hLM : L ≤ M := hML ▸ inf_le_left
  set π₀ : M →* adjointGroup .E6 K₂ := eM.toMonoidHom.comp (QuotientGroup.mk' (center M))
    with hπ₀
  have hfixα : ((centralizer ({t} : Set G)).subgroupOf M).map π₀ =
      fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) :=
    map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hfixσ : fixSubgroup (entrywiseAdjointAut .E6 σ) = (fixedFieldInclusion σ).range := by
    rw [fixSubgroup_entrywiseAdjointAut_eq_E6 σ hσσ]
    ext g
    rw [mem_subgroupOf, mem_fixedFieldImage_iff_exists, MonoidHom.mem_range]
  have hφfix : (fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)).map φ.toMonoidHom =
      (fixedFieldInclusion σ).range := by
    rw [map_fixSubgroup_conj, hφ, hfixσ]
  have hmemM : ∀ x : adjointGroup .E6 (fixSubfield σ), ((e.symm x : L) : G) ∈ M :=
    fun x => hLM (e.symm x).2
  set j : adjointGroup .E6 (fixSubfield σ) →* M :=
    (L.subtype.comp e.symm.toMonoidHom).codRestrict M hmemM with hj
  have hjG : ∀ x, ((j x : M) : G) = ((e.symm x : L) : G) := fun x => rfl
  have hjfix : ∀ x, φ (π₀ (j x)) ∈ (fixedFieldInclusion σ).range := by
    intro x
    rw [← hφfix]
    refine ⟨π₀ (j x), ?_, rfl⟩
    rw [← hfixα]
    have hjt : j x ∈ (centralizer ({t} : Set G)).subgroupOf M := by
      rw [mem_subgroupOf, mem_centralizer_singleton_iff, hjG]
      exact mem_centralizer_iff.1 htC _ (e.symm x).2
    exact ⟨j x, hjt, rfl⟩
  set ιe := MonoidHom.ofInjective (fixedFieldInclusion_injective (τ := .E6) σ) with hιe
  set β₀ : adjointGroup .E6 (fixSubfield σ) →* adjointGroup .E6 (fixSubfield σ) :=
    ιe.symm.toMonoidHom.comp (((φ.toMonoidHom.comp π₀).comp j).codRestrict _ hjfix) with hβ₀def
  have hβ₀ : ∀ x, fixedFieldInclusion σ (β₀ x) = φ (π₀ (j x)) := by
    intro x
    have h1 := ιe.apply_symm_apply ⟨φ (π₀ (j x)), hjfix x⟩
    exact congrArg Subtype.val h1
  have hβ₀inj : Function.Injective β₀ := by
    intro x y hxy
    have h1 : φ (π₀ (j x)) = φ (π₀ (j y)) := by rw [← hβ₀, ← hβ₀, hxy]
    have h2 : π₀ (j x) = π₀ (j y) := φ.injective h1
    have h3 : j (x * y⁻¹) ∈ center M := by
      rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
      have h4 : π₀ (j (x * y⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_inv, h2, mul_inv_cancel]
      exact eM.injective (h4.trans (map_one eM).symm)
    have h5 : ((j (x * y⁻¹) : M) : G) ∈
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      have hc1 : ((j (x * y⁻¹) : M) : G) ∈ centralizer (L : Set G) :=
        mem_centralizer_iff.2 fun l hl => by
          have h6 := mem_center_iff.1 h3 ⟨l, hLM hl⟩
          exact congrArg Subtype.val h6
      have hc2 : ((j (x * y⁻¹) : M) : G) ∈ centralizer ({t} : Set G) := by
        rw [mem_centralizer_singleton_iff, hjG]
        exact mem_centralizer_iff.1 htC _ (e.symm (x * y⁻¹)).2
      exact ⟨hc1, hc2⟩
    rw [hKt] at h5
    have hodd := odd_orderOf_of_mem_center hZ h3
    have hdvd : orderOf (j (x * y⁻¹)) ∣ 2 := by
      rw [← Subgroup.orderOf_coe, ← ht]
      exact orderOf_dvd_of_mem_zpowers h5
    have h7 : j (x * y⁻¹) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h8 | h8
      · exact orderOf_eq_one_iff.1 h8
      · rw [h8] at hodd
        exact absurd hodd (by decide)
    have h9 : x * y⁻¹ = 1 := by
      apply e.symm.injective
      apply Subtype.ext
      rw [map_one]
      exact congrArg (fun z : M => (z : G)) h7
    exact mul_inv_eq_one.1 h9
  set β : MulAut (adjointGroup .E6 (fixSubfield σ)) :=
    MulEquiv.ofBijective β₀ (Finite.injective_iff_bijective.1 hβ₀inj) with hβdef
  obtain ⟨βh, hβh⟩ := exists_mulAut_fixedFieldInclusion_comm σ β
  refine ⟨(βh.trans φ.symm).trans eM.symm, fun x m hm => ?_⟩
  have hmj : m = j x := Subtype.ext hm
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hβh]
  change eM.symm (φ.symm (fixedFieldInclusion σ (β₀ x))) = _
  rw [hβ₀, MulEquiv.symm_apply_apply, hmj]
  change eM.symm (eM (QuotientGroup.mk' (center M) (j x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Normalize

end CFSG.SeitzReduction.E6Pilot
