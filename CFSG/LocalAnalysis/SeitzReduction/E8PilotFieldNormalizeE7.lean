module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeExists
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance e8PilotFieldNormalizeE7NeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem mulAut_congr_apply_apply' {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (f : MulAut X)
    (y : Y) : MulAut.congr φ f y = φ (f (φ.symm y)) :=
  rfl

theorem fixedSubgroup_mulAut_conj' {X : Type*} [Group X] (z : X) :
    fixedSubgroup (MulAut.conj z) = centralizer ({z} : Set X) := by
  ext y
  change z * y * z⁻¹ = y ↔ y ∈ centralizer ({z} : Set X)
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

section Basic


variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem commutator_top_adjointGroup_E7 :
    ⁅(⊤ : Subgroup (adjointGroup .E7 k)), (⊤ : Subgroup (adjointGroup .E7 k))⁆ = ⊤ := by
  have h0 : ⁅(⊤ : Subgroup (e7Levi k)), ⊤⁆ = ⊤ :=
    (isQuasisimple_e7Levi (K := k)).1.commutator_eq_top
  have h := congrArg (fun H : Subgroup (e7Levi k) => H.map (e7LeviEquiv k).toMonoidHom) h0
  simp only [Subgroup.map_commutator] at h
  rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 (e7LeviEquiv k).surjective] at h

theorem isQuasisimple_adjointGroup_E7 : CFSG.IsQuasisimple (adjointGroup .E7 k) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (e7LeviEquiv k) isQuasisimple_e7Levi

variable {k}

omit
  [Finite k] [CharP k 2] in
theorem adjointBaseChangeE7_injective {K : Type} [Field K] (ι : k →+* K) :
    Function.Injective (adjointBaseChangeE7 ι) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))

end Basic

section Extension


variable {k K : Type} [Field k] [Finite k] [CharP k 2] [Field K] [Finite K] [CharP K 2]

theorem exists_mulAut_adjointBaseChangeE7_comm (ι : k →+* K) (δ : MulAut (adjointGroup .E7 k)) :
    ∃ δ' : MulAut (adjointGroup .E7 K),
      ∀ g, δ' (adjointBaseChangeE7 ι g) = adjointBaseChangeE7 ι (δ g) := by
  obtain ⟨f₀, hf₀, hk⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  obtain ⟨hNF, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf₀ k hk .E7 (Or.inl rfl)
  obtain ⟨⟨g, ρ⟩, hgρ, -⟩ := hNF δ
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq ι ρ
  refine ⟨MulAut.conj (adjointBaseChangeE7 ι g) * entrywiseAdjointAut .E7 ρ', fun h => ?_⟩
  apply Subtype.ext
  have hcomp : (ρ'.toRingHom).comp ι = ι.comp ρ.toRingHom := RingHom.ext fun c => hρ' c
  have h1 : Units.map (entrywiseHom ρ'.toRingHom) (baseChangeGL ι (h : ModGL .E7 k)) =
      baseChangeGL ι (Units.map (entrywiseHom ρ.toRingHom) (h : ModGL .E7 k)) := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      F4Pilot.baseChangeGL_baseChangeGL, F4Pilot.baseChangeGL_baseChangeGL, hcomp]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_entrywiseAdjointAut, coe_adjointBaseChangeE7]
  rw [hgρ h, map_mul, map_mul, map_inv, h1]

omit [Finite k] [CharP k 2] [CharP K 2] in
theorem eqLocus_entrywiseAdjointAut_E7 [CharP K 2] (ι : k →+* K) {σ : K ≃+* K}
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) :
    (entrywiseAdjointAut .E7 σ).toMonoidHom.eqLocus (MonoidHom.id _) =
      (adjointBaseChangeE7 ι).range := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  have h1 : ((entrywiseAdjointAut .E7 σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup .E7 K).subtype = entrywiseFixedGroup .E7 σ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine mem_entrywiseFixedGroup.2 ⟨x.2, ?_⟩
      have hx' : (entrywiseAdjointAut .E7 σ x : ModGL .E7 K) = x := congrArg Subtype.val hx
      rwa [coe_entrywiseAdjointAut] at hx'
    · intro hg
      obtain ⟨hgC, hgσ⟩ := mem_entrywiseFixedGroup.1 hg
      refine ⟨⟨g, hgC⟩, ?_, rfl⟩
      change entrywiseAdjointAut .E7 σ ⟨g, hgC⟩ = ⟨g, hgC⟩
      exact Subtype.ext (by rw [coe_entrywiseAdjointAut]; exact hgσ)
  have h2 : (adjointBaseChangeE7 ι).range.map (adjointGroup .E7 K).subtype =
      (adjointGroup .E7 k).map (baseChangeGL ι) := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hrange : Set.range (fixSubfield σ).subtype = Set.range ι := by
    ext z
    rw [← F4Pilot.apply_eq_iff_mem_range_fixSubfield_subtype, hfix]
  rw [h1, h2, entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (ringChar.eq K 2) σ, fixedFieldImage,
    map_adjointGroup_baseChangeGL_eq_of_range_eq (fixSubfield σ).subtype ι hrange]

omit [CharP k 2] [CharP K 2]
  in
theorem natCard_adjointGroup_E7_lt (ι : k →+* K) {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) :
    Nat.card (adjointGroup .E7 k) < Nat.card (adjointGroup .E7 K) := by
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  set α : Fin (Tag.rank .E7) → ℤ := Pi.single 0 1 with hα
  have hns : (⟨pinnedX .E7 K α c, pinnedX_mem_adjointGroup α c⟩ : adjointGroup .E7 K) ∉
      Set.range (adjointBaseChangeE7 ι) := by
    rintro ⟨g, hg⟩
    have hσι : (σ : K →+* K).comp ι = ι := RingHom.ext fun a => (hfix (ι a)).2 ⟨a, rfl⟩
    have h1 : baseChangeGL (σ : K →+* K) (baseChangeGL ι (g : ModGL .E7 k)) =
        baseChangeGL ι (g : ModGL .E7 k) := by
      rw [F4Pilot.baseChangeGL_baseChangeGL, hσι]
    have h2 : baseChangeGL ι (g : ModGL .E7 k) = pinnedX .E7 K α c := congrArg Subtype.val hg
    rw [h2, baseChangeGL_pinnedX] at h1
    exact hc (pinnedX_injective (τ := .E7) (R := K) α h1)
  have : Fintype (adjointGroup .E7 k) := Fintype.ofFinite _
  have : Fintype (adjointGroup .E7 K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem _ (adjointBaseChangeE7_injective ι) hns

end Extension

section Descent


variable {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit) in
theorem exists_conj_eq_entrywise_E7 {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {β : MulAut (adjointGroup .E7 K)} (hβ : β * β = 1)
    (hD : CFSG.IsQuasisimple ((perfectCore (fixedSubgroup β)).subgroupOf (fixedSubgroup β)))
    (hlt : Nat.card (perfectCore (fixedSubgroup β)) < Nat.card (adjointGroup .E7 K)) :
    ∃ ψ : MulAut (adjointGroup .E7 K), ψ * β * ψ⁻¹ = entrywiseAdjointAut .E7 σ := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hZ : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  have hnotinner : β ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
    rintro ⟨z, rfl⟩
    have hzz : z * z = 1 := by
      have h2 : z * z ∈ center (adjointGroup .E7 K) := by
        rw [mem_center_iff]
        intro y
        have h3 := DFunLike.congr_fun hβ y
        rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.one_apply] at h3
        calc y * (z * z) = z * (z * y * z⁻¹) * z⁻¹ * (z * z) := by rw [h3]
          _ = z * z * y := by group
      rw [hZ, mem_bot] at h2
      exact h2
    by_cases hz1 : z = 1
    · subst hz1
      have htop : fixedSubgroup (MulAut.conj (1 : adjointGroup .E7 K)) = ⊤ := by
        rw [map_one]
        exact eq_top_iff.2 fun y _ => rfl
      rw [htop, CFSG.Quasithin.perfectCore_eq_self_of_perfect (commutator_top_adjointGroup_E7 K),
        Subgroup.card_top] at hlt
      exact lt_irrefl _ hlt
    · have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hzz]) hz1
      have hcomp : IsComponent ((perfectCore (fixedSubgroup (MulAut.conj z))).subgroupOf
          (fixedSubgroup (MulAut.conj z))) :=
        ⟨hD, (CFSG.Quasithin.perfectCore_normal _).isSubnormal⟩
      let Ψ : fixedSubgroup (MulAut.conj z) ≃* centralizer ({z} : Set (adjointGroup .E7 K)) :=
        MulEquiv.subgroupCongr (fixedSubgroup_mulAut_conj' z)
      exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_adjointGroup
        hf hK z hzord _ (CFSG.ComponentClassification.CatLeaf.isComponent_map_mulEquiv Ψ hcomp)
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  obtain ⟨⟨g, σ'⟩, hgσ, -⟩ := hNF β
  have hΘβ : Θ β = σ' := hΘ β g σ' hgσ
  have hΘ1 : Θ β ≠ 1 := fun h1 => hnotinner (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  have hβ2 : β ^ 2 = 1 := by rw [sq]; exact hβ
  obtain ⟨hfe, hσc⟩ := (hinv β hβ2).resolve_left hΘ1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  obtain ⟨-, hσpow⟩ := LinearFlag.even_and_eq_pow_of_involution hf hK hσ1 hσσ
  have hσ'σ : σ' = σ := RingEquiv.ext fun c => by rw [← hΘβ, hσc, hσpow]
  obtain ⟨e', he'⟩ := hfe
  have he1 : 1 ≤ e' := by omega
  have hK' : Nat.card K = 2 ^ (2 * e') := by rw [hK, he', two_mul]
  have hσe : ∀ c, σ.toRingHom c = c ^ 2 ^ e' := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσpow, he',
      show (e' + e') / 2 = e' by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσe
  obtain ⟨β', -, hdesc⟩ := hQ1 .E7
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hαform : ∀ u, (β u : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 (fun _ => 1) *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) * (rootDiagUnit .E7 fun _ => 1)⁻¹ *
        (g : ModGL .E7 K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin (Tag.rank .E7) → Kˣ) from rfl, rootDiagUnit_one,
      mul_one, inv_one, mul_one, ← hσ'σ]
    exact hgσ u
  obtain ⟨ψ, hψ, -⟩ := hdα β hαform hβ
  exact ⟨ψ, MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_entrywiseAdjointAut])⟩

theorem exists_mulEquiv_adjointBaseChangeE7_eq {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type} [Group M]
    (ψ : adjointGroup .E7 K ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (ε : adjointGroup .E7 k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : adjointGroup .E7 K ≃* M, ∀ g, ψ' (adjointBaseChangeE7 ι g) = ε g := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have : Finite M := Finite.of_equiv _ ψ.toEquiv
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  set χ : M ≃* adjointGroup .E7 K := ψ.symm with hχ
  set β₀ := MulAut.congr χ θ with hβ₀def
  have hβ₀ : β₀ * β₀ = 1 := by rw [hβ₀def, ← map_mul, hθ, map_one]
  have hP : perfectCore (fixedSubgroup β₀) = ε.range.map χ.toMonoidHom := by
    rw [hβ₀def, CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr,
      ← CFSG.Quasithin.map_perfectCore, hεr]
    rfl
  have hinj : Function.Injective (χ.toMonoidHom.comp ε) := χ.injective.comp hε
  have hPr : ε.range.map χ.toMonoidHom = (χ.toMonoidHom.comp ε).range := by
    rw [MonoidHom.range_comp]
  let eP : adjointGroup .E7 k ≃* perfectCore (fixedSubgroup β₀) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (hP.trans hPr).symm)
  have hD : CFSG.IsQuasisimple ((perfectCore (fixedSubgroup β₀)).subgroupOf (fixedSubgroup β₀)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (eP.trans (subgroupOfEquivOfLe (CFSG.Quasithin.perfectCore_le _)).symm)
      (isQuasisimple_adjointGroup_E7 k)
  have hlt : Nat.card (perfectCore (fixedSubgroup β₀)) < Nat.card (adjointGroup .E7 K) := by
    rw [← Nat.card_congr eP.toEquiv]
    exact natCard_adjointGroup_E7_lt ι hσ1 hfix
  obtain ⟨ψ₀, hψ₀⟩ := exists_conj_eq_entrywise_E7 hσ hβ₀ hD hlt
  set ψ₁ : adjointGroup .E7 K ≃* M := ψ₀.symm.trans χ.symm with hψ₁
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (entrywiseAdjointAut .E7 σ x) := by
    intro x
    have h1 : β₀ = ψ₀⁻¹ * entrywiseAdjointAut .E7 σ * ψ₀ := by rw [← hψ₀]; group
    have h2 : θ (χ.symm (ψ₀.symm x)) = χ.symm (β₀ (ψ₀.symm x)) := by
      rw [hβ₀def, mulAut_congr_apply_apply', MulEquiv.symm_apply_apply]
    rw [hψ₁, MulEquiv.trans_apply, MulEquiv.trans_apply, h2, h1, MulAut.mul_apply,
      MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M) =
      (adjointBaseChangeE7 ι).range.map ψ₁.toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply, ← eqLocus_entrywiseAdjointAut_E7 ι hfix]
    change θ (ψ₁ x) = ψ₁ x ↔ entrywiseAdjointAut .E7 σ x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have hperf : ⁅(adjointBaseChangeE7 ι).range.map ψ₁.toMonoidHom,
      (adjointBaseChangeE7 ι).range.map ψ₁.toMonoidHom⁆ =
        (adjointBaseChangeE7 ι).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator,
      commutator_top_adjointGroup_E7 k]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp (adjointBaseChangeE7 ι)).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp (adjointBaseChangeE7 ι)) :=
    ψ₁.injective.comp (adjointBaseChangeE7_injective ι)
  set δ : MulAut (adjointGroup .E7 k) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδdef
  have hδ : ∀ g, ψ₁ (adjointBaseChangeE7 ι (δ g)) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := exists_mulAut_adjointBaseChangeE7_comm ι δ
  exact ⟨δ'.trans ψ₁, fun g => by rw [MulEquiv.trans_apply, hδ', hδ]⟩

theorem exists_mulEquiv_e7LeviBaseChange_eq {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type} [Group M] (ψ : e7Levi K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (ε : e7Levi k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : e7Levi K ≃* M, ∀ g, ψ' (e7LeviBaseChange ι g) = ε g := by
  set ε₇ : adjointGroup .E7 k →* M := ε.comp (e7LeviEquiv k).symm.toMonoidHom with hε₇def
  have hε₇ : Function.Injective ε₇ := hε.comp (e7LeviEquiv k).symm.injective
  have hε₇r : ε₇.range = ε.range := by
    rw [hε₇def, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (e7LeviEquiv k).symm.surjective, ← MonoidHom.range_eq_map]
  obtain ⟨ψ₇, hψ₇⟩ := exists_mulEquiv_adjointBaseChangeE7_eq ι hσ hfix
    ((e7LeviEquiv K).symm.trans ψ) hθ ε₇ hε₇ (hε₇r.trans hεr)
  refine ⟨(e7LeviEquiv K).trans ψ₇, fun g => ?_⟩
  rw [MulEquiv.trans_apply, e7LeviEquiv_baseChange, hψ₇, hε₇def, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

end Descent

end CFSG.SeitzReduction.E8Pilot
