module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise


section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem twoCentralTwistedFusion_field_E7 {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    F4Pilot.TwoCentralTwistedFusion (entrywiseAdjointAut .E7 σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hk, -, -, hfix, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E7 (Or.inl rfl) he K hK σ hσ
  set η := entrywiseAdjointAut .E7 σ with hηdef
  set F := η.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K)) with hFdef
  set x : K → adjointGroup .E7 K := fun c =>
    ⟨pinnedX .E7 K (highRoot .E7) c, pinnedX_mem_adjointGroup _ _⟩ with hxdef
  have hxadd : ∀ a b, x (a + b) = x a * x b := fun a b =>
    Subtype.ext (pinnedX_add .E7 K _ a b)
  have hxinv : ∀ a, (x a)⁻¹ = x (-a) := fun a =>
    Subtype.ext (pinnedX_neg .E7 K _ a)
  have hx0 : x 0 = 1 := Subtype.ext (pinnedX_zero .E7 K _)
  have hxinj : Function.Injective x := fun a b h =>
    pinnedX_injective .E7 K _ (congrArg Subtype.val h)
  have hηx : ∀ c, η (x c) = x (σ c) := fun c => by
    refine Subtype.ext (Units.ext ?_)
    rw [hηdef, coe_entrywiseAdjointAut]
    exact entrywise_pinnedX σ.toRingHom _ c
  have hK' : Nat.card K = (2 ^ e) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact pow_pow_eq_self_of_natCard_eq_sq hK' c
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra! h
    have hle := CFSG.SeitzReduction.natCard_le_of_forall_pow_eq_self
      (Nat.one_lt_two_pow (by omega : e ≠ 0)) (Set.univ : Set K) fun a _ =>
        (hσ a).symm.trans (h a)
    rw [Nat.card_univ, hK] at hle
    have hlt : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set d := σ c + c with hddef
  have hdσ : σ d = d := by rw [hddef, map_add, hσσ, add_comm]
  have hd0 : d ≠ 0 := fun h => hc (CharTwo.add_eq_zero.1 h)
  have hdF : x d ∈ F := by
    show η (x d) = x d
    rw [hηx, hdσ]
  have hFperf : ⁅F, F⁆ = F := by
    have hA : Group.IsPerfect (adjointGroup .E7 (fixSubfield σ)) :=
      Group.isPerfect_def.2 (single_edge_perfect .E7 (fixSubfield σ) (by decide))
    have hJ : Group.IsPerfect (fixedFieldImage .E7 σ) :=
      Group.IsPerfect.map (H := adjointGroup .E7 (fixSubfield σ))
        (baseChangeGL (fixSubfield σ).subtype)
    apply map_injective (adjointGroup .E7 K).subtype_injective
    rw [map_commutator, hfix]
    exact Subgroup.commutator_eq_self
  refine ⟨hFperf, x c, ⟨x d, hdF⟩, fun h1 => hd0 (hxinj (h1.trans hx0.symm)), ?_, fun β => ?_⟩
  · show (η (x c))⁻¹ * x c = x d
    rw [hηx, hxinv, ← hxadd, CharTwo.neg_eq]
  have hιF : ∀ g, fixedFieldInclusion (τ := .E7) σ g ∈ F := fun g => by
    have h1 : ((fixedFieldInclusion (τ := .E7) σ g : adjointGroup .E7 K) :
        ModGL .E7 K) ∈ fixedFieldImage .E7 σ :=
      (mem_fixedFieldImage_iff_exists σ _).2 ⟨g, rfl⟩
    rw [← hfix] at h1
    exact (mem_map_iff_mem (adjointGroup .E7 K).subtype_injective).1 h1
  have hιsurj : ∀ y ∈ F, ∃ g, fixedFieldInclusion (τ := .E7) σ g = y := fun y hy => by
    have h1 : (y : ModGL .E7 K) ∈ F.map (adjointGroup .E7 K).subtype := ⟨y, hy, rfl⟩
    rw [hfix] at h1
    exact (mem_fixedFieldImage_iff_exists σ y).1 h1
  let ι₁ : adjointGroup .E7 (fixSubfield σ) →* F :=
    (fixedFieldInclusion (τ := .E7) σ).codRestrict F hιF
  have hι₁ : Function.Bijective ι₁ :=
    ⟨fun a b h => fixedFieldInclusion_injective σ (congrArg Subtype.val h), fun y => by
      obtain ⟨g, hg⟩ := hιsurj y y.2
      exact ⟨g, Subtype.ext hg⟩⟩
  let ι' : adjointGroup .E7 (fixSubfield σ) ≃* F := MulEquiv.ofBijective ι₁ hι₁
  have hι' : ∀ g, ((ι' g : F) : adjointGroup .E7 K) =
      fixedFieldInclusion (τ := .E7) σ g := fun g => rfl
  let β' : MulAut (adjointGroup .E7 (fixSubfield σ)) := (ι'.trans β).trans ι'.symm
  have hβ' : ∀ g, ι' (β' g) = β (ι' g) := fun g => by
    simp only [β', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hdk : d ∈ fixSubfield σ := (hk d).2 ((hσ d).symm.trans hdσ)
  set y₀' : adjointGroup .E7 (fixSubfield σ) :=
    ⟨pinnedX .E7 (fixSubfield σ) (highRoot .E7) ⟨d, hdk⟩,
      pinnedX_mem_adjointGroup _ _⟩ with hy₀'def
  have hι'y : ι' y₀' = ⟨x d, hdF⟩ := Subtype.ext (Subtype.ext (by
    rw [hι', coe_fixedFieldInclusion]
    exact baseChangeGL_pinnedX _ _ _))
  have hy₀'c : y₀' ∈ centralizer ((E8Pilot.posUnipotentSylowE .E7 (fixSubfield σ) :
      Subgroup (adjointGroup .E7 (fixSubfield σ))) :
      Set (adjointGroup .E7 (fixSubfield σ))) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.1
        (E8Pilot.posUnipotent_le_centralizer_pinnedX_highRoot (τ := .E7) _
          (E8Pilot.mem_posUnipotentSylowE.1 hu)))
  obtain ⟨g', -, d', hd'⟩ := E8Pilot.exists_conj_eq_pinnedX_highRoot_of_mem_centralizer
    (Or.inr (Or.inl rfl)) _ (F4Pilot.map_mem_centralizer_smul_sylow β' _ hy₀'c)
  have hβy : (β ⟨x d, hdF⟩ : adjointGroup .E7 K) =
      fixedFieldInclusion (τ := .E7) σ (β' y₀') := by
    rw [← hι', hβ', hι'y]
  have hconj : (fixedFieldInclusion (τ := .E7) σ g')⁻¹ *
      (β ⟨x d, hdF⟩ : adjointGroup .E7 K) * fixedFieldInclusion (τ := .E7) σ g' =
      fixedFieldInclusion (τ := .E7) σ (g'⁻¹ * β' y₀' * g') := by
    rw [hβy, map_mul, map_mul, map_inv]
  refine E8Pilot.exists_sylow_of_conj_eq_pinnedX_highRoot
    (c := fixedFieldInclusion (τ := .E7) σ g') (b := (d' : K)) ?_
  rw [hconj, coe_fixedFieldInclusion, hd',
    baseChangeGL_pinnedX (τ := .E7) (fixSubfield σ).subtype (highRoot .E7) d']
  rfl

end Field

section LemmaC

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem outerFusionTwoCentral_of_odd_E7 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    (hodd : Odd f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t :=
  E8Pilot.outerFusionTwoCentral_of_forall_inner hset e
    (fun _ hα => E8Pilot.mem_range_conj_of_sq_eq_one_of_odd_E7_E8 (Or.inl rfl) hf hodd K hK hα)
    ht hKt

theorem exists_conj_eq_mul_twoCentral_E7_of_outerFusion (hset : StandardSetting G L) {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ g : G, g⁻¹ * t * g ∉ L) (hC1 : F4Pilot.OuterFusionTwoCentral L t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  by_cases hout : ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧
      g⁻¹ * t * g ∉ L ⊔ zpowers t
  · obtain ⟨g, hg1, hg2⟩ := hout
    exact hC1 g hg1 hg2
  · simp only [not_exists, not_and, not_not] at hout
    have : IsSimpleGroup G := hset.simple
    obtain ⟨x₀, hx₀, hgen, hlift⟩ := F4Pilot.exists_gen_of_mulAut hCN hLt hKt
      (F4Pilot.exists_mulAut_normalForm_of_mulEquiv e
        (E8Pilot.exists_mulAut_normalForm_E7_E8 (Or.inl rfl) hf K hK))
    exact F4Pilot.exists_conj_eq_mul_of_forall_inner
      (F4Pilot.two_lt_card_of_exists_mul_ne hset.nonab) ht hLt hCN hnot hout hx₀ hgen hlift

end LemmaC

end CFSG.SeitzReduction.E7Pilot
