module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionAut
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotOuterFusionModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped Pointwise


theorem exists_conj_eq_entrywise_of_outer_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {e : ℕ}
    (he : 1 ≤ e) (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ e) {α : MulAut (adjointGroup τ K)} (hα2 : α ^ 2 = 1)
    (hαo : α ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    ∃ ψ : MulAut (adjointGroup τ K), ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ := by
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form (by omega : 1 ≤ 2 * e) K hK τ hτ
  obtain ⟨⟨g, σ'⟩, hgσ, -⟩ := hNF α
  have hΘα : Θ α = σ' := hΘ α g σ' hgσ
  have hσ1 : Θ α ≠ 1 := fun h1 => hαo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨-, hσc⟩ := (hinv α hα2).resolve_left hσ1
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by
    rw [← hΘα, hσc, hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he K hK σ.toRingHom hσ
  obtain ⟨β, -, hdesc⟩ := hQ1 τ
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hαform : ∀ u, (α u : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ (fun _ => 1) *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ fun _ => 1)⁻¹ *
        (g : ModGL τ K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin τ.rank → Kˣ) from rfl, rootDiagUnit_one, mul_one,
      inv_one, mul_one, ← hσσ']
    exact hgσ u
  obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
  exact ⟨ψ, MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_entrywiseAdjointAut])⟩

theorem exists_sylow_of_conj_eq_pinnedX_highRoot {K : Type} [Field K] [Finite K] [CharP K 2]
    {τ : Tag}
    {z c : adjointGroup τ K} {b : K}
    (h : ((c⁻¹ * z * c : adjointGroup τ K) : ModGL τ K) = pinnedX τ K (highRoot τ) b) :
    ∃ S : Sylow 2 (adjointGroup τ K), ∀ u ∈ (S : Subgroup (adjointGroup τ K)), u * z = z * u := by
  refine ⟨c • posUnipotentSylowE τ K, fun u hu => ?_⟩
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have hv' := mem_posUnipotentSylowE.1 hv
  have hcomm : v * (c⁻¹ * z * c) = (c⁻¹ * z * c) * v := by
    refine Subtype.ext ?_
    show (v : ModGL τ K) * ((c⁻¹ * z * c : adjointGroup τ K) : ModGL τ K) =
      ((c⁻¹ * z * c : adjointGroup τ K) : ModGL τ K) * v
    rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.1
      (posUnipotent_le_centralizer_pinnedX_highRoot (τ := τ) b hv')
  rw [MulAut.smul_def, MulAut.conj_apply]
  calc c * v * c⁻¹ * z = c * (v * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * z * c) * v) * c⁻¹ := by rw [hcomm]
    _ = z * (c * v * c⁻¹) := by group

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem twoCentralTwistedFusion_field_E8 {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    F4Pilot.TwoCentralTwistedFusion (entrywiseAdjointAut .E8 σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hk, -, -, hfix, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E8 (Or.inr rfl) he K hK σ hσ
  set η := entrywiseAdjointAut .E8 σ with hηdef
  set F := η.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E8 K)) with hFdef
  set x : K → adjointGroup .E8 K := fun c =>
    ⟨pinnedX .E8 K (highRoot .E8) c, pinnedX_mem_adjointGroup _ _⟩ with hxdef
  have hxadd : ∀ a b, x (a + b) = x a * x b := fun a b =>
    Subtype.ext (pinnedX_add .E8 K _ a b)
  have hxinv : ∀ a, (x a)⁻¹ = x (-a) := fun a =>
    Subtype.ext (pinnedX_neg .E8 K _ a)
  have hx0 : x 0 = 1 := Subtype.ext (pinnedX_zero .E8 K _)
  have hxinj : Function.Injective x := fun a b h =>
    pinnedX_injective .E8 K _ (congrArg Subtype.val h)
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
    have hA : Group.IsPerfect (adjointGroup .E8 (fixSubfield σ)) :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_e8 _
    have hJ : Group.IsPerfect (fixedFieldImage .E8 σ) :=
      Group.IsPerfect.map (H := adjointGroup .E8 (fixSubfield σ))
        (baseChangeGL (fixSubfield σ).subtype)
    apply map_injective (adjointGroup .E8 K).subtype_injective
    rw [map_commutator, hfix]
    exact Subgroup.commutator_eq_self
  refine ⟨hFperf, x c, ⟨x d, hdF⟩, fun h1 => hd0 (hxinj (h1.trans hx0.symm)), ?_, fun β => ?_⟩
  · show (η (x c))⁻¹ * x c = x d
    rw [hηx, hxinv, ← hxadd, CharTwo.neg_eq]
  have hιF : ∀ g, fixedFieldInclusion (τ := .E8) σ g ∈ F := fun g => by
    have h1 : ((fixedFieldInclusion (τ := .E8) σ g : adjointGroup .E8 K) :
        ModGL .E8 K) ∈ fixedFieldImage .E8 σ :=
      (mem_fixedFieldImage_iff_exists σ _).2 ⟨g, rfl⟩
    rw [← hfix] at h1
    exact (mem_map_iff_mem (adjointGroup .E8 K).subtype_injective).1 h1
  have hιsurj : ∀ y ∈ F, ∃ g, fixedFieldInclusion (τ := .E8) σ g = y := fun y hy => by
    have h1 : (y : ModGL .E8 K) ∈ F.map (adjointGroup .E8 K).subtype := ⟨y, hy, rfl⟩
    rw [hfix] at h1
    exact (mem_fixedFieldImage_iff_exists σ y).1 h1
  let ι₁ : adjointGroup .E8 (fixSubfield σ) →* F :=
    (fixedFieldInclusion (τ := .E8) σ).codRestrict F hιF
  have hι₁ : Function.Bijective ι₁ :=
    ⟨fun a b h => fixedFieldInclusion_injective σ (congrArg Subtype.val h), fun y => by
      obtain ⟨g, hg⟩ := hιsurj y y.2
      exact ⟨g, Subtype.ext hg⟩⟩
  let ι' : adjointGroup .E8 (fixSubfield σ) ≃* F := MulEquiv.ofBijective ι₁ hι₁
  have hι' : ∀ g, ((ι' g : F) : adjointGroup .E8 K) =
      fixedFieldInclusion (τ := .E8) σ g := fun g => rfl
  let β' : MulAut (adjointGroup .E8 (fixSubfield σ)) := (ι'.trans β).trans ι'.symm
  have hβ' : ∀ g, ι' (β' g) = β (ι' g) := fun g => by
    simp only [β', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hdk : d ∈ fixSubfield σ := (hk d).2 ((hσ d).symm.trans hdσ)
  set y₀' : adjointGroup .E8 (fixSubfield σ) :=
    ⟨pinnedX .E8 (fixSubfield σ) (highRoot .E8) ⟨d, hdk⟩,
      pinnedX_mem_adjointGroup _ _⟩ with hy₀'def
  have hι'y : ι' y₀' = ⟨x d, hdF⟩ := Subtype.ext (Subtype.ext (by
    rw [hι', coe_fixedFieldInclusion]
    exact baseChangeGL_pinnedX _ _ _))
  have hy₀'c : y₀' ∈ centralizer ((posUnipotentSylowE .E8 (fixSubfield σ) :
      Subgroup (adjointGroup .E8 (fixSubfield σ))) :
      Set (adjointGroup .E8 (fixSubfield σ))) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.1
        (posUnipotent_le_centralizer_pinnedX_highRoot (τ := .E8) _
          (mem_posUnipotentSylowE.1 hu)))
  obtain ⟨g', -, d', hd'⟩ := exists_conj_eq_pinnedX_highRoot_of_mem_centralizer
    (Or.inr (Or.inr rfl)) _ (F4Pilot.map_mem_centralizer_smul_sylow β' _ hy₀'c)
  have hβy : (β ⟨x d, hdF⟩ : adjointGroup .E8 K) =
      fixedFieldInclusion (τ := .E8) σ (β' y₀') := by
    rw [← hι', hβ', hι'y]
  have hconj : (fixedFieldInclusion (τ := .E8) σ g')⁻¹ *
      (β ⟨x d, hdF⟩ : adjointGroup .E8 K) * fixedFieldInclusion (τ := .E8) σ g' =
      fixedFieldInclusion (τ := .E8) σ (g'⁻¹ * β' y₀' * g') := by
    rw [hβy, map_mul, map_mul, map_inv]
  refine exists_sylow_of_conj_eq_pinnedX_highRoot
    (c := fixedFieldInclusion (τ := .E8) σ g') (b := (d' : K)) ?_
  rw [hconj, coe_fixedFieldInclusion, hd',
    baseChangeGL_pinnedX (τ := .E8) (fixSubfield σ).subtype (highRoot .E8) d']
  rfl

theorem outerFusionTwoCentral_of_even_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    (eL : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t := by
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * e) hK
  have hσ : ∀ c, (fr ^ e) c = c ^ 2 ^ e := ringAut_pow_apply_of_frobenius hfr e
  exact F4Pilot.outerFusionTwoCentral_of_twoCentralTwistedFusion hset
    (isSolvable_outer_of_mulEquiv_E8 eL)
    (by rw [← map_center_eq eL.symm, center_adjointGroup_eq_bot, Subgroup.map_bot])
    (exists_perfect_le_of_mulEquiv_E8 hq eL) eL
    (fun α hα hαo => exists_conj_eq_entrywise_of_outer_E7_E8 (Or.inr rfl) he K hK _ hσ hα hαo)
    (twoCentralTwistedFusion_field_E8 he hK _ hσ) ht hKt

theorem outerFusionTwoCentral_E8 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (eL : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    F4Pilot.OuterFusionTwoCentral L t := by
  rcases Nat.even_or_odd' f with ⟨e, rfl | rfl⟩
  · exact outerFusionTwoCentral_of_even_E8 hset (by omega) hK eL ht hKt
  · exact outerFusionTwoCentral_of_odd_E8 hset (by omega) ⟨e, rfl⟩ hK eL ht hKt

theorem exists_conj_eq_mul_twoCentral_E8_of_two_le {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (eL : L ≃* adjointGroup .E8 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u :=
  exists_conj_eq_mul_twoCentral_E8 hset hf hK eL ht hKt (outerFusionTwoCentral_E8 hset hf hK eL ht hKt)

end CFSG.SeitzReduction.E8Pilot
