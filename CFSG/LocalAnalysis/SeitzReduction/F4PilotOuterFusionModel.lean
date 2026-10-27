module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotOuterFusionBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassRepsCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Model
public import CFSG.LocalAnalysis.SeitzReduction.Fusion

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree RootOps
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open scoped Pointwise

section Sylow

variable {X : Type*} [Group X] {p : ℕ}

theorem map_mem_centralizer_smul_sylow (β : MulAut X) (P : Sylow p X) {z : X}
    (hz : z ∈ centralizer ((P : Subgroup X) : Set X)) :
    β z ∈ centralizer (((β • P : Sylow p X) : Subgroup X) : Set X) := by
  rw [mem_centralizer_iff]
  intro u hu
  rw [SetLike.mem_coe, Sylow.pointwise_smul_def, mem_smul_pointwise_iff_exists] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [MulAut.smul_def, ← map_mul, ← map_mul, mem_centralizer_iff.1 hz v hv]

end Sylow

section Conj


variable {K : Type} [Field K]

theorem exists_sylow_of_conj_eq_root_44_47 [Finite K] [CharP K 2]
    {z c : adjointGroup ReeTag.F4.tag K} {a b : K}
    (h : ((c⁻¹ * z * c : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
      pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 44) a *
        pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 47) b) :
    ∃ S : Sylow 2 (adjointGroup ReeTag.F4.tag K),
      ∀ u ∈ (S : Subgroup (adjointGroup ReeTag.F4.tag K)), u * z = z * u := by
  obtain ⟨P, hP⟩ : ∃ P : Sylow 2 (adjointGroup ReeTag.F4.tag K),
      ∀ v, v ∈ (P : Subgroup (adjointGroup ReeTag.F4.tag K)) ↔
        (v : ModGL ReeTag.F4.tag K) ∈ posUnipotent ReeTag.F4.tag K :=
    ⟨ClassReps.posUnipotentSylow, fun v => ClassReps.mem_posUnipotentSylow⟩
  refine ⟨c • P, fun u hu => ?_⟩
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have hv' := (hP v).1 hv
  have hcomm : v * (c⁻¹ * z * c) = (c⁻¹ * z * c) * v := by
    refine Subtype.ext ?_
    show (v : ModGL ReeTag.F4.tag K) *
        ((c⁻¹ * z * c : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) =
      ((c⁻¹ * z * c : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) * v
    rw [h]
    exact (ClassReps.f4x_44_mul_f4x_47_commute a b hv').symm
  rw [MulAut.smul_def, MulAut.conj_apply]
  calc c * v * c⁻¹ * z = c * (v * (c⁻¹ * z * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * z * c) * v) * c⁻¹ := by rw [hcomm]
    _ = z * (c * v * c⁻¹) := by group

end Conj

section Field


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem twoCentralTwistedFusion_field {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e)) :
    TwoCentralTwistedFusion (ReeTag.F4.finiteExceptionalAut K ^ (2 * e)) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * e) hK
  set σ : K ≃+* K := fr ^ e
  have hσ : ∀ c, σ c = c ^ 2 ^ e := ringAut_pow_apply_of_frobenius hfr e
  obtain ⟨hk, -, hFr, hent, -, hfix, -⟩ := even_F4_canonical_field_full_centralizer he K hK σ hσ
  set η := ReeTag.F4.finiteExceptionalAut K ^ (2 * e) with hηdef
  have hη : η = entrywiseAdjointAut ReeTag.F4.tag σ := by rw [hent, hFr]
  set F := η.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag K)) with hFdef
  set x : K → adjointGroup ReeTag.F4.tag K := fun c =>
    ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 47) c, pinnedX_mem_adjointGroup _ _⟩ with hxdef
  have hxadd : ∀ a b, x (a + b) = x a * x b := fun a b =>
    Subtype.ext (pinnedX_add ReeTag.F4.tag K _ a b)
  have hxinv : ∀ a, (x a)⁻¹ = x (-a) := fun a =>
    Subtype.ext (pinnedX_neg ReeTag.F4.tag K _ a)
  have hx0 : x 0 = 1 := Subtype.ext (pinnedX_zero ReeTag.F4.tag K _)
  have hxinj : Function.Injective x := fun a b h =>
    pinnedX_injective ReeTag.F4.tag K _ (congrArg Subtype.val h)
  have hηx : ∀ c, η (x c) = x (σ c) := fun c => by
    refine Subtype.ext (Units.ext ?_)
    rw [hη, coe_entrywiseAdjointAut]
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
    have hA : Group.IsPerfect (adjointGroup ReeTag.F4.tag (fixSubfield σ)) :=
      CFSG.LieType.Steinberg.Adjoint.isPerfect_f4 _
    have hJ : Group.IsPerfect (fixedFieldImage ReeTag.F4.tag σ) :=
      Group.IsPerfect.map (H := adjointGroup ReeTag.F4.tag (fixSubfield σ))
        (baseChangeGL (fixSubfield σ).subtype)
    apply map_injective (adjointGroup ReeTag.F4.tag K).subtype_injective
    rw [map_commutator, hfix]
    exact Subgroup.commutator_eq_self
  refine ⟨hFperf, x c, ⟨x d, hdF⟩, fun h1 => hd0 (hxinj (h1.trans hx0.symm)), ?_, fun β => ?_⟩
  · show (η (x c))⁻¹ * x c = x d
    rw [hηx, hxinv, ← hxadd, CharTwo.neg_eq]
  have hιF : ∀ g, fixedFieldInclusion (τ := ReeTag.F4.tag) σ g ∈ F := fun g => by
    have h1 : ((fixedFieldInclusion (τ := ReeTag.F4.tag) σ g : adjointGroup ReeTag.F4.tag K) :
        ModGL ReeTag.F4.tag K) ∈ fixedFieldImage ReeTag.F4.tag σ :=
      (mem_fixedFieldImage_iff_exists σ _).2 ⟨g, rfl⟩
    rw [← hfix] at h1
    exact (mem_map_iff_mem (adjointGroup ReeTag.F4.tag K).subtype_injective).1 h1
  have hιsurj : ∀ y ∈ F, ∃ g, fixedFieldInclusion (τ := ReeTag.F4.tag) σ g = y := fun y hy => by
    have h1 : (y : ModGL ReeTag.F4.tag K) ∈ F.map (adjointGroup ReeTag.F4.tag K).subtype :=
      ⟨y, hy, rfl⟩
    rw [hfix] at h1
    exact (mem_fixedFieldImage_iff_exists σ y).1 h1
  let ι₁ : adjointGroup ReeTag.F4.tag (fixSubfield σ) →* F :=
    (fixedFieldInclusion (τ := ReeTag.F4.tag) σ).codRestrict F hιF
  have hι₁ : Function.Bijective ι₁ :=
    ⟨fun a b h => fixedFieldInclusion_injective σ (congrArg Subtype.val h), fun y => by
      obtain ⟨g, hg⟩ := hιsurj y y.2
      exact ⟨g, Subtype.ext hg⟩⟩
  let ι' : adjointGroup ReeTag.F4.tag (fixSubfield σ) ≃* F := MulEquiv.ofBijective ι₁ hι₁
  have hι' : ∀ g, ((ι' g : F) : adjointGroup ReeTag.F4.tag K) =
      fixedFieldInclusion (τ := ReeTag.F4.tag) σ g := fun g => rfl
  let β' : MulAut (adjointGroup ReeTag.F4.tag (fixSubfield σ)) := (ι'.trans β).trans ι'.symm
  have hβ' : ∀ g, ι' (β' g) = β (ι' g) := fun g => by
    simp only [β', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hdk : d ∈ fixSubfield σ := (hk d).2 ((hσ d).symm.trans hdσ)
  set y₀' : adjointGroup ReeTag.F4.tag (fixSubfield σ) :=
    ⟨pinnedX ReeTag.F4.tag (fixSubfield σ) (orbitCertRoot .F4 47) ⟨d, hdk⟩,
      pinnedX_mem_adjointGroup _ _⟩ with hy₀'def
  have hι'y : ι' y₀' = ⟨x d, hdF⟩ := Subtype.ext (Subtype.ext (by
    rw [hι', coe_fixedFieldInclusion]
    exact baseChangeGL_pinnedX _ _ _))
  obtain ⟨Pk, hPk⟩ : ∃ P : Sylow 2 (adjointGroup ReeTag.F4.tag (fixSubfield σ)),
      ∀ v, v ∈ (P : Subgroup (adjointGroup ReeTag.F4.tag (fixSubfield σ))) ↔
        (v : ModGL ReeTag.F4.tag (fixSubfield σ)) ∈ posUnipotent ReeTag.F4.tag (fixSubfield σ) :=
    ⟨ClassReps.posUnipotentSylow, fun v => ClassReps.mem_posUnipotentSylow⟩
  have hy₀'c : y₀' ∈ centralizer ((Pk : Subgroup (adjointGroup ReeTag.F4.tag (fixSubfield σ))) :
      Set (adjointGroup ReeTag.F4.tag (fixSubfield σ))) :=
    Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subtype.ext (f4x_central (Or.inr rfl) _ ((hPk u).1 hu))
  obtain ⟨g', a, b, hab⟩ : ∃ (g' : adjointGroup ReeTag.F4.tag (fixSubfield σ))
      (a b : fixSubfield σ),
      ((g'⁻¹ * β' y₀' * g' : adjointGroup ReeTag.F4.tag (fixSubfield σ)) :
        ModGL ReeTag.F4.tag (fixSubfield σ)) =
        pinnedX ReeTag.F4.tag (fixSubfield σ) (orbitCertRoot .F4 44) a *
          pinnedX ReeTag.F4.tag (fixSubfield σ) (orbitCertRoot .F4 47) b := by
    obtain ⟨g', -, a, b, hab⟩ :=
      ClassReps.exists_conj_eq_f4x_44_mul_f4x_47_of_mem_centralizer _
        (map_mem_centralizer_smul_sylow β' _ hy₀'c)
    exact ⟨g', a, b, hab⟩
  have hβy : (β ⟨x d, hdF⟩ : adjointGroup ReeTag.F4.tag K) =
      fixedFieldInclusion (τ := ReeTag.F4.tag) σ (β' y₀') := by
    rw [← hι', hβ', hι'y]
  have hconj : (fixedFieldInclusion (τ := ReeTag.F4.tag) σ g')⁻¹ *
      (β ⟨x d, hdF⟩ : adjointGroup ReeTag.F4.tag K) * fixedFieldInclusion (τ := ReeTag.F4.tag) σ g' =
      fixedFieldInclusion (τ := ReeTag.F4.tag) σ (g'⁻¹ * β' y₀' * g') := by
    rw [hβy, map_mul, map_mul, map_inv]
  refine exists_sylow_of_conj_eq_root_44_47
    (c := fixedFieldInclusion (τ := ReeTag.F4.tag) σ g') (a := (a : K)) (b := (b : K)) ?_
  rw [hconj, coe_fixedFieldInclusion, hab, map_mul,
    baseChangeGL_pinnedX (τ := ReeTag.F4.tag) (fixSubfield σ).subtype (orbitCertRoot .F4 44) a,
    baseChangeGL_pinnedX (τ := ReeTag.F4.tag) (fixSubfield σ).subtype (orbitCertRoot .F4 47) b]
  rfl

end Field

section Roots

theorem dualRoot_orbitCertRoot_47_44 :
    ReeTag.F4.dualRoot (orbitCertRoot .F4 47) = orbitCertRoot .F4 44 ∧
      ReeTag.F4.dualRoot (orbitCertRoot .F4 44) = orbitCertRoot .F4 47 :=
  ⟨List.ofFn_injective (by decide +kernel), List.ofFn_injective (by decide +kernel)⟩

theorem orbitCertRoot_47_ne_44 :
    (orbitCertRoot .F4 47 : Fin (Tag.rank .F4) → ℤ) ≠ orbitCertRoot .F4 44 := by
  intro h
  have := congrArg List.ofFn h
  revert this
  decide +kernel

end Roots

section Ree


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem twoCentralTwistedFusion_ree {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    TwoCentralTwistedFusion (ReeTag.F4.finiteReeAut K a) := by
  have h2 : (2 : K) = 0 := ReeTag.F4_two_eq_zero (K := K)
  set η := ReeTag.F4.finiteReeAut K a with hηdef
  set F := η.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag K)) with hFdef
  obtain ⟨hdr, hds⟩ := dualRoot_orbitCertRoot_47_44
  have hr47 : IsRoot ReeTag.F4.tag (orbitCertRoot .F4 47) ∧ 0 < height (orbitCertRoot .F4 47) :=
    f4_isRoot_pos ⟨by norm_num, by norm_num⟩
  have hr44 : IsRoot ReeTag.F4.tag (orbitCertRoot .F4 44) ∧ 0 < height (orbitCertRoot .F4 44) :=
    f4_isRoot_pos ⟨by norm_num, by norm_num⟩
  set xr : adjointGroup ReeTag.F4.tag K :=
    ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 47) 1, pinnedX_mem_adjointGroup _ _⟩ with hxrdef
  set xs : adjointGroup ReeTag.F4.tag K :=
    ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 44) 1, pinnedX_mem_adjointGroup _ _⟩ with hxsdef
  have hxr : (xr : ModGL ReeTag.F4.tag K) = pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 47) 1 := rfl
  have hxs : (xs : ModGL ReeTag.F4.tag K) = pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 44) 1 := rfl
  have hηr : η xr = xs := (ReeTag.finiteReeAut_pinnedX_F4 hr47.1 (1 : K)).trans
    (Subtype.ext (by rw [hdr, one_pow]))
  have hηs : η xs = xr := (ReeTag.finiteReeAut_pinnedX_F4 hr44.1 (1 : K)).trans
    (Subtype.ext (by rw [hds, one_pow]))
  have hxs2 : xs * xs = 1 := Subtype.ext (by
    show pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 44) 1 *
      pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 44) 1 = 1
    rw [← pinnedX_add ReeTag.F4.tag K (orbitCertRoot .F4 44) 1 1, one_add_one_eq_two, h2,
      pinnedX_zero ReeTag.F4.tag K (orbitCertRoot .F4 44)])
  have hxsinv : xs⁻¹ = xs := inv_eq_of_mul_eq_one_right hxs2
  have hcomm : xs * xr = xr * xs := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    have h := f4x_central (K := K) (k := 44) (Or.inl rfl) 1
      (f4x_mem_posUnipotent (i := 47) ⟨by norm_num, by norm_num⟩ (1 : K))
    exact Subtype.ext h.symm
  have hy₀F : xs * xr ∈ F := by
    show η (xs * xr) = xs * xr
    rw [map_mul, hηs, hηr, hcomm]
  have hFperf : ⁅F, F⁆ = F := by
    have hperf : commutator (reeFixed ReeTag.F4 K a) = ⊤ :=
      CFSG.LieType.Simplicity.commutator_reeFixed_F4 a ha hK
    have hFR : F = ReeTag.F4.finiteReeFixedGroup K a := rfl
    rw [hFR, finiteReeFixedGroup_eq_reeFixed_F4, ← map_subtype_commutator, hperf,
      ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨hFperf, xr, ⟨xs * xr, hy₀F⟩, fun h1 => ?_, ?_, fun β => ?_⟩
  · have h3 : ((xs * xr : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) = 1 := by
      rw [show (xs * xr : adjointGroup ReeTag.F4.tag K) = 1 from h1, OneMemClass.coe_one]
    rw [Subgroup.coe_mul, hxs, hxr] at h3
    exact pinnedX_mul_pinnedX_ne_one K hr44.1 hr47.1 hr44.2 hr47.2
      (Ne.symm orbitCertRoot_47_ne_44) h3
  · show (η xr)⁻¹ * xr = xs * xr
    rw [hηr, hxsinv]
  have hFΓ : F.map (adjointGroup ReeTag.F4.tag K).subtype = ReeTag.F4.reeGamma K a := rfl
  let ρ : F ≃* ReeTag.F4.reeGamma K a :=
    (F.equivMapOfInjective _ (adjointGroup ReeTag.F4.tag K).subtype_injective).trans
      (MulEquiv.subgroupCongr hFΓ)
  have hρ : ∀ w : F, ((ρ w : ReeTag.F4.reeGamma K a) : ModGL ReeTag.F4.tag K) =
      ((w : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) := fun w => rfl
  obtain ⟨hfield, hNF, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, γ⟩, hxγ, -⟩ := hNF ((ρ.symm.trans β).trans ρ)
  have hfix1 : ∀ α : Fin ReeTag.F4.tag.rank → ℤ,
      Units.map (entrywiseHom γ.toRingHom) (pinnedX ReeTag.F4.tag K α 1) =
        pinnedX ReeTag.F4.tag K α 1 := fun α =>
    Units.ext ((entrywise_pinnedX γ.toRingHom α (1 : K)).trans (by rw [map_one]))
  have hγ : ((ReeTag.F4.reeGammaFieldAut K a γ (ρ ⟨xs * xr, hy₀F⟩) : ReeTag.F4.reeGamma K a) :
      ModGL ReeTag.F4.tag K) = (xs : ModGL ReeTag.F4.tag K) * xr := by
    rw [(hfield γ).1, hρ, Subgroup.coe_mul, hxs, hxr, map_mul, hfix1 (orbitCertRoot .F4 44),
      hfix1 (orbitCertRoot .F4 47)]
  have h1 := congrArg (fun φ : MulAut (ReeTag.F4.reeGamma K a) =>
    ((φ (ρ ⟨xs * xr, hy₀F⟩) : ReeTag.F4.reeGamma K a) : ModGL ReeTag.F4.tag K)) hxγ
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.mul_apply,
    MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hγ, hρ] at h1
  obtain ⟨c, -, hcx⟩ := x.2
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  refine exists_sylow_of_conj_eq_root_44_47 (c := c) (a := 1) (b := 1) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1, ← hxs, ← hxr]
  rw [show ((c : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) = x from hcx]
  group

end Ree

section Assembly


theorem twoCentralTwistedFusion_of_two_le {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) :
    TwoCentralTwistedFusion (ReeTag.F4.finiteExceptionalAut K ^ f) := by
  rcases Nat.even_or_odd' f with ⟨e, rfl | rfl⟩
  · exact twoCentralTwistedFusion_field (by omega) hK
  · obtain ⟨-, -, -, -, -, -, hodd⟩ := even_F4_exact_automorphism_normal_form (by omega) K hK
    rw [(hodd e rfl).2.1]
    exact twoCentralTwistedFusion_ree (by omega) hK

end Assembly

end CFSG.SeitzReduction.F4Pilot
