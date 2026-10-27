module

public import CFSG.LargeExtraspecial.AS35YSAct
public import CFSG.LargeExtraspecial.AS35YLSU33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] noncomputable def actL_YS (hst : S.Asc512Standing) :
    S.LbarAsc →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S) :=
  (act0_YS hst).comp (Subgroup.inclusion LbarAsc_le_Mbar_YL)

theorem actL_YS_apply (hst : S.Asc512Standing) (l : S.LbarAsc) :
    actL_YS hst l = act0_YS hst ⟨l, LbarAsc_le_Mbar_YL l.2⟩ :=
  rfl

theorem actL_YS_injective (hst : S.Asc512Standing) : Function.Injective (actL_YS hst) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  exact Subtype.ext (act0_YS_eq_one hst l.2 hl)

theorem act0_YS_conj (hst : S.Asc512Standing) (a b : S.Mbar) :
    act0_YS hst a * act0_YS hst b * (act0_YS hst a)⁻¹ = act0_YS hst (a * b * a⁻¹) := by
  rw [map_mul, map_mul, map_inv]

theorem act0_YS_conj' (hst : S.Asc512Standing) (a b : S.Mbar) :
    (act0_YS hst a)⁻¹ * act0_YS hst b * act0_YS hst a = act0_YS hst (a⁻¹ * b * a) := by
  rw [map_mul, map_mul, map_inv]

theorem act0_mem_closure_YS (hst : S.Asc512Standing) {l : S.O} (hl : l ∈ S.LbarAsc) :
    act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ ∈
      closure {σ | ∃ (d : S.O) (hd : d ∈ S.DbarAsc),
        act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ = σ} := by
  induction hl using Subgroup.closure_induction with
  | mem σ hσ => exact subset_closure ⟨σ, hσ, rfl⟩
  | one =>
    have e : (⟨1, LbarAsc_le_Mbar_YL (one_mem _)⟩ : S.Mbar) = 1 := rfl
    rw [e, map_one]
    exact one_mem _
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, LbarAsc_le_Mbar_YL (mul_mem ha hb)⟩ : S.Mbar) =
        ⟨a, LbarAsc_le_Mbar_YL ha⟩ * ⟨b, LbarAsc_le_Mbar_YL hb⟩ := rfl
    rw [e, map_mul]
    exact mul_mem iha ihb
  | inv a ha iha =>
    have e : (⟨a⁻¹, LbarAsc_le_Mbar_YL (inv_mem ha)⟩ : S.Mbar) =
        (⟨a, LbarAsc_le_Mbar_YL ha⟩ : S.Mbar)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem iha

theorem irred_V0_of_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h : RadSing_YS S) {τ x : S.O} (hτ : τ ∈ S.DbarAsc) (hxM : x ∈ S.Mbar) {k : ℕ}
    (hx3 : x ^ (3 ^ k) = 1) (hxt : x * τ = τ * x)
    (hfpf : ∀ v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) :
    ∀ Z : Submodule (ZMod 2) (V0_YS S),
      (∀ (l : S.O) (hl : l ∈ S.LbarAsc), ∀ z ∈ Z, act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ z ∈ Z) →
        Z = ⊥ ∨ Z = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set D : Set (V0_YS S ≃ₗ[ZMod 2] V0_YS S) :=
    {σ | ∃ (d : S.O) (hd : d ∈ S.DbarAsc), act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ = σ}
    with hDdef
  have hord : ∀ {d e : S.O} (hd : d ∈ S.DbarAsc) (he : e ∈ S.DbarAsc),
      orderOf (act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ *
        act0_YS hst ⟨e, DbarAsc_subset_Mbar_YL he⟩) = orderOf (d * e) := by
    intro d e hd he
    have e1 : actL_YS hst ⟨d, subset_closure hd⟩ * actL_YS hst ⟨e, subset_closure he⟩ =
        actL_YS hst ((⟨d, subset_closure hd⟩ : S.LbarAsc) * ⟨e, subset_closure he⟩) :=
      ((actL_YS hst).map_mul _ _).symm
    rw [← actL_YS_apply hst ⟨d, subset_closure hd⟩, ← actL_YS_apply hst ⟨e, subset_closure he⟩,
      e1, orderOf_injective _ (actL_YS_injective hst), ← Subgroup.orderOf_coe, Subgroup.coe_mul]
  have hA : ∀ σ ∈ D, IsTypeA (q0_YS h) σ 2 := by
    rintro _ ⟨d, hd, rfl⟩
    exact isTypeA_act0_YS hS hst h hd
  have hconj : ∀ σ ∈ D, ∃ c ∈ closure D,
      c * act0_YS hst ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ * c⁻¹ = σ := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨l, hl, hld⟩ := hst.conj τ hτ d hd
    refine ⟨act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩, act0_mem_closure_YS hst hl, ?_⟩
    have e : (⟨l, LbarAsc_le_Mbar_YL hl⟩ : S.Mbar) * ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ *
        (⟨l, LbarAsc_le_Mbar_YL hl⟩ : S.Mbar)⁻¹ = ⟨d, DbarAsc_subset_Mbar_YL hd⟩ :=
      Subtype.ext hld
    exact (act0_YS_conj hst _ _).trans (congrArg (act0_YS hst) e)
  have hfixD : ∀ v, (∀ σ ∈ D, σ v = v) → v = 0 :=
    fun v hv => act0_YS_fix hS hst hnd fun d hd => hv _ ⟨d, hd, rfl⟩
  have hsqD : ∀ σ ∈ D, ∀ σ' ∈ D, orderOf (σ * σ') = 4 → (σ * σ') ^ 2 ∈ D := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ h4
    rw [hord hd he] at h4
    have hsq := sq_mem_DbarAsc_YL hS hd he h4
    refine ⟨_, hsq, ?_⟩
    have e : (⟨(d * e) ^ 2, DbarAsc_subset_Mbar_YL hsq⟩ : S.Mbar) =
        ((⟨d, DbarAsc_subset_Mbar_YL hd⟩ : S.Mbar) * ⟨e, DbarAsc_subset_Mbar_YL he⟩) ^ 2 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul])
    exact (congrArg (act0_YS hst) e).trans (((act0_YS hst).map_pow _ 2).trans
      (congrArg (· ^ 2) ((act0_YS hst).map_mul _ _)))
  have hndD : ∃ σ ∈ D, ∃ σ' ∈ D, orderOf (σ * σ') = 4 := by
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨e, he, rfl⟩, h4⟩ := hnd
    have h4' := AS35YL.orderOf_eq_four_of_mk_YL
      (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hd he h4
    exact ⟨_, ⟨_, hd, rfl⟩, _, ⟨_, he, rfl⟩, by rw [hord hd he, h4']⟩
  have hxD : ∀ σ ∈ D, (act0_YS hst ⟨x, hxM⟩)⁻¹ * σ * act0_YS hst ⟨x, hxM⟩ ∈ D := by
    rintro _ ⟨d, hd, rfl⟩
    have hd' := S.conj_mem_DbarAsc_L (S.Mbar.inv_mem hxM) hd
    rw [inv_inv] at hd'
    refine ⟨_, hd', ?_⟩
    have e : (⟨x⁻¹ * d * x, DbarAsc_subset_Mbar_YL hd'⟩ : S.Mbar) =
        (⟨x, hxM⟩ : S.Mbar)⁻¹ * ⟨d, DbarAsc_subset_Mbar_YL hd⟩ * ⟨x, hxM⟩ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])
    exact (congrArg (act0_YS hst) e).trans (act0_YS_conj' hst _ _).symm
  have hxt' : act0_YS hst ⟨x, hxM⟩ * act0_YS hst ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ =
      act0_YS hst ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ * act0_YS hst ⟨x, hxM⟩ := by
    have e : (⟨x, hxM⟩ : S.Mbar) * ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ =
        ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ * ⟨x, hxM⟩ := Subtype.ext hxt
    exact ((act0_YS hst).map_mul _ _).symm.trans ((congrArg (act0_YS hst) e).trans
      ((act0_YS hst).map_mul _ _))
  have hxk' : act0_YS hst ⟨x, hxM⟩ ^ (3 ^ k) = 1 := by
    have e : (⟨x, hxM⟩ : S.Mbar) ^ (3 ^ k) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hx3]; rfl)
    exact ((act0_YS hst).map_pow _ _).symm.trans ((congrArg (act0_YS hst) e).trans
      (act0_YS hst).map_one)
  have hτD : act0_YS hst ⟨τ, DbarAsc_subset_Mbar_YL hτ⟩ ∈ D := ⟨τ, hτ, rfl⟩
  have hirr := AS35YL.irred_of_fpf_YL (q0_YS_nondegenerate h) hτD hA hconj hfixD
    hsqD hndD (x := act0_YS hst ⟨x, hxM⟩) (q0_act0_YS h hst _) hxD hxt' hxk'
    (fun v hv hxv => fpf_act0_YS hS hst hnd hτ hxM hxt hfpf hv hxv)
  intro Z hZ
  exact hirr Z fun _ ⟨d, hd, hσd⟩ z hz => hσd ▸ hZ d (subset_closure hd) z hz

theorem irred_V0_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    (h5127 : S14.Asc512FiveTwelveSevenStmt) (h : RadSing_YS S) :
    ∀ Z : Submodule (ZMod 2) (V0_YS S),
      (∀ (l : S.O) (hl : l ∈ S.LbarAsc), ∀ z ∈ Z, act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ z ∈ Z) →
        Z = ⊥ ∨ Z = ⊤ := by
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨x, hxM, ⟨k, hxk⟩, hxt, hfpf⟩ := h5127 _ S hS g ht htM
  have htD : S.ρ ⟨_, htM⟩ ∈ S.DbarAsc := ⟨_, ht, htM, rfl⟩
  have hx3 : x ^ (3 ^ k) = 1 := by rw [← hxk]; exact pow_orderOf_eq_one x
  generalize S.ρ ⟨g * S.z * g⁻¹, htM⟩ = τ at htD hxt hfpf
  exact irred_V0_of_YS hS hst hnd h htD hxM hx3 hxt hfpf

@[expose] noncomputable def rhoX_YS (hst : S.Asc512Standing) (hc : center S.LbarAsc = ⊥) :
    (S.LbarAsc ⧸ center S.LbarAsc) →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S) :=
  (actL_YS hst).comp (AS35YL.quotEquiv_YL S.LbarAsc hc).toMonoidHom

theorem rhoX_YS_mk (hst : S.Asc512Standing) (hc : center S.LbarAsc = ⊥) (l : S.LbarAsc) :
    rhoX_YS hst hc (QuotientGroup.mk' (center S.LbarAsc) l) = actL_YS hst l :=
  rfl

theorem rhoX_YS_injective (hst : S.Asc512Standing) (hc : center S.LbarAsc = ⊥) :
    Function.Injective (rhoX_YS hst hc) :=
  (actL_YS_injective hst).comp (AS35YL.quotEquiv_YL S.LbarAsc hc).injective

theorem exists_V0_input_of_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h5127 : S14.Asc512FiveTwelveSevenStmt) (h : RadSing_YS S)
    {t₀ : S.O} (ht₀ : t₀ ∈ S.DbarAsc) :
    ∃ ρ : (S.LbarAsc ⧸ center S.LbarAsc) →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S),
      Function.Injective ρ ∧ (∀ x v, q0_YS h (ρ x v) = q0_YS h v) ∧
      (∀ Z : Submodule (ZMod 2) (V0_YS S), (∀ x, ∀ z ∈ Z, ρ x z ∈ Z) → Z = ⊥ ∨ Z = ⊤) ∧
      ∃ d : S.LbarAsc ⧸ center S.LbarAsc, d ≠ 1 ∧ d * d = 1 ∧
        IsTypeA (q0_YS h) (ρ d) 2 := by
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hinj := rhoX_YS_injective hst hc
  have hA : IsTypeA (q0_YS h)
      (rhoX_YS hst hc (QuotientGroup.mk' (center S.LbarAsc) ⟨t₀, subset_closure ht₀⟩)) 2 := by
    rw [rhoX_YS_mk, actL_YS_apply]
    exact isTypeA_act0_YS hS hst h ht₀
  refine ⟨rhoX_YS hst hc, hinj, fun x v => ?_, fun Z hZ => ?_, _,
    fun h1 => hA.2.1 (by rw [h1, map_one]),
    hinj (((rhoX_YS hst hc).map_mul _ _).trans (hA.2.2.1.trans (rhoX_YS hst hc).map_one.symm)),
    hA⟩
  · obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center S.LbarAsc) x
    rw [rhoX_YS_mk, actL_YS_apply]
    exact q0_act0_YS h hst _ v
  · refine irred_V0_YS hS hst hnd h5127 h Z fun l hl z hz => ?_
    have := hZ (QuotientGroup.mk' (center S.LbarAsc) ⟨l, hl⟩) z hz
    rwa [rhoX_YS_mk, actL_YS_apply] at this

theorem exists_V0_input_YS (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (h5127 : S14.Asc512FiveTwelveSevenStmt) (h : RadSing_YS S) :
    ∃ ρ : (S.LbarAsc ⧸ center S.LbarAsc) →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S),
      Function.Injective ρ ∧ (∀ x v, q0_YS h (ρ x v) = q0_YS h v) ∧
      (∀ Z : Submodule (ZMod 2) (V0_YS S), (∀ x, ∀ z ∈ Z, ρ x z ∈ Z) → Z = ⊥ ∨ Z = ⊤) ∧
      ∃ d : S.LbarAsc ⧸ center S.LbarAsc, d ≠ 1 ∧ d * d = 1 ∧
        IsTypeA (q0_YS h) (ρ d) 2 :=
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  exists_V0_input_of_YS hS hst hnd h5127 h (DbarAsc_nonempty_YL (S := S)).some_mem

theorem finrank_V0_add_YS :
    finrank (ZMod 2) (V0_YS S) + finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) +
      finrank (ZMod 2) (fixW_YS S) = 2 * S.width ∧
    finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) ≤ finrank (ZMod 2) (fixW_YS S) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have h1 : finrank (ZMod 2) (V0_YS S) + finrank (ZMod 2) (AS35YS.radU S.q (commU_YS S)) =
      finrank (ZMod 2) (commU_YS S) :=
    Submodule.finrank_quotient_add_finrank (AS35YS.radU S.q (commU_YS S))
  have h2 := finrank_commU_add_YS (S := S)
  refine ⟨by omega, ?_⟩
  let f : AS35YS.radU S.q (commU_YS S) →ₗ[ZMod 2] fixW_YS S :=
    { toFun := fun x => ⟨((x : commU_YS S) : S.Qt),
        mem_fixW_of_mem_radU_YS (AS35YS.mem_radU.mp x.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y hxy => ?_
  exact Subtype.ext (Subtype.ext (congrArg (fun z : fixW_YS S => (z : S.Qt)) hxy))

theorem false_of_u33_YS (hmod : S14.Asc512U33ModuleInput) (hS : S.SixHyp)
    (hst : S.Asc512Standing) (h5127 : S14.Asc512FiveTwelveSevenStmt)
    (hfam : S14.Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc) (h : RadSing_YS S) :
    False := by
  obtain ⟨hnd, hL⟩ := hfam
  obtain ⟨ρ, hinj, hiso, hirr, d, hd1, hdd, hdA⟩ := exists_V0_input_YS hS hst hnd h5127 h
  exact hmod _ hL _ (q0_YS h) (q0_YS_nondegenerate h) ρ hinj hiso hirr d hd1 hdd
    hdA.2.2.2.1.le

end Setting

end CFSG.LargeExtraspecial
