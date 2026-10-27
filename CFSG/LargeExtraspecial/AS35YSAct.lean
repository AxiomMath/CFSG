module

public import CFSG.LargeExtraspecial.AS35YSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] def RadSing_YS : Prop :=
  ∀ v ∈ fixW_YS S, (∀ w ∈ fixW_YS S, polar S.q v w = 0) → S.q v = 0

variable (S) in
noncomputable abbrev MbarL_YS : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.Mbar.map S.O.subtype

theorem mbarL_iso_YS : ∀ g ∈ MbarL_YS S, ∀ v, S.q (g v) = S.q v := by
  rintro _ ⟨m, -, rfl⟩ v
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup m.2 v

theorem mbarL_U_YS (hst : S.Asc512Standing) :
    ∀ g ∈ MbarL_YS S, ∀ u ∈ commU_YS S, g u ∈ commU_YS S := by
  rintro _ ⟨m, hm, rfl⟩ u hu
  exact commU_YS_invariant hst hm hu

variable (S) in
abbrev V0_YS : Type := AS35YS.Quo S.q (commU_YS S)

@[expose] noncomputable def act0_YS (hst : S.Asc512Standing) :
    S.Mbar →* (V0_YS S ≃ₗ[ZMod 2] V0_YS S) :=
  (AS35YS.quoHom S.q (commU_YS S) (MbarL_YS S) mbarL_iso_YS (mbarL_U_YS hst)).comp
    (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).toMonoidHom

theorem act0_YS_mk (hst : S.Asc512Standing) (m : S.Mbar) (u : commU_YS S) :
    act0_YS hst m (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ⟨((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u,
        commU_YS_invariant hst m.2 u.2⟩ :=
  rfl

theorem radU_sing_YS (h : RadSing_YS S) :
    ∀ v ∈ commU_YS S, (∀ u ∈ commU_YS S, polar S.q v u = 0) → S.q v = 0 :=
  fun v hvU hv => h v (mem_fixW_of_mem_radU_YS hv) (mem_commU_YS.mp hvU)

noncomputable abbrev q0_YS (h : RadSing_YS S) : QuadraticForm (ZMod 2) (V0_YS S) :=
  AS35YS.qQuo (radU_sing_YS h)

theorem q0_YS_nondegenerate (h : RadSing_YS S) : (q0_YS h).polarBilin.Nondegenerate :=
  AS35YS.qQuo_nondegenerate _

theorem q0_act0_YS (h : RadSing_YS S) (hst : S.Asc512Standing) (m : S.Mbar) (x : V0_YS S) :
    q0_YS h (act0_YS hst m x) = q0_YS h x :=
  AS35YS.qQuo_quoHom (radU_sing_YS h) (H := MbarL_YS S) (hiso := mbarL_iso_YS)
    (hU := mbarL_U_YS hst) _ x

theorem act0_YS_mem_O (h : RadSing_YS S) (hst : S.Asc512Standing) (m : S.Mbar) :
    act0_YS hst m ∈ TauCeti.QuadraticMap.orthogonalGroup (q0_YS h) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => q0_act0_YS h hst m x

theorem mk_eq_zero_YS {u : commU_YS S} :
    (Submodule.Quotient.mk u : V0_YS S) = 0 ↔ (u : S.Qt) ∈ fixW_YS S := by
  rw [Submodule.Quotient.mk_eq_zero, AS35YS.mem_radU]
  constructor
  · intro hu
    exact mem_fixW_of_mem_radU_YS hu
  · intro hu u' hu'
    rw [polar_comm]
    exact mem_commU_YS.mp hu' _ hu

theorem mk_eq_mk_YS {u u' : commU_YS S} :
    (Submodule.Quotient.mk u : V0_YS S) = Submodule.Quotient.mk u' ↔
      (u : S.Qt) - u' ∈ fixW_YS S := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_YS, Submodule.coe_sub]

theorem pow_four_of_act0_YS (hst : S.Asc512Standing) {l : S.O} (hl : l ∈ S.LbarAsc)
    (h1 : act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ = 1) : l ^ 4 = 1 := by
  set L : S.Qt ≃ₗ[ZMod 2] S.Qt := (l : S.Qt ≃ₗ[ZMod 2] S.Qt) with hL
  have hU : ∀ u ∈ commU_YS S, L u - u ∈ fixW_YS S := by
    intro u hu
    have e := LinearEquiv.congr_fun h1 (Submodule.Quotient.mk ⟨u, hu⟩)
    rw [act0_YS_mk, LinearEquiv.coe_one, id, mk_eq_mk_YS] at e
    exact e
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  set a := L v - v with ha
  have haU : a ∈ commU_YS S := sub_mem_commU_YS hl v
  set b := L a - a with hb
  have hbW : b ∈ fixW_YS S := hU a haU
  have hLb : L b = b := hbW l hl
  have hLv : L v = v + a := by rw [ha]; abel
  have hLa : L a = a + b := by rw [hb]; abel
  have h2 := AS35YL.add_self_YL a
  have h3 := AS35YL.add_self_YL b
  rw [Subgroup.coe_pow, Subgroup.coe_one, LinearEquiv.coe_one, id]
  change (L ^ 4) v = v
  rw [pow_succ, pow_succ, pow_succ, pow_one]
  simp only [LinearEquiv.mul_apply]
  have e2 : L (L v) = v + b := by
    rw [hLv, map_add, hLv, hLa, add_assoc, ← add_assoc a a b, h2, zero_add]
  have e2b : L (L b) = b := by rw [hLb, hLb]
  calc L (L (L (L v))) = L (L (v + b)) := by rw [e2]
    _ = L (L v) + L (L b) := by rw [map_add, map_add]
    _ = v := by rw [e2, e2b, add_assoc, h3, add_zero]

theorem act0_YS_eq_one (hst : S.Asc512Standing) {l : S.O} (hl : l ∈ S.LbarAsc)
    (h1 : act0_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ = 1) : l = 1 := by
  set K : Subgroup S.O :=
    { carrier := {k | ∃ hk : k ∈ S.LbarAsc, act0_YS hst ⟨k, LbarAsc_le_Mbar_YL hk⟩ = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨S.LbarAsc.mul_mem ha hb, ?_⟩
        have e : (⟨a * b, LbarAsc_le_Mbar_YL (S.LbarAsc.mul_mem ha hb)⟩ : S.Mbar) =
            ⟨a, LbarAsc_le_Mbar_YL ha⟩ * ⟨b, LbarAsc_le_Mbar_YL hb⟩ := rfl
        rw [e, map_mul, ha1, hb1, mul_one]
      one_mem' := ⟨S.LbarAsc.one_mem, map_one _⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        refine ⟨S.LbarAsc.inv_mem ha, ?_⟩
        have e : (⟨a⁻¹, LbarAsc_le_Mbar_YL (S.LbarAsc.inv_mem ha)⟩ : S.Mbar) =
            (⟨a, LbarAsc_le_Mbar_YL ha⟩ : S.Mbar)⁻¹ := rfl
        rw [e, map_inv, ha1, inv_one] } with hK
  have hKM : K ≤ S.Mbar := fun k hk => LbarAsc_le_Mbar_YL hk.1
  have hK2 : IsPGroup 2 K := by
    rintro ⟨k, hk, hk1⟩
    exact ⟨2, Subtype.ext (by simpa using pow_four_of_act0_YS hst hk hk1)⟩
  have hnorm : S.Mbar ≤ normalizer (K : Set S.O) := by
    intro m hm
    have hconj : ∀ m ∈ S.Mbar, ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
      rintro m hm k ⟨hk, hk1⟩
      refine ⟨hst.normal m hm k hk, ?_⟩
      have e : (⟨m * k * m⁻¹, LbarAsc_le_Mbar_YL (hst.normal m hm k hk)⟩ : S.Mbar) =
          ⟨m, hm⟩ * ⟨k, LbarAsc_le_Mbar_YL hk⟩ * (⟨m, hm⟩ : S.Mbar)⁻¹ := rfl
      rw [e, map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel]
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj m hm x, fun hx => ?_⟩
    have := hconj m⁻¹ (S.Mbar.inv_mem hm) _ hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at this
  have hbot := S.eq_bot_of_normalized_L hKM hnorm hK2
  have hlK : l ∈ K := ⟨hl, h1⟩
  rw [hbot, mem_bot] at hlK
  exact hlK

theorem mem_fixW_of_fix_YS {v : S.Qt}
    (hv : ∀ d ∈ S.DbarAsc, (d : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v ∈ fixW_YS S := by
  intro l hl
  induction hl using Subgroup.closure_induction with
  | mem σ hσ => exact hv σ hσ
  | one => rfl
  | mul a b _ _ ha hb =>
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hb, ha]
  | inv a _ ha =>
    have e := congrArg (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) ha
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel] at e
    exact e.symm

theorem act0_YS_fix (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    {x : V0_YS S}
    (hx : ∀ d (hd : d ∈ S.DbarAsc), act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ x = x) :
    x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    rw [mk_eq_zero_YS]
    refine mem_fixW_of_fix_YS fun d hd => ?_
    have e := hx d hd
    rw [act0_YS_mk, mk_eq_mk_YS] at e
    have hmem : ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) ∈
        fixW_YS S ⊓ commSpace (d : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨e, sub_mem_commSpace _ _⟩
    rw [fixW_inf_commSpace_YS hS hst hnd hd, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem

theorem mem_commSpace_act0_YS (hst : S.Asc512Standing) (m : S.Mbar) {y : V0_YS S}
    (hy : y ∈ commSpace (act0_YS hst m)) :
    ∃ u : commU_YS S, y = Submodule.Quotient.mk ⟨((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u,
      (commU_YS S).sub_mem (commU_YS_invariant hst m.2 u.2) u.2⟩ := by
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    refine ⟨u, ?_⟩
    rw [act0_YS_mk, ← Submodule.Quotient.mk_sub]
    rfl

theorem finrank_commSpace_act0_le_YS (hst : S.Asc512Standing) (m : S.Mbar) :
    finrank (ZMod 2) (commSpace (act0_YS hst m)) ≤
      finrank (ZMod 2) (commSpace ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set C := commSpace ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hC
  set N : Submodule (ZMod 2) (commU_YS S) := C.comap (commU_YS S).subtype with hN
  have hle : commSpace (act0_YS hst m) ≤ N.map (AS35YS.radU S.q (commU_YS S)).mkQ := by
    intro y hy
    obtain ⟨u, rfl⟩ := mem_commSpace_act0_YS hst m hy
    exact ⟨_, sub_mem_commSpace _ _, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_map_le (AS35YS.radU S.q (commU_YS S)).mkQ N
  have h3 : finrank (ZMod 2) N ≤ finrank (ZMod 2) C := by
    let f : N →ₗ[ZMod 2] C :=
      { toFun := fun x => ⟨((x : commU_YS S) : S.Qt), x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y hxy => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : S.Qt)) hxy))
  exact h1.trans (h2.trans h3)

theorem isTypeA_act0_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h : RadSing_YS S)
    {d : S.O} (hd : d ∈ S.DbarAsc) :
    IsTypeA (q0_YS h) (act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩) 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hA := isTypeA_of_mem_DbarAsc_YL hS hd
  set D := act0_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩ with hD
  have hDD : D * D = 1 := by
    rw [hD, ← map_mul]
    have e : (⟨d, DbarAsc_subset_Mbar_YL hd⟩ : S.Mbar) * ⟨d, DbarAsc_subset_Mbar_YL hd⟩ = 1 :=
      Subtype.ext (mul_self_of_mem_DbarAsc_YL hd)
    rw [e, map_one]
  have hD1 : D ≠ 1 := by
    intro h1
    have := act0_YS_eq_one hst (subset_closure hd) h1
    exact hA.2.1 (by rw [this]; rfl)
  have hzero : ∀ y ∈ commSpace D, q0_YS h y = 0 := by
    intro y hy
    obtain ⟨u, rfl⟩ := mem_commSpace_act0_YS hst _ hy
    rw [AS35YS.qQuo_mk]
    exact hA.2.2.2.2 _ (sub_mem_commSpace _ _)
  have hle := finrank_commSpace_act0_le_YS hst ⟨d, DbarAsc_subset_Mbar_YL hd⟩
  rw [← hD, hA.2.2.2.1] at hle
  have hev := even_finrank_commSpace_of_forall_eq_zero (q0_YS_nondegenerate h)
    (act0_YS_mem_O h hst _) hDD hzero
  have h1 := one_le_finrank_commSpace hD1
  refine ⟨q0_act0_YS h hst _, hD1, hDD, ?_, hzero⟩
  obtain ⟨k, hk⟩ := hev
  set n := finrank (ZMod 2) (commSpace D) with hn
  omega

theorem fpf_act0_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (hnd : InspNondeg _ S.EhatAsc)
    {t : S.O} (ht : t ∈ S.DbarAsc) {x : S.O} (hx : x ∈ S.Mbar) (hxt : x * t = t * x)
    (hfpf : ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0)
    {y : V0_YS S} (hy : y ∈ commSpace (act0_YS hst ⟨t, DbarAsc_subset_Mbar_YL ht⟩))
    (hxy : act0_YS hst ⟨x, hx⟩ y = y) : y = 0 := by
  obtain ⟨u, rfl⟩ := mem_commSpace_act0_YS hst _ hy
  set a := (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u with ha
  rw [act0_YS_mk, mk_eq_mk_YS] at hxy
  have hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a =
        (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
      rw [ha, map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hxt]
    rw [e]
    exact sub_mem_commSpace _ _
  have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a ∈
      fixW_YS S ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ⟨hxy, Submodule.sub_mem _ hxa (sub_mem_commSpace _ _)⟩
  rw [fixW_inf_commSpace_YS hS hst hnd ht, Submodule.mem_bot, sub_eq_zero] at hmem
  have ha0 := hfpf a (sub_mem_commSpace _ _) hmem
  rw [mk_eq_zero_YS]
  change a ∈ fixW_YS S
  rw [ha0]
  exact (fixW_YS S).zero_mem

end Setting

end CFSG.LargeExtraspecial
