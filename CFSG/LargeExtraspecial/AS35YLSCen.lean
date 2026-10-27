module

public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YL

theorem LbarAsc_le_centralizer_YL :
    S.LbarAsc ≤ centralizer ((S.Mbar ⊓ centralizer S.DbarAsc : Subgroup S.O) : Set S.O) := by
  show closure S.DbarAsc ≤ _
  rw [closure_le]
  intro d hd
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro c hc
  exact ((mem_centralizer_iff.mp (mem_inf.mp hc).2) d hd).symm

theorem card_center_LbarAsc_le_three_YL (hst : S.Asc512Standing) :
    Nat.card (center S.LbarAsc) ≤ 3 := by
  set C : Subgroup S.O := S.Mbar ⊓ centralizer S.DbarAsc with hC
  set Z : Subgroup S.O := (center S.LbarAsc).map S.LbarAsc.subtype with hZ
  have hLC := LbarAsc_le_centralizer_YL (S := S)
  have hZC : Z ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_inf.mpr ⟨LbarAsc_le_Mbar_YL z.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨d, subset_closure hd⟩)
  have hcomm : ∀ x ∈ Z, ∀ c ∈ C, c * x = x * c := by
    rintro _ ⟨z, -, rfl⟩ c hc
    exact mem_centralizer_iff.mp (hLC z.2) c hc
  have hnorm : (Z.subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    have h := hcomm _ hx _ c.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h, mul_inv_cancel_right]
    exact hx
  have : IsMulCommutative (Z.subgroupOf C) := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hcomm _ (mem_subgroupOf.mp b.2) _ (a : C).2))⟩⟩
  have hnil : Group.IsNilpotent (Z.subgroupOf C) := CommGroup.isNilpotent
  have hle : Z.subgroupOf C ≤ CFSG.generalizedFitting C :=
    (le_sSup (s := {N : Subgroup C | N.Normal ∧ Group.IsNilpotent N}) ⟨hnorm, hnil⟩).trans
      (le_sup_left : CFSG.fittingSubgroup C ≤ CFSG.fittingSubgroup C ⊔ CFSG.layer C)
  calc Nat.card (center S.LbarAsc) = Nat.card Z :=
        (Subgroup.card_map_of_injective S.LbarAsc.subtype_injective).symm
    _ = Nat.card (Z.subgroupOf C) := (Nat.card_congr (subgroupOfEquivOfLe hZC).toEquiv).symm
    _ ≤ Nat.card (CFSG.generalizedFitting C) := Subgroup.card_le_of_le hle
    _ ≤ 3 := hst.fstar_card

theorem card_center_LbarAsc_ne_two_YL (hst : S.Asc512Standing) :
    Nat.card (center S.LbarAsc) ≠ 2 := by
  intro h2
  set Z : Subgroup S.O := (center S.LbarAsc).map S.LbarAsc.subtype with hZ
  have hcard : Nat.card Z = 2 := by
    rw [Subgroup.card_map_of_injective S.LbarAsc.subtype_injective, h2]
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hZM : Z ≤ S.Mbar := by
    rintro _ ⟨z, -, rfl⟩
    exact LbarAsc_le_Mbar_YL z.2
  have hconj : ∀ m ∈ S.Mbar, ∀ x ∈ Z, m * x * m⁻¹ ∈ Z := by
    rintro m hm _ ⟨z, hz, rfl⟩
    have hzL : m * (z : S.O) * m⁻¹ ∈ S.LbarAsc := hst.normal m hm z z.2
    refine ⟨⟨_, hzL⟩, mem_center_iff.mpr fun l => Subtype.ext ?_, rfl⟩
    have hl' : m⁻¹ * (l : S.O) * m⁻¹⁻¹ ∈ S.LbarAsc := hst.normal _ (S.Mbar.inv_mem hm) l l.2
    have hc : m⁻¹ * (l : S.O) * m⁻¹⁻¹ * z = z * (m⁻¹ * l * m⁻¹⁻¹) :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨_, hl'⟩)
    rw [inv_inv] at hc
    show (l : S.O) * (m * z * m⁻¹) = m * z * m⁻¹ * l
    calc (l : S.O) * (m * z * m⁻¹) = m * ((m⁻¹ * l * m) * z) * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * l * m)) * m⁻¹ := by rw [hc]
      _ = m * z * m⁻¹ * l := by group
  have hnorm : S.Mbar ≤ normalizer (Z : Set S.O) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hconj m hm x, fun hx => ?_⟩
    have := hconj m⁻¹ (S.Mbar.inv_mem hm) _ hx
    rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x by group] at this
  have hbot := S.eq_bot_of_normalized_L hZM hnorm hZ2
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

theorem center_LbarAsc_eq_bot_YL (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) : center S.LbarAsc = ⊥ := by
  have h3 := card_center_LbarAsc_le_three_YL hst
  have h2 := card_center_LbarAsc_ne_two_YL hst
  have hpos : 0 < Nat.card (center S.LbarAsc) := Nat.card_pos
  by_cases h1 : Nat.card (center S.LbarAsc) = 1
  · exact Subgroup.card_eq_one.mp h1
  exfalso
  have hc3 : Nat.card (center S.LbarAsc) = 3 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := center S.LbarAsc) 3 (by rw [hc3])
  set w : S.O := ((ω : S.LbarAsc) : S.O) with hw
  set W : S.Qt ≃ₗ[ZMod 2] S.Qt := (w : S.Qt ≃ₗ[ZMod 2] S.Qt) with hWdef
  have hwo : orderOf w = 3 := by
    rw [hw, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hω]
  have hwL : w ∈ S.LbarAsc := (ω : S.LbarAsc).2
  have hwc : ∀ l ∈ S.LbarAsc, W * (l : S.Qt ≃ₗ[ZMod 2] S.Qt) = (l : S.Qt ≃ₗ[ZMod 2] S.Qt) * W := by
    intro l hl
    exact congrArg Subtype.val (congrArg Subtype.val (mem_center_iff.mp ω.2 ⟨l, hl⟩)).symm
  have hW3 : W ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hwo] at h
    have := congrArg Subtype.val h
    simpa [hWdef] using this
  have hiso : ∀ v, S.q (W v) = S.q v := fun v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup w.2 v
  obtain ⟨x, hx, y, hy, h4⟩ := hnd
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨e, he, rfl⟩ := hy
  have h4' := AS35YL.orderOf_eq_four_of_mk_YL
    (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hd he h4
  have h4l : orderOf (((d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      = 4 := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, h4']
  have hdA := isTypeA_of_mem_DbarAsc_YL hS hd
  obtain ⟨a, haC, ha0, hWa⟩ := exists_fix_of_orderOf_eq_four_YL S.q_nondegenerate hdA
    (isTypeA_of_mem_DbarAsc_YL hS he) h4l hiso (hwc _ (subset_closure hd))
    (hwc _ (subset_closure he))
  have hWd : ∀ v ∈ commSpace ((d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt), W v = v :=
    apply_eq_of_fix_of_pow_three_YL hW3 hdA.2.2.2.1
      (fun v hv => map_mem_commSpace_of_commute_YL (hwc _ (subset_closure hd)) hv) haC ha0 hWa
  have hall : ∀ d' ∈ S.DbarAsc, ∀ v ∈ commSpace ((d' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt), W v = v := by
    intro d' hd' v hv
    obtain ⟨g, hg, hgd⟩ := hst.conj _ hd d' hd'
    have hv' : v ∈ commSpace (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) := by
      rw [← hgd] at hv
      simpa using hv
    have hu := hWd _ (inv_apply_mem_commSpace_conj_YL hv')
    have hWg := hwc _ hg
    have e1 : v = ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ v) := (LinearEquiv.apply_symm_apply _ v).symm
    rw [e1, ← LinearEquiv.mul_apply, hWg, LinearEquiv.mul_apply, hu]
  have hclos : ∀ l ∈ S.LbarAsc, ∀ v, W (((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) =
      ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem d' hd' => exact fun v => hall d' hd' _ (sub_mem_commSpace _ v)
    | one => intro v; simp
    | mul a b _ _ iha ihb =>
      intro v
      have e : ((a * b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
          (((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
            ((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) +
          (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
        abel
      rw [e, map_add, iha, ihb]
    | inv a _ iha =>
      intro v
      have e : ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
          -(((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) -
            ((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
        have h1 : ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((a⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
            = v := by
          rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
          rfl
        rw [h1, neg_sub]
      rw [e, map_neg, iha]
  have hsq : W * W = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have h := hclos w hwL v
    rw [map_sub] at h
    change W (W v) = v
    change W (W v) - W v = W v - v at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, sub_add_eq_add_sub, add_self_YL, zero_sub, OrthoF2.vec_neg]
  have hw2 : w * w = 1 := Subtype.ext hsq
  have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hw2])
  rw [hwo] at hdvd
  exact absurd hdvd (by norm_num)

@[expose] noncomputable def actHat_YL (hc : center S.LbarAsc = ⊥) :
    S.LbarAsc ⧸ center S.LbarAsc →* (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  S.O.subtype.comp (quotEmb_YL S.LbarAsc hc)

theorem actHat_YL_injective (hc : center S.LbarAsc = ⊥) : Function.Injective (actHat_YL hc) :=
  S.O.subtype_injective.comp (quotEmb_YL_injective _ hc)

@[simp] theorem actHat_YL_mk (hc : center S.LbarAsc = ⊥) (l : S.LbarAsc) :
    actHat_YL hc (QuotientGroup.mk' (center S.LbarAsc) l) =
      ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl

theorem actHat_YL_isometry (hc : center S.LbarAsc = ⊥) (x : S.LbarAsc ⧸ center S.LbarAsc)
    (v : S.Qt) : S.q (actHat_YL hc x v) = S.q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (quotEmb_YL S.LbarAsc hc x).2 v

theorem card_quot_le_card_O_YL (hc : center S.LbarAsc = ⊥) :
    Nat.card (S.LbarAsc ⧸ center S.LbarAsc) ≤ Nat.card S.O :=
  Nat.card_le_card_of_injective _ (quotEmb_YL_injective S.LbarAsc hc)

theorem irred_actHat_YL (hc : center S.LbarAsc = ⊥) (h : S.LbarIrred_YL) :
    ∀ W : Submodule (ZMod 2) S.Qt, (∀ x, ∀ w ∈ W, actHat_YL hc x w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  refine h W fun l hl w hw => ?_
  have := hW (QuotientGroup.mk' (center S.LbarAsc) ⟨l, hl⟩) w hw
  rwa [actHat_YL_mk] at this

theorem exists_inv_of_center_eq_bot_YL (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hc : center S.LbarAsc = ⊥) [h : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc)] :
    ∃ d : S.LbarAsc ⧸ center S.LbarAsc, d ∈ S.EhatAsc ∧ d ≠ 1 ∧ d * d = 1 ∧
      IsTypeA S.q (actHat_YL hc d) 2 := by
  obtain ⟨t₀, ht₀⟩ := @nonempty_of_nontrivial_YL _ _ S.DbarAsc h
  have hT : t₀ ∈ S.LbarAsc := subset_closure ht₀
  have h1 : QuotientGroup.mk' (center S.LbarAsc) ⟨t₀, hT⟩ ≠ 1 :=
    mk_ne_one_YL hst.conj (d := ⟨t₀, hT⟩) ht₀
  have h2 : QuotientGroup.mk' (center S.LbarAsc) ⟨t₀, hT⟩ *
      QuotientGroup.mk' (center S.LbarAsc) ⟨t₀, hT⟩ = 1 :=
    mul_self_of_mem_image_YL (D := S.DbarAsc) (fun _ hd => mul_self_of_mem_DbarAsc_YL hd)
      ⟨⟨t₀, hT⟩, ht₀, rfl⟩
  have h3 : IsTypeA S.q (actHat_YL hc (QuotientGroup.mk' (center S.LbarAsc) ⟨t₀, hT⟩)) 2 := by
    rw [actHat_YL_mk]
    exact isTypeA_of_mem_DbarAsc_YL hS ht₀
  exact ⟨_, mk_mem_EhatAsc_YL (d := ⟨t₀, hT⟩) ht₀, h1, h2, h3⟩

theorem not_inspNondeg_of_fpf_YL (hS : S.SixHyp) (hst : S.Asc512Standing)
    {y : S.Qt ≃ₗ[ZMod 2] S.Qt} (hy : ∀ v, S.q (y v) = S.q v)
    (hyL : ∀ l ∈ S.LbarAsc,
      y * ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * y)
    {t : S.O} (ht : t ∈ S.DbarAsc)
    (hfpf : ∀ v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), y v = v → v = 0) :
    ¬ InspNondeg _ S.EhatAsc := by
  rintro ⟨x, hx, z, hz, h4⟩
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨e, he, rfl⟩ := hz
  have h4' := AS35YL.orderOf_eq_four_of_mk_YL
    (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hd he h4
  have h4l : orderOf (((d : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
      = 4 := by
    rw [← Subgroup.coe_mul, Subgroup.orderOf_coe, h4']
  obtain ⟨a, haC, ha0, hya⟩ := exists_fix_of_orderOf_eq_four_YL S.q_nondegenerate
    (isTypeA_of_mem_DbarAsc_YL hS hd) (isTypeA_of_mem_DbarAsc_YL hS he) h4l hy
    (hyL _ (subset_closure hd)) (hyL _ (subset_closure he))
  obtain ⟨g, hg, hgd⟩ := hst.conj t ht _ hd
  have ha' : a ∈ commSpace (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) *
      ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) := by
    rw [← hgd] at haC
    simpa using haC
  have hga := inv_apply_mem_commSpace_conj_YL ha'
  have hyg : y * ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ * y :=
    (Commute.inv_right (show Commute y _ from hyL g hg)).eq
  have hfix : y (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ a) =
      ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ a := by
    rw [← LinearEquiv.mul_apply, hyg, LinearEquiv.mul_apply, hya]
  have h0 := hfpf _ hga hfix
  exact ha0 ((LinearEquiv.map_eq_zero_iff _).mp h0)

end Setting

end CFSG.LargeExtraspecial
