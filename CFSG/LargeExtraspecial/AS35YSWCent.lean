module

public import CFSG.LargeExtraspecial.AS35YSU33
public import CFSG.LargeExtraspecial.AS35YSWModel
public import CFSG.LargeExtraspecial.AS35QCoCent
public import CFSG.LargeExtraspecial.AS35YFBase
public import CFSG.LargeExtraspecial.AS35YRFrameB
public import CFSG.LargeExtraspecial.AS35YSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions
open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

namespace AS35YS

section Refl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem eq_refl_of_commSpace_le {v : V} (hqv : q v = 1) {c : V ≃ₗ[ZMod 2] V}
    (hc : ∀ w, q (c w) = q w) (hcv : ∀ w, c w - w ∈ (ZMod 2) ∙ v) (hc1 : c ≠ 1) :
    ∀ w, c w = w + polar q w v • v := by
  have hform : ∀ w, ∃ a : ZMod 2, c w = w + a • v := fun w => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hcv w)
    exact ⟨a, by rw [ha]; abel⟩
  have hP1 : ∀ w, polar q w v = 0 → c w = w := by
    intro w hw
    obtain ⟨a, ha⟩ := hform w
    have hq := hc w
    rw [ha, QuadraticMap.map_add (⇑q) w (a • v), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, hw, hqv, smul_zero, add_zero, smul_eq_mul, mul_one,
      add_eq_left] at hq
    rcases AS35YR.Frame.zmod2_cases_YR a with rfl | rfl
    · rw [ha, zero_smul, add_zero]
    · exact absurd hq (by decide)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, c w₀ ≠ w₀ := by
    by_contra h
    push Not at h
    exact hc1 (LinearEquiv.ext h)
  have hpw₀ : polar q w₀ v = 1 :=
    (AS35YR.Frame.zmod2_cases_YR _).resolve_left fun h => hw₀ (hP1 w₀ h)
  have hcw₀ : c w₀ = w₀ + v := by
    obtain ⟨a, ha⟩ := hform w₀
    rcases AS35YR.Frame.zmod2_cases_YR a with rfl | rfl
    · rw [zero_smul, add_zero] at ha
      exact absurd ha hw₀
    · rw [ha, one_smul]
  intro w
  rcases AS35YR.Frame.zmod2_cases_YR (polar q w v) with h | h
  · rw [h, zero_smul, add_zero]
    exact hP1 w h
  · have h2 : polar q (w + w₀) v = 0 := by
      rw [QuadraticMap.polar_add_left, h, hpw₀]
      decide
    have h3 := hP1 _ h2
    rw [map_add, hcw₀] at h3
    rw [h, one_smul]
    calc c w = c w + (w₀ + v) - (w₀ + v) := by abel
      _ = w + w₀ - (w₀ + v) := by rw [h3]
      _ = w - v := by abel
      _ = w + v := by rw [sub_eq_add_neg, ZModModule.neg_eq_self]

end Refl

end AS35YS

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_seven_u33_YS
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1) :
    ∃ x : S.O, x ∈ S.LbarAsc ∧ x ^ 7 = 1 ∧ x ≠ 1 := by
  have := AS35QCo.finite_lin S
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  obtain ⟨e⟩ := equiv_of_lieModel hL
  have hcard : Nat.card S.LbarAsc = 6048 := by
    rw [Nat.card_congr ((AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e).toEquiv,
      AS35YR.card_QP]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := S.LbarAsc) 7 (by rw [hcard]; norm_num)
  refine ⟨l, l.2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← hl, pow_orderOf_eq_one, Subgroup.coe_one]
  · intro h
    have h1 : l = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hl
    norm_num at hl

theorem fixW_le_span_YS (h4 : S.width = 4) {x : S.O} (hxL : x ∈ S.LbarAsc) (hx7 : x ^ 7 = 1)
    (hx1 : x ≠ 1) {v : S.Qt} (hvW : v ∈ fixW_YS S)
    (hvperp : ∀ w ∈ fixW_YS S, polar S.q v w = 0) (hv0 : v ≠ 0) :
    fixW_YS S ≤ (ZMod 2) ∙ v := by
  have := AS35QCo.finite_Qt S
  have hx := AS35QCo.seven_hyp S h4 hx7 hx1
  obtain ⟨hF2, -, -⟩ := hx.finrank_fixSpace
  have hWx : fixW_YS S ≤ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := fun w hw =>
    mem_fixSpace.mpr (hw x hxL)
  have hvspan : (ZMod 2) ∙ v ≤ fixW_YS S := (Submodule.span_singleton_le_iff_mem _ _).mpr hvW
  by_cases h1 : finrank (ZMod 2) (fixW_YS S) ≤ 1
  · exact (Submodule.eq_of_le_of_finrank_le hvspan
      (by rw [finrank_span_singleton hv0]; exact h1)).ge
  · exfalso
    have hWeq : fixW_YS S = fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      Submodule.eq_of_le_of_finrank_le hWx (by rw [hF2]; omega)
    have hvC : v ∈ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [AS35QCo.commSpace_eq_orthogonal S.q_nondegenerate hx.isom,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [← hWeq] at hn
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact hvperp n hn
    have hmem : v ∈ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
      ⟨hWx hvW, hvC⟩
    rw [AS35QCo.fixSpace_inf_commSpace ⟨3, rfl⟩ hx.pow, Submodule.mem_bot] at hmem
    exact hv0 hmem

theorem mbar_fix_YS (hst : S.Asc512Standing) {v : S.Qt} (hvW : v ∈ fixW_YS S)
    (hW : fixW_YS S ≤ (ZMod 2) ∙ v) (hv0 : v ≠ 0) {m : S.O} (hm : m ∈ S.Mbar) :
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hW (fixW_YS_invariant hst hm hvW))
  rcases AS35YR.Frame.zmod2_cases_YR a with rfl | rfl
  · rw [zero_smul] at ha
    exact absurd ((m : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (ha.symm.trans (map_zero _).symm)) hv0
  · rw [one_smul] at ha
    exact ha.symm

theorem eq_one_of_mem_cg_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h4 : S.width = 4)
    {x : S.O} (hxL : x ∈ S.LbarAsc) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) {v : S.Qt} (hqv : S.q v = 1)
    (hvW : v ∈ fixW_YS S) (hW : fixW_YS S ≤ (ZMod 2) ∙ v) {c : S.O} (hcM : c ∈ S.Mbar)
    (hcC : c ∈ centralizer S.DbarAsc) (hc : c ^ 2 = 1 ∨ c ^ 3 = 1) : c = 1 := by
  have := AS35QCo.finite_Qt S
  have hq := S.q_nondegenerate
  have hV := AS35QCo.finrank_eq_eight S h4
  have hv0 : v ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hqv; exact zero_ne_one hqv
  have hx := AS35QCo.seven_hyp S h4 hx7 hx1
  obtain ⟨hF2, -, -⟩ := hx.finrank_fixSpace
  have hcomm : ∀ g ∈ S.LbarAsc, g * c = c * g := fun g hg =>
    AS35QCo.commute_of_mem_centralizer S hcC hg
  have hlin : ∀ g ∈ S.LbarAsc, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) * (c : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * g := fun g hg => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm g hg]
  have hcx : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * x = x * c := (hlin x hxL).symm
  have hFinf : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ :=
    AS35QCo.fixSpace_inf_commSpace ⟨3, rfl⟩ hx.pow
  by_contra hc1
  have hC1 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcne := AS35QCo.commSpace_ne_bot hC1
  have hinW : ∀ U : Submodule (ZMod 2) S.Qt,
      (∀ g ∈ S.LbarAsc, ∀ u ∈ U, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) → U ≤ (ZMod 2) ∙ v :=
    fun U hU u hu => hW fun g hg => hU g hg u hu
  rcases hc with hc2 | hc3
  ·
    have hcc : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) * c = 1 := by
      rw [← Subgroup.coe_mul, ← pow_two, hc2]
      rfl
    have hle := hx.commSpace_le_fixSpace hcx (Or.inl hcc)
    have hle' := Submodule.finrank_mono hle
    rw [hF2] at hle'
    have h2 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠ 2 := by
      intro h
      have heq : commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) = fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [h, hF2])
      have h1 : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [← heq, AS35QCo.commSpace_eq_orthogonal hq hx.isom, ← heq,
          ← AS35QCo.fixSpace_eq_orthogonal hq (AS35QCo.isom S c)]
        exact commSpace_le_fixSpace hcc
      have h0 : fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
        rw [← hFinf]
        exact le_antisymm (le_inf le_rfl h1) inf_le_left
      rw [h0, finrank_bot] at hF2
      exact absurd hF2 (by norm_num)
    have h1 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 1 := by omega
    have hcv : commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ (ZMod 2) ∙ v := by
      refine hinW _ fun g hg u hu => ?_
      by_cases hu0 : u = 0
      · rw [hu0, map_zero]
      · refine AS35QCo.Frame.eq_of_finrank_eq_one h1
          (AS35QCo.apply_mem_commSpace (hlin g hg) hu) hu ?_ hu0
        intro h
        exact hu0 ((g : S.Qt ≃ₗ[ZMod 2] S.Qt).injective (h.trans (map_zero _).symm))
    have hrefl := AS35YS.eq_refl_of_commSpace_le hqv (AS35QCo.isom S c)
      (fun w => hcv (sub_mem_commSpace _ w)) hC1
    have hcen : ∀ m ∈ S.Mbar, m * c * m⁻¹ = c := by
      intro m hm
      have hmv := mbar_fix_YS hst hvW hW hv0 hm
      have hC1' : ((m * c * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := by
        intro h
        apply hc1
        have h' : (m * c * m⁻¹ : S.O) = 1 := Subtype.ext h
        calc c = m⁻¹ * (m * c * m⁻¹) * m := by group
          _ = 1 := by rw [h']; group
      have hcv' : ∀ w, ((m * c * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ v := by
        intro w
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
          (hcv (sub_mem_commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w)))
        refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
        have e1 : ((m * c * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
            (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w)) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply]
        have e2 : (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w) = w :=
          (m : S.Qt ≃ₗ[ZMod 2] S.Qt).apply_symm_apply w
        calc a • v = a • (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by rw [hmv]
          _ = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (a • v) := (map_smul _ a v).symm
          _ = (m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt)
                ((m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w) - (m : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w) := by rw [ha]
          _ = ((m * c * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w := by rw [map_sub, e1, e2]
      have hrefl' := AS35YS.eq_refl_of_commSpace_le hqv (AS35QCo.isom S (m * c * m⁻¹)) hcv' hC1'
      refine Subtype.ext (LinearEquiv.ext fun w => ?_)
      rw [hrefl' w, hrefl w]
    have hA : ∀ a ∈ zpowers c, ∀ b ∈ zpowers c, a * b = b * a := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (zpow_mul_comm c i j)
    have hAn : ∀ m ∈ S.Mbar, ∀ a ∈ zpowers c, m * a * m⁻¹ ∈ zpowers c := by
      rintro m hm _ ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      change c ^ i = m * c ^ i * m⁻¹
      rw [← conj_zpow, hcen m hm]
    have hAM : zpowers c ≤ S.Mbar := (zpowers_le).mpr hcM
    have hcc' : c * c = 1 := by rw [← pow_two]; exact hc2
    exact hc1 (asc_eq_one_of_sq hAM hAn hA (mem_zpowers c) hcc')
  ·
    have hc3' : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hc3]
      rfl
    have hle := hx.commSpace_le_fixSpace hcx (Or.inr hc3')
    have hle' := Submodule.finrank_mono hle
    rw [hF2] at hle'
    have hev : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) % 2 = 0 := by
      have h1 := AS35QCo.mod_two_of_pow_three hc3' (W := ⊤) (fun _ _ => Submodule.mem_top)
      rw [top_inf_eq, finrank_top, hV] at h1
      have h2 := finrank_commSpace_add_finrank_fixSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)
      rw [hV] at h2
      omega
    have hU2 : finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2 := by omega
    have hnd : commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
          ⊥ := by
      rw [← AS35QCo.fixSpace_eq_orthogonal hq (AS35QCo.isom S c), inf_comm]
      exact AS35QCo.fixSpace_inf_commSpace ⟨1, rfl⟩ hc3'
    have hD : ∀ a ∈ S.DbarAsc, ∀ u ∈ commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt),
        (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := fun a ha u hu =>
      AS35QCo.eq_of_isTypeA (AS35QCo.isTypeA_of_mem_dbar S hS ha) hU2 hnd
        (fun w hw => AS35QCo.apply_mem_commSpace (hlin a (subset_closure ha)) hw) hu
    have hcv := hinW _ fun g hg u hu => AS35QCo.fixed_of_mem_lbar S hD hg u hu
    have h1 := Submodule.finrank_mono hcv
    rw [finrank_span_singleton hv0, hU2] at h1
    omega

theorem cg_trivial_YS (hS : S.SixHyp) (hst : S.Asc512Standing) (h4 : S.width = 4) {x : S.O}
    (hxL : x ∈ S.LbarAsc) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) {v : S.Qt} (hqv : S.q v = 1)
    (hvW : v ∈ fixW_YS S) (hW : fixW_YS S ≤ (ZMod 2) ∙ v) {c : S.O}
    (hc : c ∈ S.Mbar ⊓ centralizer S.DbarAsc) : c = 1 := by
  set Cg : Subgroup S.O := S.Mbar ⊓ centralizer S.DbarAsc with hCg
  have : Finite Cg := inferInstance
  have hF : CFSG.generalizedFitting Cg = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [mem_bot]
    have hd := orderOf_dvd_natCard (⟨f, hf⟩ : CFSG.generalizedFitting Cg)
    rw [Subgroup.orderOf_mk] at hd
    have hle := (Nat.le_of_dvd Nat.card_pos hd).trans hst.fstar_card
    have hpos := orderOf_pos f
    have hpow := pow_orderOf_eq_one f
    have h123 : orderOf f = 1 ∨ orderOf f = 2 ∨ orderOf f = 3 := by omega
    rcases h123 with h | h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hpow
      exact Subtype.ext (eq_one_of_mem_cg_YS hS hst h4 hxL hx7 hx1 hqv hvW hW (mem_inf.mp f.2).1
        (mem_inf.mp f.2).2 (Or.inl (by rw [← Subgroup.coe_pow, hpow]; rfl)))
    · rw [h] at hpow
      exact Subtype.ext (eq_one_of_mem_cg_YS hS hst h4 hxL hx7 hx1 hqv hvW hW (mem_inf.mp f.2).1
        (mem_inf.mp f.2).2 (Or.inr (by rw [← Subgroup.coe_pow, hpow]; rfl)))
  have hcen := CFSG.centralizer_generalizedFitting_le Cg
  rw [hF] at hcen
  have hmem : (⟨c, hc⟩ : Cg) ∈ centralizer ((⊥ : Subgroup Cg) : Set Cg) :=
    mem_centralizer_iff.mpr fun h hh => by
      rw [SetLike.mem_coe, mem_bot] at hh
      rw [hh, one_mul, mul_one]
  have h1 := hcen hmem
  rw [mem_bot] at h1
  exact congrArg Subtype.val h1

theorem conjL_YS_eq_conj (hst : S.Asc512Standing) (l : S.O) (hl : l ∈ S.LbarAsc) :
    conjL_YS hst ⟨l, LbarAsc_le_Mbar_YL hl⟩ = MulAut.conj (⟨l, hl⟩ : S.LbarAsc) := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  rw [conjL_YS_apply, MulAut.conj_apply]
  rfl

theorem iota_injective_YS (hst : S.Asc512Standing) (M : AutModel S.LbarAsc (Equiv.Perm (Fin 28)))
    (hCg : ∀ c ∈ S.Mbar ⊓ centralizer S.DbarAsc, c = 1) :
    Function.Injective (M.ι.comp (conjL_YS hst)) := by
  refine (injective_iff_map_eq_one _).mpr fun m hm => ?_
  have hm' : M.ι (conjL_YS hst m) = M.ι 1 := by
    rw [map_one]
    exact hm
  have h1 : conjL_YS hst m = 1 := M.ι_injective hm'
  have hmC : (m : S.O) ∈ S.Mbar ⊓ centralizer S.DbarAsc := by
    refine mem_inf.mpr ⟨m.2, mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact (commute_of_conjL_eq_one hst h1 ⟨d, subset_closure hd⟩).symm
  exact Subtype.ext (hCg _ hmC)

theorem iota_eq_YS (hst : S.Asc512Standing)
    (M : AutModel S.LbarAsc (Equiv.Perm (Fin 28))) (hP : M.P = QP.originalSubgroup)
    (hA : M.A = QA.originalSubgroup) (l : S.O) (hl : l ∈ S.LbarAsc) :
    (M.ι.comp (conjL_YS hst)) ⟨l, LbarAsc_le_Mbar_YL hl⟩ =
      ((M.e ⟨l, hl⟩ : M.P) : Equiv.Perm (Fin 28)) := by
  rw [MonoidHom.comp_apply, conjL_YS_eq_conj hst l hl]
  exact AS35YS.Φ_conj_eq M hP hA _

theorem exists_iota_YS
    (hst : S.Asc512Standing) (hc : center S.LbarAsc = ⊥)
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSU 3 3 1)
    (hCg : ∀ c ∈ S.Mbar ⊓ centralizer S.DbarAsc, c = 1) :
    ∃ ι : S.Mbar →* Equiv.Perm (Fin 28), Function.Injective ι ∧
      (∀ m, ι m ∈ QA.originalSubgroup) ∧
      (∀ (l : S.O) (hl : l ∈ S.LbarAsc), ι ⟨l, LbarAsc_le_Mbar_YL hl⟩ ∈ QP.originalSubgroup) ∧
      (∀ p ∈ QP.originalSubgroup,
        ∃ (l : S.O) (hl : l ∈ S.LbarAsc), ι ⟨l, LbarAsc_le_Mbar_YL hl⟩ = p) := by
  obtain ⟨e⟩ := equiv_of_lieModel hL
  obtain ⟨M, hP, hA⟩ := autModel ((AS35YL.quotEquiv_YL S.LbarAsc hc).symm.trans e)
  refine ⟨M.ι.comp (conjL_YS hst), iota_injective_YS hst M hCg, fun m => ?_, fun l hl => ?_,
    fun p hp => ?_⟩
  · exact (Subgroup.ext_iff.mp hA _).mp (M.ι_mem (conjL_YS hst m))
  · rw [iota_eq_YS hst M hP hA l hl]
    exact (Subgroup.ext_iff.mp hP _).mp (M.e ⟨l, hl⟩).2
  · obtain ⟨k, hk⟩ := M.e.surjective ⟨p, (Subgroup.ext_iff.mp hP _).mpr hp⟩
    refine ⟨k, k.2, ?_⟩
    rw [iota_eq_YS hst M hP hA k k.2]
    exact congrArg Subtype.val hk

theorem card_mbar_le_YS (ι : S.Mbar →* Equiv.Perm (Fin 28))
    (hι : Function.Injective ι) (hιA : ∀ m, ι m ∈ QA.originalSubgroup) :
    Nat.card S.Mbar ≤ 12096 := by
  have h := Nat.card_le_card_of_injective (fun m => (⟨ι m, hιA m⟩ : QA.originalSubgroup))
    fun a b hab => hι (congrArg Subtype.val hab)
  rwa [card_group QA QA_ok, QA_valid.2] at h

end Setting

end CFSG.LargeExtraspecial
