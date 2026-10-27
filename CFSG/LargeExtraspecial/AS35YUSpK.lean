module

public import CFSG.LargeExtraspecial.AS35YTCaseB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] noncomputable def fixWGroup_YU : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) where
  carrier := {g | ∀ w ∈ fixW_YS S, g w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb w hw => by
    rw [LinearEquiv.mul_apply, hb w hw, ha w hw]
  inv_mem' := fun {a} ha w hw => by
    have e : a⁻¹ (a w) = w := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rwa [ha w hw] at e

theorem sub_mem_of_fix_YU {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hgU : ∀ u ∈ commU_YS S, g u = u)
    (hgW : ∀ w ∈ fixW_YS S, g w = w) (x : S.Qt) :
    g x - x ∈ fixW_YS S ∧ g x - x ∈ commU_YS S := by
  have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg
  refine ⟨mem_fixW_of_mem_radU_YS fun u hu => ?_, mem_commU_YS.mpr fun w hw => ?_⟩
  · rw [polar_sub_left, ← hgU u hu, hpol, hgU u hu, sub_self]
  · rw [polar_sub_left, ← hgW w hw, hpol, hgW w hw, sub_self]

theorem eq_one_of_quo_YU {r : S.Qt} (hrW : r ∈ fixW_YS S) (hr : S.q r = 1)
    (hR : ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r) {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hgW : ∀ w ∈ fixW_YS S, g w = w)
    (heven : Even (finrank (ZMod 2) (commSpace g)))
    (hquo : ∀ u ∈ commU_YS S, ∀ u' ∈ commU_YS S, polar S.q (g u - u) u' = 0) : g = 1 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hiso := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
  have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg
  have hgU' : ∀ u ∈ commU_YS S, g u ∈ commU_YS S := fun u hu =>
    mem_commU_YS.mpr fun w hw => by
      rw [← hgW w hw, hpol]
      exact mem_commU_YS.mp hu w hw
  have hgU : ∀ u ∈ commU_YS S, g u = u := by
    intro u hu
    rcases hR _ (mem_fixW_of_mem_radU_YS (hquo u hu))
        ((commU_YS S).sub_mem (hgU' u hu) hu) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have e : g u = u + r := by rw [← h]; abel
      have h1 := hiso u
      rw [e, QuadraticMap.map_add S.q, hr, mem_commU_YS.mp hu r hrW] at h1
      have h10 : (1 : ZMod 2) = 0 := by linear_combination h1
      exact one_ne_zero h10
  have hr0 : r ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hr
    exact zero_ne_one hr
  have hle : commSpace g ≤ (ZMod 2) ∙ r := by
    intro y hy
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
    obtain ⟨h1, h2⟩ := sub_mem_of_fix_YU hg hgU hgW x
    rcases hR _ h1 h2 with h | h
    · rw [h]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self r
  have h1 : finrank (ZMod 2) (commSpace g) ≤ 1 :=
    (Submodule.finrank_mono hle).trans (finrank_span_singleton (K := ZMod 2) hr0).le
  have h0 : finrank (ZMod 2) (commSpace g) = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact A2Mod.commSpace_eq_bot_iff.mp (Submodule.finrank_eq_zero.mp h0)

theorem mem_LbarAsc_of_odd_psp_YU (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hnd : InspNondeg _ S.EhatAsc) {m : ℕ}
    (hL : LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp m 2 1)
    (hdim : finrank (ZMod 2) (commU_YS S) = 2 * m + 1) {r : S.Qt} (hrW : r ∈ fixW_YS S)
    (hrU : r ∈ commU_YS S) (hr : S.q r = 1)
    (hR : ∀ v ∈ fixW_YS S, v ∈ commU_YS S → v = 0 ∨ v = r) {s : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) (hsW : ∀ w ∈ fixW_YS S, s w = w)
    (heven : Even (finrank (ZMod 2) (commSpace s))) : (⟨s, hs⟩ : S.O) ∈ S.LbarAsc := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := AS35YR.finite_linearEquiv_YR
  have : Finite (V0_YS S) := Module.finite_of_finite (ZMod 2)
  have : Finite (V0_YS S ≃ₗ[ZMod 2] V0_YS S) := AS35YR.finite_linearEquiv_YR
  have hc := center_LbarAsc_eq_bot_YL hS hst hnd
  have hr0 : r ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at hr
    exact zero_ne_one hr
  set K : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := omegaGroup S.q S.q_nondegenerate ⊓ fixWGroup_YU S
    with hK
  set LL : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) := S.LbarAsc.map S.O.subtype with hLL
  have hLK : LL ≤ K := by
    have hle : S.LbarAsc ≤ (omegaGroup S.q S.q_nondegenerate).subgroupOf S.O := by
      show closure S.DbarAsc ≤ _
      rw [closure_le]
      intro d hd
      have hdA := isTypeA_of_mem_DbarAsc_YL hS hd
      rw [SetLike.mem_coe, mem_subgroupOf, mem_omegaGroup]
      exact ⟨d.2, by rw [hdA.2.2.2.1]; exact even_two⟩
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨mem_subgroupOf.mp (hle hx), fun w hw => mem_fixW_YS.mp hw x hx⟩
  have hiso : ∀ g ∈ K, ∀ v, S.q (g v) = S.q v := fun g hg v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_omegaGroup.mp (mem_inf.mp hg).1).1 v
  have hUinv : ∀ g ∈ K, ∀ u ∈ commU_YS S, g u ∈ commU_YS S := fun g hg u hu =>
    mem_commU_YS.mpr fun w hw => by
      rw [← (mem_inf.mp hg).2 w hw,
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (mem_omegaGroup.mp (mem_inf.mp hg).1).1]
      exact mem_commU_YS.mp hu w hw
  set φ := AS35YS.quoHom S.q (commU_YS S) K hiso hUinv with hφ
  have hmem : ∀ k : K, φ k ∈ TauCeti.BilinForm.isometryGroup (AS35YS.bQuo S.q (commU_YS S)) :=
    fun k => TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun v w => AS35YS.bQuo_quoHom k v w
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    obtain ⟨hkΩ, hkW⟩ := mem_inf.mp k.2
    refine Subtype.ext (eq_one_of_quo_YU hrW hr hR (mem_omegaGroup.mp hkΩ).1 hkW
      (mem_omegaGroup.mp hkΩ).2 fun u hu u' hu' => ?_)
    have e : φ k (Submodule.Quotient.mk (⟨u, hu⟩ : commU_YS S)) =
        Submodule.Quotient.mk ⟨u, hu⟩ := by
      rw [hk]
      rfl
    rw [hφ, AS35YS.quoHom_mk, Submodule.Quotient.eq] at e
    exact AS35YS.mem_radU.mp e u' hu'
  obtain ⟨j, hjV, hjU, hcard, -⟩ := caseB_YT hst hrW hrU hr0
  have hmj := AS35YT.le_of_le_spOrd_of_PSp hL (by rw [card_quot_eq_YT hc]; exact hcard)
  have hjm : j = m := by omega
  subst hjm
  have h1 := Nat.card_le_card_of_injective
    (fun k : K => (⟨φ k, hmem k⟩ :
      TauCeti.BilinForm.isometryGroup (AS35YS.bQuo S.q (commU_YS S))))
    fun a b hab => hinj (congrArg Subtype.val hab)
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup j
    (AS35YS.bQuo S.q (commU_YS S)) AS35YS.bQuo_isAlt AS35YS.bQuo_nondegenerate hjV,
    Nat.card_zmod] at h1
  have hLcard : Nat.card S.LbarAsc = 2 ^ (j ^ 2) * ∏ i ∈ Finset.Icc 1 j, (2 ^ (2 * i) - 1) := by
    rw [← card_quot_eq_YT hc, (A2Mod.Ord.card_of_lieModel_PSp hL).2, AS35YT.ordBC_two_eq',
      _root_.sq]
  have hLLc : Nat.card LL = Nat.card S.LbarAsc :=
    Subgroup.card_map_of_injective S.O.subtype_injective
  have heq : LL = K := Subgroup.eq_of_le_of_card_ge hLK (by rw [hLLc, hLcard]; exact h1)
  have hsK : s ∈ K := mem_inf.mpr ⟨mem_omegaGroup.mpr ⟨hs, heven⟩, hsW⟩
  rw [← heq] at hsK
  obtain ⟨x, hx, hxs⟩ := hsK
  have : x = ⟨s, hs⟩ := Subtype.ext hxs
  rwa [← this]

end Setting

end CFSG.LargeExtraspecial
