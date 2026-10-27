module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

section Generic

variable {G : Type} [Group G]

@[expose] noncomputable def centerQuotAction (M : Subgroup G) :
    normalizer (M : Set G) →* MulAut (M ⧸ center M) :=
  normalizerQuotMulAut (MulEquiv.refl (M ⧸ center M))

theorem centerQuotAction_apply_mk (M : Subgroup G) (n : normalizer (M : Set G)) (y : M) :
    centerQuotAction M n (QuotientGroup.mk' (center M) y) =
      QuotientGroup.mk' (center M) (M.normalizerMonoidHom n y) :=
  normalizerQuotMulAut_apply (MulEquiv.refl (M ⧸ center M)) n y

theorem normalizerQuotMulAut_eq_congr {M : Subgroup G} {X : Type*} [Group X]
    (e : M ⧸ center M ≃* X) (n : normalizer (M : Set G)) :
    normalizerQuotMulAut e n = MulAut.congr e (centerQuotAction M n) :=
  MulEquiv.ext fun _ => rfl

theorem fixedSubgroup_normalizerMonoidHom_eq {M : Subgroup G} {w : G}
    (hw : w ∈ normalizer (M : Set G)) :
    fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩) = (centralizer ({w} : Set G)).subgroupOf M := by
  ext m
  rw [mem_subgroupOf, mem_centralizer_singleton_iff]
  change M.normalizerMonoidHom ⟨w, hw⟩ m = m ↔ _
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    calc (m : G) * w = w * (m : G) * w⁻¹ * w := by rw [h1]
      _ = w * m := by group
  · intro h
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← h, mul_inv_cancel_right]

theorem map_mk_fixedSubgroup_eq {M : Subgroup G} {X : Type*} [Group X]
    (hZ : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* X) {w : G} (hw2 : orderOf w = 2)
    (hw : w ∈ normalizer (M : Set G)) :
    (fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩)).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) =
      fixedSubgroup (normalizerQuotMulAut eM ⟨w, hw⟩) := by
  rw [fixedSubgroup_normalizerMonoidHom_eq hw]
  exact E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM hw2 hw

theorem card_fixedSubgroup_quot_dvd {M : Subgroup G} {X : Type*} [Group X]
    (hZ : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* X) {w : G} (hw2 : orderOf w = 2)
    (hw : w ∈ normalizer (M : Set G)) :
    Nat.card (fixedSubgroup (normalizerQuotMulAut eM ⟨w, hw⟩)) ∣
      Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩)) := by
  rw [← map_mk_fixedSubgroup_eq hZ eM hw2 hw]
  exact Subgroup.card_map_dvd _ _

theorem factorization_card_fixedSubgroup_quot_le {M : Subgroup G} {X : Type*} [Group X]
    [Finite G] (hZ : Odd (Nat.card (center M))) (eM : M ⧸ center M ≃* X) {w : G}
    (hw2 : orderOf w = 2) (hw : w ∈ normalizer (M : Set G)) :
    (Nat.card (fixedSubgroup (normalizerQuotMulAut eM ⟨w, hw⟩))).factorization 2 ≤
      (Nat.card (fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩))).factorization 2 := by
  have : Finite X := Finite.of_equiv _ eM.toEquiv
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (card_fixedSubgroup_quot_dvd hZ eM hw2 hw) 2

theorem centerQuotAction_mul_self {M : Subgroup G} {w : G} (hw2 : orderOf w = 2)
    (hw : w ∈ normalizer (M : Set G)) :
    centerQuotAction M ⟨w, hw⟩ * centerQuotAction M ⟨w, hw⟩ = 1 := by
  rw [← _root_.sq]
  exact E6Pilot.normalizerQuotMulAut_sq_eq_one _ hw2 hw

theorem eq_one_of_mem_center_of_commute {M L : Subgroup G} (hLM : L ≤ M) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center M))) {z : M} (hz : z ∈ center M) (hzt : (z : G) * t = t * z) :
    z = 1 := by
  have hzL : (z : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact (congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hLM hl⟩))
  have hzz : (z : G) ∈ zpowers t := hKt ▸ ⟨hzL, mem_centralizer_singleton_iff.2 hzt⟩
  have hzodd := E6Pilot.odd_orderOf_of_mem_center hZ hz
  have hdvd2 : orderOf z ∣ 2 := by
    rw [← Subgroup.orderOf_coe, ← ht]
    exact orderOf_dvd_of_mem_zpowers hzz
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · rw [h2] at hzodd
    exact absurd hzodd (by decide)

theorem injective_mk_comp_subtype_of_commute {M L : Subgroup G} (hLM : L ≤ M) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center M))) {H : Subgroup M} (hH : ∀ h ∈ H, (h : G) * t = t * h) :
    Function.Injective ((QuotientGroup.mk' (center M)).comp H.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  have hzZ : (z : M) ∈ center M := by
    rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
    exact hz
  have h1 := eq_one_of_mem_center_of_commute hLM ht hKt hZ hzZ (hH _ z.2)
  exact (mem_bot).2 (Subtype.ext h1)

theorem map_mk_fixedSubgroup_eq_centerQuot {M : Subgroup G} (hZ : Odd (Nat.card (center M)))
    {w : G} (hw2 : orderOf w = 2) (hw : w ∈ normalizer (M : Set G)) :
    (fixedSubgroup (M.normalizerMonoidHom ⟨w, hw⟩)).map (QuotientGroup.mk' (center M)) =
      fixedSubgroup (centerQuotAction M ⟨w, hw⟩) := by
  have h := map_mk_fixedSubgroup_eq hZ (MulEquiv.refl (M ⧸ center M)) hw2 hw
  have e1 : (MulEquiv.refl (M ⧸ center M)).toMonoidHom.comp (QuotientGroup.mk' (center M)) =
      QuotientGroup.mk' (center M) := MonoidHom.ext fun _ => rfl
  rw [e1] at h
  exact h

theorem normalizerMonoidHom_eq_one_of_centerQuotAction_eq_one {M : Subgroup G}
    [Group.IsPerfect M] {w : G} (hw : w ∈ normalizer (M : Set G))
    (h1 : centerQuotAction M ⟨w, hw⟩ = 1) : M.normalizerMonoidHom ⟨w, hw⟩ = 1 := by
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective M
  rw [map_one]
  exact MulEquiv.ext fun x => by
    have := congrArg (fun γ : MulAut (M ⧸ center M) => γ x) h1
    exact this

end Generic

@[expose] def SpOmegaRowGlobalQuot {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type}
    [Field K] (e : L ≃* StatedSp n K) (t : G) (f : ℕ) (κ : Sp2mKind) : Prop :=
  SpGlobalCoverType e f κ ∧
    ∀ hN : t ∈ normalizer (spGlobal e : Set G),
      centerQuotAction (spGlobal e) ⟨t, hN⟩ ∉
          (MulAut.conj : spGlobal e ⧸ center (spGlobal e) →* MulAut _).range ∧
        LieModel (fixedSubgroup (centerQuotAction (spGlobal e) ⟨t, hN⟩)) .PSp n 2 f

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spOmegaRowGlobalQuot_of_coverType (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : IsLinearUnitaryKind κ) (hcov : SpGlobalCoverType e f κ) :
    SpOmegaRowGlobalQuot e t f κ := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨hqs, hZ, hty⟩ := hcov
  have hperf : Group.IsPerfect (spGlobal e) := hqs.1
  have hSperf : ⁅spGlobal e, spGlobal e⁆ = spGlobal e := isPerfect_iff.mp hperf
  obtain ⟨τ, r, hτ, hr, hτm⟩ := exists_lieModel_of_isLinearUnitaryKind hκ hty
  have hadm : StatedLieAdmissible τ r 2 f := F4Pilot.statedLieAdmissible_of_lieModel hτm
  have hS : IsSimpleGroup (spGlobal e ⧸ center (spGlobal e)) := by
    rcases hτ with rfl | rfl
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSL hτm
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSU hτm
  have hna : ∃ a b : spGlobal e ⧸ center (spGlobal e), a * b ≠ b * a := hqs.2.2
  have hLm : LieModel L .PSp n 2 f := lieModel_of_mulEquiv_statedSp e hKc (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
  refine ⟨⟨hqs, hZ, hty⟩, fun hN => ?_⟩
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ with hθdef
  set θq := centerQuotAction (spGlobal e) ⟨t, hN⟩ with hθqdef
  set π : spGlobal e →* spGlobal e ⧸ center (spGlobal e) := QuotientGroup.mk' (center (spGlobal e))
    with hπ
  have hfix : (fixedSubgroup θ).map π = fixedSubgroup θq :=
    map_mk_fixedSubgroup_eq_centerQuot hZ ht hN
  have hfixC : ∀ x : spGlobal e, x ∈ fixedSubgroup θ → (x : G) * t = t * x := by
    intro x hx
    have h1 := (Subgroup.ext_iff.1 (fixedSubgroup_normalizerMonoidHom_eq hN) x).1 hx
    rw [mem_subgroupOf, mem_centralizer_singleton_iff] at h1
    exact h1
  set L₀ : Subgroup (spGlobal e) := L.subgroupOf (spGlobal e) with hL₀
  have hL₀C : L₀ ≤ fixedSubgroup θ := by
    intro x hx
    change θ x = x
    apply Subtype.ext
    rw [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : (x : G) ∈ L := hx
    rw [← mem_centralizer_iff.1 htC (x : G) hxL, mul_inv_cancel_right]
  have hθ1 : θq ≠ 1 := by
    intro h1
    have hθ1' : θ = 1 := normalizerMonoidHom_eq_one_of_centerQuotAction_eq_one hN h1
    have hSt : spGlobal e ≤ centralizer ({t} : Set G) := fun g hg => by
      rw [mem_centralizer_singleton_iff]
      exact hfixC ⟨g, hg⟩ (by change θ ⟨g, hg⟩ = ⟨g, hg⟩; rw [hθ1', MulAut.one_apply])
    have heq : spGlobal e = L :=
      le_antisymm (std_perfect_le hset.standardSetting hOut htC ht hSperf hSt) hLS
    have hZ1 : center (spGlobal e) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      exact (mem_bot).2 (eq_one_of_mem_center_of_commute hLS ht hKt hZ hz
        (mem_centralizer_singleton_iff.1 (hSt z.2)))
    have hXL : spGlobal e ⧸ center (spGlobal e) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hZ1).trans
        (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr heq))
    have hLτ : LieModel L τ r 2 f := LieType.CurtisTits.lieModel_of_mulEquiv hXL hτm
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical n) hLm
      (Or.inl (by rcases hτ with rfl | rfl <;> decide)) (by rcases hτ with rfl | rfl <;> decide)
      hadm hLτ
  have hθ2 : orderOf θq = 2 :=
    orderOf_eq_prime (by rw [_root_.sq]; exact centerQuotAction_mul_self ht hN) hθ1
  have hinjL : Function.Injective (π.comp L₀.subtype) :=
    injective_mk_comp_subtype_of_commute hLS ht hKt hZ fun x hx =>
      hfixC x (hL₀C hx)
  have hrangeL : (π.comp L₀.subtype).range = L₀.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hL₀q : L₀.map π ≤ fixedSubgroup θq := hfix ▸ Subgroup.map_mono hL₀C
  let eL : L₀.map π ≃* L :=
    (MulEquiv.subgroupCongr hrangeL.symm).trans
      ((MonoidHom.ofInjective hinjL).symm.trans (Subgroup.subgroupOfEquivOfLe hLS))
  let D : Subgroup (fixedSubgroup θq) := (L₀.map π).subgroupOf (fixedSubgroup θq)
  have eD : D ≃* L := (Subgroup.subgroupOfEquivOfLe hL₀q).trans eL
  have hDm : LieModel D .PSp n 2 f := LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLm
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hDm).1.1
  have hDn : D.Normal := by
    refine ⟨fun d hd c => ?_⟩
    have hd' : ((d : fixedSubgroup θq) : spGlobal e ⧸ center (spGlobal e)) ∈ L₀.map π := hd
    obtain ⟨l, hl, hld⟩ := hd'
    have hc' : ((c : fixedSubgroup θq) : spGlobal e ⧸ center (spGlobal e)) ∈
        (fixedSubgroup θ).map π := by
      rw [hfix]
      exact c.2
    obtain ⟨y, hy, hyc⟩ := hc'
    have hyN := hCN (mem_centralizer_singleton_iff.2 (hfixC y hy))
    have hlL : (l : G) ∈ L := hl
    have hmem : (y : G) * l * (y : G)⁻¹ ∈ L := (mem_normalizer_iff.1 hyN _).1 hlL
    change (((c * d * c⁻¹ : fixedSubgroup θq) : spGlobal e ⧸ center (spGlobal e))) ∈ L₀.map π
    refine ⟨y * l * y⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hld, hyc]
  have hD : IsComponent D := ⟨hDq, hDn.isSubnormal⟩
  by_cases hin : θq ∈ (MulAut.conj : spGlobal e ⧸ center (spGlobal e) →* MulAut _).range
  · exact (F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
      (involutionCentralizersComponentFree_of_evenLieType ⟨τ, r, f, hadm, hτm⟩) hθ2 hin
      hD).elim
  · refine ⟨hin, ?_⟩
    rcases hτ with rfl | rfl
    · exact (catSp2mEvenOuterFamily_PSL (sp2mEvenTypeDetClassical n) _ hS hna r f
        hadm hτm θq hθ2 hin f D hD hDm).2
    · exact (catSp2mEvenOuterFamily_PSU (sp2mEvenTypeDetClassical n) _ hS hna r f
        hadm hτm θq hθ2 hin f D hD hDm).2

end Global

end CFSG.SeitzReduction.SymplecticPilot
