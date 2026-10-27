module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Generic

theorem eq_of_mk_eq_of_mul_self_eq_one {M : Type*} [Group M] (hZ : Odd (Nat.card (center M)))
    {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : (QuotientGroup.mk a : M ⧸ center M) = QuotientGroup.mk b) : a = b := by
  have hz : a⁻¹ * b ∈ center M := QuotientGroup.eq.1 hab
  have hz2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    have hc : (a⁻¹ * b) * a = a * (a⁻¹ * b) := (mem_center_iff.1 hz a).symm
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    calc (a⁻¹ * b) * (a⁻¹ * b) = (a⁻¹ * b) * a * b := by rw [hai]; group
      _ = a * (a⁻¹ * b) * b := by rw [hc]
      _ = b * b := by group
      _ = 1 := hb
  have hodd := E6Pilot.odd_orderOf_of_mem_center hZ hz
  have hdvd : orderOf (a⁻¹ * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
  have h1 : orderOf (a⁻¹ * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
  exact h1

variable {G : Type*} [Group G]

theorem normalizerQuotMulAut_trans {M : Subgroup G} {X : Type*} [Group X]
    (eM : M ⧸ center M ≃* X) (θ : MulAut X) (n : normalizer (M : Set G)) :
    normalizerQuotMulAut (eM.trans θ) n = θ * normalizerQuotMulAut eM n * θ⁻¹ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := (eM.trans θ).surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
  rw [normalizerQuotMulAut_apply]
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    normalizerQuotMulAut_apply]

theorem exists_conj_eq_iff_trans {M : Subgroup G} {X : Type*} [Group X]
    (eM : M ⧸ center M ≃* X) (θ : MulAut X) (n : normalizer (M : Set G)) (β : MulAut X) :
    (∃ φ : MulAut X, φ * normalizerQuotMulAut (eM.trans θ) n * φ⁻¹ = β) ↔
      ∃ φ : MulAut X, φ * normalizerQuotMulAut eM n * φ⁻¹ = β := by
  rw [normalizerQuotMulAut_trans]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ * θ, by rw [← hφ]; group⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ * θ⁻¹, by rw [← hφ]; group⟩

theorem mulAut_conj_conj_eq {X : Type*} [Group X] (φ : MulAut X) (y : X) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  apply MulEquiv.ext
  intro z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mulAut_mul_conj_of_apply_eq {X : Type*} [Group X] {η : MulAut X} {x : X} (hηx : η x = x) :
    η * MulAut.conj x = MulAut.conj x * η := by
  have h := mulAut_conj_conj_eq η x
  rw [hηx] at h
  calc η * MulAut.conj x = (η * MulAut.conj x * η⁻¹) * η := by group
    _ = MulAut.conj x * η := by rw [h]

end Generic

section B1

variable {G : Type*} [Group G]

theorem exists_partner_of_conj_eq_conj_mul {M : Subgroup G} (hZ : Odd (Nat.card (center M)))
    {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G}
    (htM : t ∈ normalizer (M : Set G)) {φ η : MulAut X} {x : X} (hx : x * x = 1)
    (hηx : η x = x) (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj x * η) :
    ∃ w : M, w * w = 1 ∧ t * (w : G) = w * t ∧
      eM (QuotientGroup.mk' (center M) w) = φ⁻¹ x ∧
      ∃ htw : t * (w : G) ∈ normalizer (M : Set G),
        φ * normalizerQuotMulAut eM ⟨t * w, htw⟩ * φ⁻¹ = η := by
  set A := normalizerQuotMulAut eM ⟨t, htM⟩ with hAdef
  set wb : X := φ⁻¹ x with hwb
  obtain ⟨q, hq⟩ := eM.surjective wb
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
  have hwb2 : wb * wb = 1 := by rw [hwb, ← map_mul, hx, map_one]
  have hm2 : m ^ 2 ∈ center M := by
    rw [← QuotientGroup.eq_one_iff]
    apply eM.injective
    rw [map_one, QuotientGroup.mk_pow, map_pow, sq]
    change eM (QuotientGroup.mk' (center M) m) * eM (QuotientGroup.mk' (center M) m) = 1
    rw [hq, hwb2]
  obtain ⟨w, hw2, hwm⟩ := E6Pilot.exists_sq_eq_one_mul_inv_mem_center hZ hm2
  have hww : w * w = 1 := by rw [← sq]; exact hw2
  have hwq : eM (QuotientGroup.mk' (center M) w) = wb := by
    rw [← hq]
    congr 1
    exact E6Pilot.mk_eq_of_mul_inv_mem_center hwm
  have hA : A = φ⁻¹ * (MulAut.conj x * η) * φ := by
    rw [← hφ]
    group
  have hAw : A wb = wb := by
    rw [hA, hwb]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply, hηx,
      MulAut.conj_apply, mul_inv_cancel_right]
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβ : ∀ m : M, ((β m : M) : G) = t * m * t⁻¹ := fun m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ m
  have hβw : β w = w := by
    refine eq_of_mk_eq_of_mul_self_eq_one hZ (by rw [← map_mul, hww, map_one]) hww ?_
    apply eM.injective
    have h1 := normalizerQuotMulAut_apply eM ⟨t, htM⟩ w
    rw [← hAdef, hwq, hAw] at h1
    exact h1.symm.trans hwq.symm
  have htw : t * (w : G) = w * t := by
    have h1 := congrArg Subtype.val hβw
    rw [hβ] at h1
    calc t * (w : G) = t * w * t⁻¹ * t := by group
      _ = w * t := by rw [h1]
  refine ⟨w, hww, htw, hwq, mul_mem htM (le_normalizer w.2), ?_⟩
  have hsplit : (⟨t * w, mul_mem htM (le_normalizer w.2)⟩ : normalizer (M : Set G)) =
      ⟨t, htM⟩ * ⟨(w : G), le_normalizer w.2⟩ := rfl
  rw [hsplit, map_mul, EPilot.normalizerQuotMulAut_of_mem eM w.2]
  have hw' : eM (QuotientGroup.mk' (center M) ⟨(w : G), w.2⟩) = wb := hwq
  rw [hw', ← hAdef]
  calc φ * (A * MulAut.conj wb) * φ⁻¹ = (φ * A * φ⁻¹) * (φ * MulAut.conj wb * φ⁻¹) := by group
    _ = MulAut.conj x * η * MulAut.conj x := by
        rw [hφ, mulAut_conj_conj_eq, hwb, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    _ = MulAut.conj (x * x) * η := by
        rw [mul_assoc, mulAut_mul_conj_of_apply_eq hηx, ← mul_assoc, map_mul]
    _ = η := by rw [hx, map_one, one_mul]

theorem commute_partner_of_fix {M : Subgroup G} (hZ : Odd (Nat.card (center M)))
    {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G}
    (htM : t ∈ normalizer (M : Set G)) {φ η : MulAut X} {x : X}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj x * η)
    (hfix : ∀ g : X, (MulAut.conj x * η) g = g → g * x = x * g)
    {w : M} (hww : w * w = 1) (hwq : eM (QuotientGroup.mk' (center M) w) = φ⁻¹ x)
    {c : G} (hcM : c ∈ M) (hct : c * t = t * c) : c * w = w * c := by
  set c' : M := ⟨c, hcM⟩ with hc'
  set β := M.normalizerMonoidHom ⟨t, htM⟩ with hβdef
  have hβc : β c' = c' := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨t, htM⟩ c', hc']
    change t * c * t⁻¹ = c
    rw [← hct, mul_inv_cancel_right]
  set A := normalizerQuotMulAut eM ⟨t, htM⟩ with hAdef
  have hAc : A (eM (QuotientGroup.mk' (center M) c')) = eM (QuotientGroup.mk' (center M) c') := by
    rw [hAdef, normalizerQuotMulAut_apply, ← hβdef, hβc]
  have hξc : (MulAut.conj x * η) (φ (eM (QuotientGroup.mk' (center M) c'))) =
      φ (eM (QuotientGroup.mk' (center M) c')) := by
    rw [← hφ]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hAc]
  have hcx := hfix _ hξc
  have hcw : eM (QuotientGroup.mk' (center M) c') * φ⁻¹ x =
      φ⁻¹ x * eM (QuotientGroup.mk' (center M) c') := by
    have h1 := congrArg (fun z => φ⁻¹ z) hcx
    simp only [map_mul, MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
    simpa only [MulAut.inv_apply] using h1
  have hconj : c' * w * c'⁻¹ = w := by
    refine eq_of_mk_eq_of_mul_self_eq_one hZ ?_ hww ?_
    · calc c' * w * c'⁻¹ * (c' * w * c'⁻¹) = c' * (w * w) * c'⁻¹ := by group
        _ = 1 := by rw [hww, mul_one, mul_inv_cancel]
    · apply eM.injective
      change eM (QuotientGroup.mk' (center M) (c' * w * c'⁻¹)) = eM (QuotientGroup.mk' (center M) w)
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hwq, hcw, mul_inv_cancel_right]
  have h1 := congrArg Subtype.val hconj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  calc c * (w : G) = c * w * c⁻¹ * c := by group
    _ = w * c := by rw [h1]

end B1

section B2

variable {G : Type} [Group G] [Finite G]

theorem mem_perfectCore_of_fixSubgroup_perfect {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G}
    (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G))
    (hperf : ⁅E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩),
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)⁆ =
        E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩))
    {w : M} (hww : w * w = 1) (htw : t * (w : G) = w * t) :
    (w : G) ∈ perfectCore (M ⊓ centralizer ({t} : Set G)) := by
  have : Finite X := Finite.of_equiv _ eM.toEquiv
  set π : M →* X := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  set S : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hS
  have hSπ : S.map π = E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) :=
    E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hPπ : (perfectCore S).map π = E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
    rw [CFSG.Quasithin.map_perfectCore, hSπ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]
  have hwS : w ∈ S := by
    rw [hS, mem_subgroupOf, mem_centralizer_singleton_iff]
    exact htw.symm
  obtain ⟨l, hl, hlw⟩ : π w ∈ (perfectCore S).map π := hPπ ▸ hSπ ▸ ⟨w, hwS, rfl⟩
  have hz : l⁻¹ * w ∈ center M := by
    have h1 : (QuotientGroup.mk' (center M)) l = (QuotientGroup.mk' (center M)) w :=
      eM.injective hlw
    exact QuotientGroup.eq.1 h1
  obtain ⟨k, hk⟩ := E6Pilot.odd_orderOf_of_mem_center hZ hz
  set z := l⁻¹ * w with hzdef
  have hzk : z ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one z
  have hlwz : l = w * z⁻¹ := by rw [hzdef]; group
  have hcomm : Commute w z⁻¹ := mem_center_iff.1 (inv_mem hz) w
  have hw2k : w ^ (2 * k + 1) = w := by
    rw [pow_succ, pow_mul, sq, hww, one_pow, one_mul]
  have hlpow : l ^ (2 * k + 1) = w := by
    rw [hlwz, hcomm.mul_pow, hw2k, inv_pow, hzk, inv_one, mul_one]
  have hwP : w ∈ perfectCore S := hlpow ▸ pow_mem hl _
  have hmap : (perfectCore S).map M.subtype = perfectCore (M ⊓ centralizer ({t} : Set G)) := by
    rw [CFSG.Quasithin.map_perfectCore, hS, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hmap]
  exact ⟨w, hwP, rfl⟩

theorem perfectCore_inf_centralizer_le {L : Subgroup G} (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (M : Subgroup G) :
    perfectCore (M ⊓ centralizer ({t} : Set G)) ≤ L :=
  std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)

theorem fixSubgroup_perfect_of_conj {X : Type*} [Group X] {A β φ : MulAut X}
    (h : φ * A * φ⁻¹ = β)
    (hβ : ⁅E6Pilot.fixSubgroup β, E6Pilot.fixSubgroup β⁆ = E6Pilot.fixSubgroup β) :
    ⁅E6Pilot.fixSubgroup A, E6Pilot.fixSubgroup A⁆ = E6Pilot.fixSubgroup A := by
  have hmap := map_eqLocus_eq_of_conj h
  apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
  change (⁅A.toMonoidHom.eqLocus (MonoidHom.id X), A.toMonoidHom.eqLocus (MonoidHom.id X)⁆).map
      φ.toMonoidHom = (A.toMonoidHom.eqLocus (MonoidHom.id X)).map φ.toMonoidHom
  rw [map_commutator, hmap]
  exact hβ

end B2

section XiData


theorem xi_data_of_le {K : Type} [Field K] (hK : ringChar K = 2)
    {C : Subgroup (ModGL TwistTag.E6.tag K)} (hC : C ≤ adjointGroup TwistTag.E6.tag K)
    {η : MulAut C} (hη : ∀ h : C, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ C) :
    (⟨_, hx⟩ : C) * ⟨_, hx⟩ = 1 ∧ η ⟨_, hx⟩ = ⟨_, hx⟩ ∧
      ∀ g : C, (MulAut.conj (⟨_, hx⟩ : C) * η) g = g → g * ⟨_, hx⟩ = ⟨_, hx⟩ * g := by
  obtain ⟨-, hP, hsq, hset⟩ :=
    even_E6_highest_root_graph_fixed_centralizer_intersection K hK one_ne_zero
  refine ⟨Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]; exact hsq),
    Subtype.ext (by rw [hη]; exact hP), fun g hg => ?_⟩
  have hg' : pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ = g := by
    have h1 := congrArg Subtype.val hg
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη] at h1
    exact h1
  have hmem : (g : ModGL TwistTag.E6.tag K) ∈
      {g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) |
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
            (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ = g} := ⟨hC g.2, hg'⟩
  rw [hset] at hmem
  have h2 := hmem.2.2
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  calc (g : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K e6HighestRoot 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * g *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ *
            pinnedX TwistTag.E6.tag K e6HighestRoot 1 := by rw [h2]
    _ = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * g := by group

theorem graphFixedRootGroup_E6_le_adjointGroup {K : Type} [Field K] (σ : K →+* K) :
    graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K :=
  (graphFixedRootGroup_le TwistTag.E6 K σ).trans (twistedFixedGroup_le_adjointGroup _ _ _)

end XiData

end CFSG.SeitzReduction.F4Pilot
