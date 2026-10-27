module

public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Order.CompletePartialOrder
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup
import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime
import CFSG.FeitThompson.Foundations.AbelianSolvable
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup Pointwise

variable {G : Type*} [Group G] {H R X Y N : Subgroup G} {p : ℕ}

theorem isInvariantSubgroup_subgroupOf (hRX : R ≤ normalizer (X : Set G))
    (hRY : R ≤ normalizer (Y : Set G)) :
    IsInvariantSubgroup (conjOnNormalized X hRX) (Y.subgroupOf X) := by
  refine isInvariantSubgroup_iff_forall_map_eq.mpr fun r => ?_
  ext x
  simp only [Subgroup.mem_map, mem_subgroupOf]
  refine ⟨?_, fun hx => ⟨conjOnNormalized X hRX r⁻¹ x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    change ((conjOnNormalized X hRX r y : ↥X) : G) ∈ Y
    rw [conjOnNormalized_apply_coe]
    exact le_normalizer_iff.mp hRY r r.2 _ hy
  · rw [conjOnNormalized_apply_coe]
    simpa using le_normalizer_iff.mp hRY (r⁻¹ : ↥R) (r⁻¹ : ↥R).2 _ hx
  · change conjOnNormalized X hRX r (conjOnNormalized X hRX r⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

def sectionConj (hRX : R ≤ normalizer (X : Set G)) (hRY : R ≤ normalizer (Y : Set G))
    [(Y.subgroupOf X).Normal] : ↥R →* MulAut (↥X ⧸ Y.subgroupOf X) :=
  (isInvariantSubgroup_subgroupOf hRX hRY).quotientAut

@[simp]
theorem sectionConj_mk (hRX : R ≤ normalizer (X : Set G)) (hRY : R ≤ normalizer (Y : Set G))
    [(Y.subgroupOf X).Normal] (r : ↥R) (x : ↥X) :
    sectionConj hRX hRY r (QuotientGroup.mk x)
      = QuotientGroup.mk (conjOnNormalized X hRX r x) :=
  (isInvariantSubgroup_subgroupOf hRX hRY).quotientAut_mk r x

theorem coe_conjOnNormalized_apply (hRX : R ≤ normalizer (X : Set G)) (r : ↥R) (x : ↥X) :
    ((conjOnNormalized X hRX r x : ↥X) : G) = (r : G) * (x : G) * (r : G)⁻¹ :=
  conjOnNormalized_apply_coe hRX r x

theorem fixedPoints_conjOnNormalized_eq_bot (hXH : X ≤ H)
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) (hRX : R ≤ normalizer (X : Set G)) :
    FixedPoints.subgroup (conjOnNormalized X hRX).range ↥X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_fixedPoints_range_iff] at hx
  have hcent : (x : G) ∈ centralizer (R : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    have h := congrArg (Subtype.val (p := fun y : G => y ∈ X)) (hx ⟨r, hr⟩)
    rw [conjOnNormalized_apply_coe] at h
    calc r * (x : G) = r * (x : G) * r⁻¹ * r := by group
      _ = (x : G) * r := by rw [h]
  have hmem : (x : G) ∈ H ⊓ centralizer (R : Set G) := ⟨hXH x.2, hcent⟩
  rw [hCH, mem_bot] at hmem
  exact mem_bot.mpr (Subtype.ext (by rw [hmem, OneMemClass.coe_one]))

theorem coprime_natCard_of_le [H.Normal] [Finite H] (hp : p.Prime) (hR : Nat.card R = p)
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) (hXH : X ≤ H) :
    (Nat.card R).Coprime (Nat.card X) := by
  rw [hR]
  exact hp.coprime_iff_not_dvd.mpr fun hdvd =>
    not_dvd_natCard_of_inf_centralizer_eq_bot hp hR hCH (hdvd.trans (card_dvd_of_le hXH))

theorem isSolvable_of_natCard_eq_prime (hp : p.Prime) (hR : Nat.card R = p) :
    Group.IsSolvable ↥R := by
  have : Fact p.Prime := ⟨hp⟩
  have := isCyclic_of_prime_card (α := ↥R) hR
  exact isSolvable_of_isMulCommutative

theorem finite_of_natCard_eq_prime (hp : p.Prime) (hR : Nat.card R = p) : Finite ↥R :=
  Nat.finite_of_card_ne_zero (by rw [hR]; exact hp.pos.ne')

theorem fixedPoints_sectionConj_eq_bot [Finite H] [H.Normal] [Group.IsSolvable ↥H]
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥)
    (hXH : X ≤ H) (hRX : R ≤ normalizer (X : Set G)) (hRY : R ≤ normalizer (Y : Set G))
    [(Y.subgroupOf X).Normal] :
    FixedPoints.subgroup (sectionConj hRX hRY).range (↥X ⧸ Y.subgroupOf X) = ⊥ := by
  have : Finite ↥X := Finite.of_injective _ (inclusion_injective hXH)
  have : Finite ↥R := finite_of_natCard_eq_prime hp hR
  have : Group.IsSolvable ↥X := isSolvable_of_le hXH
  have : Group.IsSolvable ↥R := isSolvable_of_natCard_eq_prime hp hR
  rw [sectionConj, fixedPoints_quotientAut_range _ (coprime_natCard_of_le hp hR hCH hXH),
    fixedPoints_conjOnNormalized_eq_bot hXH hCH hRX, Subgroup.map_bot]

theorem mem_of_forall_inv_mul_conj_mem [Finite H] [H.Normal] [Group.IsSolvable ↥H]
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥)
    (hXH : X ≤ H) (hHY : H ≤ normalizer (Y : Set G))
    (hRX : R ≤ normalizer (X : Set G)) (hRY : R ≤ normalizer (Y : Set G))
    {x : G} (hx : x ∈ X) (hfix : ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ Y) : x ∈ Y := by
  have : (Y.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer (hXH.trans hHY)
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥X ⧸ Y.subgroupOf X) ∈
      FixedPoints.subgroup (sectionConj hRX hRY).range (↥X ⧸ Y.subgroupOf X) := by
    rw [mem_fixedPoints_range_iff]
    intro r
    rw [sectionConj_mk, QuotientGroup.eq, mem_subgroupOf]
    have h : (((conjOnNormalized X hRX r ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ : ↥X) : G)
        = (x⁻¹ * ((r : G) * x * (r : G)⁻¹))⁻¹ := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, conjOnNormalized_apply_coe]
      group
    rw [h]
    exact Y.inv_mem (hfix r r.2)
  rw [fixedPoints_sectionConj_eq_bot hp hR hCH hXH hRX hRY, mem_bot,
    QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
  exact hmem

theorem normal_of_mul_eq_univ_of_le_normalizer
    (hprod : (H : Set G) * (R : Set G) = Set.univ)
    (hHN : H ≤ normalizer (N : Set G)) (hRN : R ≤ normalizer (N : Set G)) : N.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  obtain ⟨h, hh, r, hr, rfl⟩ : g ∈ (H : Set G) * (R : Set G) := by rw [hprod]; trivial
  exact mul_mem (hHN hh) (hRN hr)

theorem map_mk'_mul_map_mk'_eq_univ (N : Subgroup G) [N.Normal]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) :
    ((H.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
        * ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨h, hh, r, hr, rfl⟩ : g ∈ (H : Set G) * (R : Set G) := by rw [hprod]; trivial
    exact ⟨mk h, ⟨h, hh, rfl⟩, mk r, ⟨r, hr, rfl⟩, rfl⟩

theorem map_mk'_inf_map_mk'_eq_bot [N.Normal] (hNH : N ≤ H) (hinf : H ⊓ R = ⊥) :
    (H.map (mk' N) : Subgroup (G ⧸ N)) ⊓ R.map (mk' N) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨h, hh, rfl⟩, ⟨r, hr, hrx⟩⟩
  rw [mk'_apply, mk'_apply, QuotientGroup.eq] at hrx
  have hrH : r ∈ H := by
    have h1 : r⁻¹ ∈ H := by
      have : r⁻¹ * h * h⁻¹ ∈ H := H.mul_mem (hNH hrx) (H.inv_mem hh)
      simpa using this
    simpa using H.inv_mem h1
  have hr1 : r = 1 := by
    have : r ∈ H ⊓ R := ⟨hrH, hr⟩
    rwa [hinf, mem_bot] at this
  rw [hr1, inv_one, one_mul] at hrx
  rw [mem_bot, mk'_apply, QuotientGroup.eq_one_iff]
  exact hrx

theorem natCard_map_mk' [N.Normal] (hNR : Disjoint N R) :
    Nat.card (R.map (mk' N) : Subgroup (G ⧸ N)) = Nat.card R := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex,
    Subgroup.subgroupOf_eq_bot.2 hNR, Subgroup.index_bot]

theorem forall_inv_mul_conj_mem_of_commute [N.Normal] (hp : p.Prime) (hR : Nat.card R = p)
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) {h : G}
    (hcomm : Commute (mk h : G ⧸ N) (mk r : G ⧸ N)) :
    ∀ s ∈ R, h⁻¹ * (s * h * s⁻¹) ∈ N := by
  intro s hs
  obtain ⟨k, hk⟩ : s ∈ zpowers r := by
    rw [zpowers_eq_of_natCard_eq_prime hp hR hr hr1]; exact hs
  have hcs : Commute (mk h : G ⧸ N) (mk s : G ⧸ N) := by
    rw [← hk]
    simpa using hcomm.zpow_right k
  rw [← QuotientGroup.eq_one_iff]
  have hx : (mk (h⁻¹ * (s * h * s⁻¹)) : G ⧸ N)
      = (mk h : G ⧸ N)⁻¹ * ((mk s : G ⧸ N) * (mk h : G ⧸ N) * (mk s : G ⧸ N)⁻¹) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hx, ← hcs.eq]
  group

theorem map_mk'_inf_centralizer_singleton_eq_bot [Finite H] [H.Normal] [Group.IsSolvable ↥H]
    [N.Normal] (hp : p.Prime) (hR : Nat.card R = p)
    (hCH : H ⊓ centralizer (R : Set G) = ⊥) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    (H.map (mk' N) : Subgroup (G ⧸ N)) ⊓ centralizer ({(mk r : G ⧸ N)}) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, rfl⟩ := hx1
  rw [mem_centralizer_iff] at hx2
  have hcomm : Commute (mk h : G ⧸ N) (mk r : G ⧸ N) := (hx2 _ rfl).symm
  have hmemN : h ∈ N :=
    mem_of_forall_inv_mul_conj_mem (H := H) (X := H) (Y := N) hp hR hCH le_rfl
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal hh
      (forall_inv_mul_conj_mem_of_commute (N := N) hp hR hr hr1 hcomm)
  rw [mem_bot, mk'_apply, QuotientGroup.eq_one_iff]
  exact hmemN

theorem isFixedFreePrimeComplementSetup_quotient [Finite H] [H.Normal] [Group.IsSolvable ↥H]
    (hprod : (H : Set G) * (R : Set G) = Set.univ) (hinf : H ⊓ R = ⊥)
    (hp : p.Prime) (hR : Nat.card R = p) (hCH : H ⊓ centralizer (R : Set G) = ⊥)
    (hNH : N ≤ H) (hHN : H ≤ normalizer (N : Set G)) (hRN : R ≤ normalizer (N : Set G))
    (_hlt : N < H) :
    ∃ _ : N.Normal,
      (H.map (mk' N) : Subgroup (G ⧸ N)).Normal ∧
      ((H.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
          * ((R.map (mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) = Set.univ ∧
      (H.map (mk' N) : Subgroup (G ⧸ N)) ⊓ R.map (mk' N) = ⊥ ∧
      Nat.card (R.map (mk' N) : Subgroup (G ⧸ N)) = p ∧
      ∀ r ∈ R, r ≠ 1 →
        (H.map (mk' N) : Subgroup (G ⧸ N)) ⊓ centralizer ({(mk r : G ⧸ N)}) = ⊥ := by
  have hNnormal : N.Normal := normal_of_mul_eq_univ_of_le_normalizer hprod hHN hRN
  have hdisj : Disjoint N R :=
    disjoint_iff.2 (le_antisymm ((inf_le_inf_right R hNH).trans hinf.le) bot_le)
  exact ⟨hNnormal, QuotientGroup.map_normal N H,
    map_mk'_mul_map_mk'_eq_univ N hprod,
    map_mk'_inf_map_mk'_eq_bot hNH hinf,
    (natCard_map_mk' hdisj).trans hR,
    fun _ hr hr1 => map_mk'_inf_centralizer_singleton_eq_bot hp hR hCH hr hr1⟩

end CFSG.FeitThompson
