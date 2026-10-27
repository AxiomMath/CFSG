module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutI

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

abbrev fixOf {G : Type*} [Group G] (θ : MulAut G) : Subgroup G :=
  MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id G)

theorem mem_fixOf {G : Type*} [Group G] {θ : MulAut G} {x : G} : x ∈ fixOf θ ↔ θ x = x :=
  Iff.rfl

theorem fixOf_conj {G : Type*} [Group G] (u : G) :
    fixOf (MulAut.conj u) = centralizer ({u} : Set G) := by
  ext x
  rw [mem_fixOf, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * u = u * x * u⁻¹ * u := by rw [h]
      _ = u * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

variable {K : Type} [Field K]

theorem perfect_le_map_fixOf (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    {N : Subgroup (StatedProj (StatedSp 2 K))} (hN : ∀ x ∈ N, α x = x) (hperf : ⁅N, N⁆ = N) :
    N ≤ (fixOf θ).map (proj 2 K) := by
  have hfix : ∀ x ∈ N, ∃ g, proj 2 K g = x ∧ θ g * g⁻¹ ∈ spScalars 2 K := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective x
    refine ⟨g, rfl, ?_⟩
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα, hN _ hx, mul_inv_cancel]
  rw [← hperf, commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl, hg⟩ := hfix x hx
  obtain ⟨h, rfl, hh⟩ := hfix y hy
  refine ⟨⁅g, h⁆, ?_, map_commutatorElement _ _ _⟩
  exact fix_commutator (fun z hz => mem_center_of_mem_spScalars hz) θ.toMonoidHom hg hh

theorem map_fixOf_le (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g)) :
    (fixOf θ).map (proj 2 K) ≤ fixOf α := by
  rintro _ ⟨g, hg, rfl⟩
  change α (proj 2 K g) = proj 2 K g
  rw [hθα]
  exact congrArg (proj 2 K) hg

abbrev fixProj (θ : MulAut (StatedSp 2 K)) : fixOf θ →* (fixOf θ).map (proj 2 K) :=
  (proj 2 K).subgroupMap (fixOf θ)

theorem ker_fixProj (θ : MulAut (StatedSp 2 K)) :
    (fixProj θ).ker = (spScalars 2 K).subgroupOf (fixOf θ) := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_proj, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ker_fixProj_le_center (θ : MulAut (StatedSp 2 K)) :
    (fixProj θ).ker ≤ center (fixOf θ) := by
  intro g hg
  rw [ker_fixProj, mem_subgroupOf] at hg
  rw [mem_center_iff]
  intro h
  exact Subtype.ext (mem_center_iff.mp (mem_center_of_mem_spScalars hg) h)

theorem card_map_fixOf_mul_two [Finite K] (h2 : (2 : K) ≠ 0) (θ : MulAut (StatedSp 2 K))
    (hZ : ∀ z ∈ spScalars 2 K, θ z = z) :
    Nat.card ((fixOf θ).map (proj 2 K)) * 2 = Nat.card (fixOf θ) := by
  have hle : spScalars 2 K ≤ fixOf θ := fun z hz => hZ z hz
  have hker : Nat.card (fixProj θ).ker = 2 := by
    rw [ker_fixProj, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_spScalars h2]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (fixProj θ).ker, hker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (fixProj θ)
      ((proj 2 K).subgroupMap_surjective (fixOf θ))).toEquiv]

theorem eq_map_fixOf_of_isPComponent [Finite K] (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    (hQ : CFSG.IsQuasisimple (fixOf θ))
    {J : Subgroup (StatedProj (StatedSp 2 K))} (hJX : J ≤ fixOf α)
    (hJ : CFSG.IsPComponent 2 (J.subgroupOf (fixOf α))) : J = (fixOf θ).map (proj 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := commutator_eq_of_isPComponent hJX hJ
  have hJN : J ≤ (fixOf θ).map (proj 2 K) :=
    perfect_le_map_fixOf θ hθα (fun x hx => hJX hx) hperf
  have hJN' : CFSG.IsPComponent 2 (J.subgroupOf ((fixOf θ).map (proj 2 K))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJN (map_fixOf_le θ hθα) hJ
  obtain ⟨L, hL, hLM, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2 (fixProj θ)
    ((proj 2 K).subgroupMap_surjective (fixOf θ)) (ker_fixProj_le_center θ) _ hJN'
  have hLtop := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hQ 2 L hL
  rw [hLtop, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr ((proj 2 K).subgroupMap_surjective (fixOf θ))] at hLM
  refine le_antisymm hJN fun x hx => ?_
  have : (⟨x, hx⟩ : (fixOf θ).map (proj 2 K)) ∈ J.subgroupOf ((fixOf θ).map (proj 2 K)) :=
    hLM ▸ Subgroup.mem_top _
  exact this

end CFSG.ComponentClassification.CatFactsSp4
