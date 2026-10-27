module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZ
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore derivedSeriesOf perfectCore_le perfectCore_mono
  exists_perfectCore_eq map_derivedSeriesOf)

section General

variable {G : Type*} [Group G]

theorem derivedSeriesOf_sup_le {Q M : Subgroup G} (hMN : M ≤ normalizer (Q : Set G)) (n : ℕ) :
    derivedSeriesOf (Q ⊔ M) n ≤ Q ⊔ derivedSeriesOf M n := by
  set X := Q ⊔ M with hX
  have hQX : Q ≤ X := le_sup_left
  have hMX : M ≤ X := le_sup_right
  have hnorm : (Q.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQX).2 (sup_le le_normalizer hMN)
  set f := QuotientGroup.mk' (Q.subgroupOf X) with hf
  have htop : (⊤ : Subgroup X) = Q.subgroupOf X ⊔ M.subgroupOf X := by
    rw [← subgroupOf_sup hQX hMX, subgroupOf_self]
  have hmapQ : (Q.subgroupOf X).map f = ⊥ := by
    rw [eq_bot_iff, map_le_iff_le_comap]
    intro x hx
    rw [mem_comap, mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  have hmap : (⊤ : Subgroup X).map f = (M.subgroupOf X).map f := by
    rw [htop, Subgroup.map_sup, hmapQ, bot_sup_eq]
  have hle : derivedSeriesOf (⊤ : Subgroup X) n ≤
      derivedSeriesOf (M.subgroupOf X) n ⊔ Q.subgroupOf X := by
    have h1 : (derivedSeriesOf (⊤ : Subgroup X) n).map f =
        (derivedSeriesOf (M.subgroupOf X) n).map f := by
      rw [map_derivedSeriesOf, map_derivedSeriesOf, hmap]
    have h2 := le_comap_map f (derivedSeriesOf (⊤ : Subgroup X) n)
    rw [h1, comap_map_eq, hf, QuotientGroup.ker_mk'] at h2
    exact h2
  have hX' : derivedSeriesOf X n = (derivedSeriesOf (⊤ : Subgroup X) n).map X.subtype := by
    rw [map_derivedSeriesOf, ← MonoidHom.range_eq_map, range_subtype]
  have hM' : derivedSeriesOf M n = (derivedSeriesOf (M.subgroupOf X) n).map X.subtype := by
    rw [map_derivedSeriesOf, map_subgroupOf_eq_of_le hMX]
  rw [hX', hM']
  calc (derivedSeriesOf (⊤ : Subgroup X) n).map X.subtype
      ≤ (derivedSeriesOf (M.subgroupOf X) n ⊔ Q.subgroupOf X).map X.subtype := map_mono hle
    _ = (derivedSeriesOf (M.subgroupOf X) n).map X.subtype ⊔ Q := by
        rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hQX]
    _ = Q ⊔ (derivedSeriesOf (M.subgroupOf X) n).map X.subtype := sup_comm _ _

theorem perfectCore_sup_le [Finite G] {Q M : Subgroup G} (hMN : M ≤ normalizer (Q : Set G)) :
    perfectCore (Q ⊔ M) ≤ Q ⊔ perfectCore M := by
  obtain ⟨n₁, h₁⟩ := exists_perfectCore_eq (Q ⊔ M)
  obtain ⟨n₂, h₂⟩ := exists_perfectCore_eq M
  rw [h₁ (max n₁ n₂) (le_max_left _ _), h₂ (max n₁ n₂) (le_max_right _ _)]
  exact derivedSeriesOf_sup_le hMN _

theorem perfectCore_eq_inf_sup_perfectCore [Finite G] {X Q M : Subgroup G} (hX : Q ⊔ M = X)
    (hMN : M ≤ normalizer (Q : Set G)) :
    perfectCore X = (perfectCore X ⊓ Q) ⊔ perfectCore M := by
  have hMX : perfectCore M ≤ perfectCore X := perfectCore_mono (le_sup_right.trans hX.le)
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hMX)
  have hx' : x ∈ ((Q ⊔ perfectCore M : Subgroup G) : Set G) :=
    (hX ▸ perfectCore_sup_le hMN) hx
  rw [coe_mul_of_right_le_normalizer_left Q (perfectCore M) ((perfectCore_le M).trans hMN)] at hx'
  obtain ⟨q, hq, m, hm, rfl⟩ := hx'
  have hqX : q ∈ perfectCore X := by
    have := mul_mem hx (inv_mem (hMX hm))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨hqX, hq⟩)) (mem_sup_right hm)

end General

variable {K : Type} [Field K]


theorem perfectCore_centralizer_zD [Finite K] [CharP K 2] :
    perfectCore (centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))) =
        (perfectCore (centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))) ⊓ zDRadical K) ⊔
          perfectCore (zDLevi K) ∧
      IsPGroup 2 (perfectCore (centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))) ⊓
        zDRadical K : Subgroup (adjointGroup .E6 K)) ∧
      perfectCore (zDLevi K) ≤ normalizer ((perfectCore (centralizer ({e6Rep K 2} :
        Set (adjointGroup .E6 K))) ⊓ zDRadical K : Subgroup (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K)) ∧
      Disjoint (perfectCore (centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))) ⊓
        zDRadical K : Subgroup (adjointGroup .E6 K)) (perfectCore (zDLevi K)) := by
  obtain ⟨hQp, hQM, hinf, hMN⟩ := isTwoRadicalDecomp_zD (K := K)
  set X := centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))
  refine ⟨perfectCore_eq_inf_sup_perfectCore hQM hMN, hQp.to_le inf_le_right, ?_, ?_⟩
  · have hMX : perfectCore (zDLevi K) ≤ perfectCore X :=
      perfectCore_mono (le_sup_right.trans hQM.le)
    exact le_trans (le_inf (hMX.trans le_normalizer) ((perfectCore_le _).trans hMN))
      inf_normalizer_le_normalizer_inf
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hxQ⟩, hxM⟩ := mem_inf.1 hx
    have : x ∈ zDRadical K ⊓ zDLevi K := mem_inf.2 ⟨hxQ, perfectCore_le _ hxM⟩
    rwa [hinf] at this

end CFSG.SeitzReduction.E6Pilot
