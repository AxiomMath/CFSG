module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.RankThree.PartOne.S11d.LieComponentLift

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.PerfectAutomorphisms

namespace H2

theorem conj_eq_self_iff {N : Type} [Group N] {J : Subgroup N} {v : N}
    (hvn : v ∈ normalizer (J : Set N)) (c : ↥J) :
    J.normalizerMonoidHom ⟨v, hvn⟩ c = c ↔ v * (c : N) = (c : N) * v := by
  rw [Subtype.ext_iff]
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact mul_inv_eq_iff_eq_mul

@[expose] noncomputable def quotRestr {N : Type} [Group N] (J : Subgroup N) (v : N) :
    ↥(J ⊓ centralizer ({v} : Set N)) →* ↥J ⧸ Subgroup.center ↥J :=
  (QuotientGroup.mk' (Subgroup.center ↥J)).comp (Subgroup.inclusion inf_le_left)

theorem quotRestr_apply {N : Type} [Group N] (J : Subgroup N) (v : N)
    (x : ↥(J ⊓ centralizer ({v} : Set N))) :
    quotRestr J v x = QuotientGroup.mk' (Subgroup.center ↥J) ⟨(x : N), x.2.1⟩ := rfl

theorem quotRestr_ker_le_center {N : Type} [Group N] (J : Subgroup N) (v : N) :
    (quotRestr J v).ker ≤ Subgroup.center ↥(J ⊓ centralizer ({v} : Set N)) := by
  intro x hx
  rw [MonoidHom.mem_ker, quotRestr_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    at hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨(y : N), y.2.1⟩)
  apply Subtype.ext
  exact h

theorem mem_range_of_mem_fixSub {N : Type} [Group N] {J : Subgroup N} {v : N}
    (hvn : v ∈ normalizer (J : Set N)) {c : ↥J}
    (hc : c ∈ fixSub (J.normalizerMonoidHom ⟨v, hvn⟩)) :
    QuotientGroup.mk' (Subgroup.center ↥J) c ∈ (quotRestr J v).range := by
  have h1 : J.normalizerMonoidHom ⟨v, hvn⟩ c = c := hc
  have h2 := (conj_eq_self_iff hvn c).mp h1
  refine ⟨⟨(c : N), c.2, ?_⟩, rfl⟩
  show (c : N) ∈ centralizer ({v} : Set N)
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact h2

theorem range_le_fixSub {N : Type} [Group N] {J : Subgroup N} {v : N}
    (hvn : v ∈ normalizer (J : Set N)) :
    (quotRestr J v).range ≤ fixSub (actCenterQuot J ⟨v, hvn⟩) := by
  rintro _ ⟨x, rfl⟩
  have hx : v * (x : N) = (x : N) * v := by
    have : (x : N) ∈ centralizer ({v} : Set N) := x.2.2
    rw [mem_centralizer_iff] at this
    exact this v rfl
  rw [mem_fixSub, quotRestr_apply]
  change onCenterQuotient (J.normalizerMonoidHom ⟨v, hvn⟩)
    (QuotientGroup.mk' (Subgroup.center ↥J) _) = _
  rw [onCenterQuotient_apply_mk]
  congr 1
  exact (conj_eq_self_iff hvn ⟨(x : N), x.2.1⟩).mpr hx

theorem commutator_le_range {N : Type} [Group N] {J : Subgroup N} {v : N}
    (hvn : v ∈ normalizer (J : Set N)) :
    ⁅fixSub (actCenterQuot J ⟨v, hvn⟩), fixSub (actCenterQuot J ⟨v, hvn⟩)⁆ ≤
      (quotRestr J v).range := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := commutator_fixSub_le_map (J.normalizerMonoidHom ⟨v, hvn⟩) hy
  exact mem_range_of_mem_fixSub hvn hc

theorem layer_ne_bot_of_central_lift {𝒢 Y : Type*} [Group 𝒢] [Group Y] (π₀ : 𝒢 →* Y)
    (hker : π₀.ker ≤ Subgroup.center 𝒢) {F : Subgroup Y} (hF : π₀.range ≤ F)
    (hD : ∀ D : Subgroup ↥F, IsComponent D → D.map F.subtype ≤ π₀.range)
    (h : layer ↥F ≠ ⊥) : layer 𝒢 ≠ ⊥ := by
  obtain ⟨D, hDc⟩ : ∃ D : Subgroup ↥F, IsComponent D := by
    by_contra hne
    apply h
    have : {K : Subgroup ↥F | IsComponent K} = ∅ :=
      Set.eq_empty_of_forall_notMem fun K hK => hne ⟨K, hK⟩
    rw [layer, this, sSup_empty]
  set B : Subgroup Y := π₀.range with hB
  set D' : Subgroup Y := D.map F.subtype with hD'
  have hD'B : D' ≤ B := hD D hDc
  have hq' : IsQuasisimple ↥D' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.equivMapOfInjective F.subtype F.subtype_injective) hDc.1
  have hq₁ : IsQuasisimple ↥(D'.subgroupOf B) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD'B).symm hq'
  have hsubF : (D'.subgroupOf F).IsSubnormal := by
    have : D'.subgroupOf F = D := Subgroup.comap_map_eq_self_of_injective F.subtype_injective D
    rw [this]
    exact hDc.2
  have hsub₁ : (D'.subgroupOf B).IsSubnormal :=
    CFSG.RankThree.PartOne.isSubnormal_subgroupOf_of_le' hF hsubF
  let π : 𝒢 →* ↥B := π₀.rangeRestrict
  have hπ : Function.Surjective π := π₀.rangeRestrict_surjective
  have hπker : π.ker ≤ Subgroup.center 𝒢 := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hc1 : Subgroup.centralizer ({π 1} : Set ↥B) = ⊤ := by
    rw [map_one]
    exact Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
  have hc1' : Subgroup.centralizer ({1} : Set 𝒢) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
  obtain ⟨hqL, hLc, hLsub, -⟩ := CFSG.RankThree.PartOne.exists_lift_component hπ hπker (A := 1)
    hq₁ (by rw [hc1]; exact le_top) (by rw [hc1]; exact hsub₁.subgroupOf)
  have hLcomp : IsComponent (CFSG.RankThree.PartOne.derivedPreimage π (D'.subgroupOf B)) :=
    ⟨hqL, Subgroup.IsSubnormal.trans hLc hLsub (by rw [hc1']; exact Subgroup.IsSubnormal.top)⟩
  intro hbot
  have hle := CFSG.LocalCores.component_le_layer hLcomp
  rw [hbot, le_bot_iff] at hle
  exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hqL) hle

end H2

theorem layer_fixSub_actCenterQuot {N : Type} [Group N] [Finite N] {J : Subgroup N}
    (hJ : IsComponent J) {v : N} (hvn : v ∈ normalizer (J : Set N))
    (h : layer ↥(J ⊓ centralizer ({v} : Set N)) = ⊥) :
    layer ↥(fixSub (actCenterQuot J ⟨v, hvn⟩)) = ⊥ := by
  have _ := hJ
  by_contra hne
  refine H2.layer_ne_bot_of_central_lift (H2.quotRestr J v) (H2.quotRestr_ker_le_center J v)
    (H2.range_le_fixSub hvn) (fun D hD => ?_) hne h
  have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hD.1.1
  calc D.map (fixSub (actCenterQuot J ⟨v, hvn⟩)).subtype
      = (⁅D, D⁆).map (fixSub (actCenterQuot J ⟨v, hvn⟩)).subtype := by rw [hperf]
    _ = ⁅D.map (fixSub (actCenterQuot J ⟨v, hvn⟩)).subtype,
          D.map (fixSub (actCenterQuot J ⟨v, hvn⟩)).subtype⁆ := Subgroup.map_commutator _ _ _
    _ ≤ ⁅fixSub (actCenterQuot J ⟨v, hvn⟩), fixSub (actCenterQuot J ⟨v, hvn⟩)⁆ :=
        Subgroup.commutator_mono (Subgroup.map_subtype_le D) (Subgroup.map_subtype_le D)
    _ ≤ (H2.quotRestr J v).range := H2.commutator_le_range hvn

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
