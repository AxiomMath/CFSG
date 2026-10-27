module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg

open Subgroup CFSG.ComponentClassification.PerfectAutomorphisms CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] noncomputable def yAct (J : Subgroup G) :
    ↥(normalizer (J : Set G)) →* MulAut (↥J ⧸ center ↥J) :=
  (centerQuotientHom ↥J).comp J.normalizerMonoidHom

theorem yAct_apply_mk (J : Subgroup G) (n : ↥(normalizer (J : Set G))) (x : ↥J) :
    yAct J n (QuotientGroup.mk x) =
      QuotientGroup.mk
        (⟨(n : G) * x * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 _).mp x.2⟩ : ↥J) :=
  onCenterQuotient_apply_mk _ x

@[expose] def innHom (Q : Type*) [Group Q] : Q →* MulAut (Q ⧸ center Q) :=
  (MulAut.conj : (Q ⧸ center Q) →* MulAut (Q ⧸ center Q)).comp (QuotientGroup.mk' (center Q))

theorem innHom_apply {Q : Type*} [Group Q] (x : Q) :
    innHom Q x = MulAut.conj (QuotientGroup.mk x : Q ⧸ center Q) := rfl

theorem yAct_of_mem (J : Subgroup G) (x : ↥J) :
    yAct J ⟨(x : G), le_normalizer x.2⟩ = innHom ↥J x := by
  ext v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center ↥J) v
  rw [innHom, MonoidHom.comp_apply, MulAut.conj_apply]
  exact yAct_apply_mk J _ y

theorem yAct_eq_one_iff (J : Subgroup G) [Group.IsPerfect ↥J] (n : ↥(normalizer (J : Set G))) :
    yAct J n = 1 ↔ (n : G) ∈ centralizer (J : Set G) := by
  change centerQuotientHom ↥J (J.normalizerMonoidHom n) = 1 ↔ _
  rw [← map_one (centerQuotientHom ↥J), (centerQuotientHom_injective ↥J).eq_iff]
  constructor
  · intro h1
    have h2 : n ∈ J.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker] at h2
    exact h2
  · intro hc
    have h2 : n ∈ (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := hc
    rw [← Subgroup.normalizerMonoidHom_ker] at h2
    exact h2

theorem isSylowOf_map_innHom {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (R : Sylow p Q) :
    IsSylowOf p ((R : Subgroup Q).map (innHom Q))
      (MulAut.conj : (Q ⧸ center Q) →* MulAut (Q ⧸ center Q)).range := by
  have h1 : Function.Surjective (QuotientGroup.mk' (center Q)) := QuotientGroup.mk'_surjective _
  have h2 : Function.Surjective
      (MulAut.conj : (Q ⧸ center Q) →* MulAut (Q ⧸ center Q)).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  refine ⟨(R.mapSurjective h1).mapSurjective h2, ?_⟩
  rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_inf_isSubnormal_top {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    {P : Subgroup A} (hP : IsSylowOf p P ⊤) {H : Subgroup A} (hH : H.IsSubnormal) :
    IsSylowOf p (P ⊓ H) H := by
  induction hH with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

theorem isSylowOf_inf_of_subnormalIn {p : ℕ} [Fact p.Prime] [Finite G] {S H J : Subgroup G}
    (hS : IsSylowOf p S H) (hJH : J ≤ H) (hJ : (J.subgroupOf H).IsSubnormal) :
    IsSylowOf p (S ⊓ J) J := by
  have hS' : IsSylowOf p (S.subgroupOf H) ⊤ := by
    rw [← isSylowOf_map_subtype_iff H, subgroupOf_map_subtype, inf_of_le_left hS.le,
      ← MonoidHom.range_eq_map, range_subtype]
    exact hS
  have h2 := isSylowOf_inf_isSubnormal_top hS' hJ
  rw [← isSylowOf_map_subtype_iff H, Subgroup.map_inf_eq _ _ _ H.subtype_injective,
    subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hS.le,
    inf_of_le_left hJH] at h2
  exact h2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg
