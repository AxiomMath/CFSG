module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

instance normal_subgroupOf_normalizer (T : Subgroup G) :
    (T.subgroupOf (Subgroup.normalizer (T : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl

abbrev NQuot (T : Subgroup G) : Type :=
  ↥(Subgroup.normalizer (T : Set G)) ⧸ T.subgroupOf (Subgroup.normalizer (T : Set G))

@[expose] def barElt (T : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    NQuot T :=
  QuotientGroup.mk (⟨x, hx⟩ : ↥(Subgroup.normalizer (T : Set G)))

@[expose] def barSub (T U : Subgroup G) : Subgroup (NQuot T) :=
  (U.subgroupOf (Subgroup.normalizer (T : Set G))).map
    (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G))))

section Basic

variable {T U : Subgroup G}

theorem barElt_mul {x y : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ Subgroup.normalizer (T : Set G)) :
    barElt T hx * barElt T hy = barElt T ((Subgroup.normalizer (T : Set G)).mul_mem hx hy) :=
  rfl

theorem barElt_inv {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    (barElt T hx)⁻¹ = barElt T ((Subgroup.normalizer (T : Set G)).inv_mem hx) :=
  rfl

theorem barElt_one : barElt T ((Subgroup.normalizer (T : Set G)).one_mem) = 1 := rfl

theorem barElt_eq_iff {x y : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ Subgroup.normalizer (T : Set G)) : barElt T hx = barElt T hy ↔ x⁻¹ * y ∈ T := by
  unfold barElt
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf

theorem barElt_eq_one_iff {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    barElt T hx = 1 ↔ x ∈ T := by
  unfold barElt
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem barElt_mem_barSub_iff {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G)) :
    barElt T hx ∈ barSub T U ↔
      ∃ u : G, u ∈ Subgroup.normalizer (T : Set G) ∧ u ∈ U ∧ u⁻¹ * x ∈ T := by
  unfold barSub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨(u : G), u.2, Subgroup.mem_subgroupOf.1 hu, ?_⟩
    have h : (u : G)⁻¹ * x ∈ T := by
      have := QuotientGroup.eq.1 hux
      exact Subgroup.mem_subgroupOf.1 this
    exact h
  · rintro ⟨u, huN, huU, hux⟩
    refine ⟨⟨u, huN⟩, Subgroup.mem_subgroupOf.2 huU, ?_⟩
    exact (barElt_eq_iff huN hx).2 hux

theorem barElt_mem_barSub {u : G} (hu : u ∈ Subgroup.normalizer (T : Set G)) (huU : u ∈ U) :
    barElt T hu ∈ barSub T U :=
  (barElt_mem_barSub_iff hu).2 ⟨u, hu, huU, by simp⟩

theorem exists_eq_barElt_of_mem_barSub {y : NQuot T} (hy : y ∈ barSub T U) :
    ∃ (u : G) (hu : u ∈ Subgroup.normalizer (T : Set G)), u ∈ U ∧ barElt T hu = y := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
  exact ⟨u, u.2, Subgroup.mem_subgroupOf.1 hu, rfl⟩

theorem conjSubgroup_barSub {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    conjSubgroup (barElt T hn) (barSub T U) = barSub T (conjSubgroup n U) :=
  (map_subgroupOf_conjSubgroup_of_mem (Subgroup.normalizer (T : Set G)) T U hn).symm

theorem barSub_normal (hU : ∀ n ∈ Subgroup.normalizer (T : Set G), conjSubgroup n U = U) :
    (barSub T U).Normal := by
  refine ⟨fun y hy z => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have h := conj_mem_conjSubgroup (QuotientGroup.mk x : NQuot T) hy
  have e : (QuotientGroup.mk x : NQuot T) = barElt T x.2 := rfl
  rw [e, conjSubgroup_barSub, hU _ x.2] at h
  exact h

theorem isPGroup_barSub (hU : IsPGroup 2 U) : IsPGroup 2 (barSub T U) :=
  (hU.comap_subtype (K := Subgroup.normalizer (T : Set G))).map _

theorem isElemAbelian_subgroupOf {K : Subgroup G} (hU : IsElemAbelian 2 U) :
    IsElemAbelian 2 (U.subgroupOf K) := CFSG.Open.IsElemAbelian.subgroupOf hU K

theorem isElemAbelian_barSub (hU : IsElemAbelian 2 U) : IsElemAbelian 2 (barSub T U) :=
  isElemAbelian_map_of_hom (isElemAbelian_subgroupOf hU) _

theorem card_barSub (hUN : U ≤ Subgroup.normalizer (T : Set G)) (hUT : U ⊓ T = ⊥) :
    Nat.card (barSub T U) = Nat.card U := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun u : U => (⟨barElt T (hUN u.2), barElt_mem_barSub (hUN u.2) u.2⟩ : barSub T U))
    ⟨?_, ?_⟩)).symm
  · intro u u' h
    have h1 := (barElt_eq_iff (hUN u.2) (hUN u'.2)).1 (congrArg Subtype.val h)
    have h3 : (u : G)⁻¹ * u' ∈ U ⊓ T := ⟨U.mul_mem (U.inv_mem u.2) u'.2, h1⟩
    rw [hUT, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  · rintro ⟨y, hy⟩
    obtain ⟨u, hu, huU, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
    exact ⟨⟨u, huU⟩, rfl⟩

theorem conjSubgroup_le_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (hU : U ≤ Subgroup.normalizer (T : Set G)) :
    conjSubgroup g U ≤ Subgroup.normalizer (T : Set G) := by
  rintro _ ⟨u, hu, rfl⟩
  have := (Subgroup.normalizer (T : Set G)).mul_mem
    ((Subgroup.normalizer (T : Set G)).mul_mem hg (hU hu))
    ((Subgroup.normalizer (T : Set G)).inv_mem hg)
  simpa [MulAut.conj_apply] using this

theorem barElt_commutator {x y : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ Subgroup.normalizer (T : Set G))
    (hxy : ⁅x, y⁆ ∈ Subgroup.normalizer (T : Set G)) :
    barElt T hxy = ⁅barElt T hx, barElt T hy⁆ := rfl

theorem commutator_mem_of_bar_comm {x y : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hy : y ∈ Subgroup.normalizer (T : Set G))
    (h : barElt T hx * barElt T hy = barElt T hy * barElt T hx) : ⁅x, y⁆ ∈ T := by
  have hxy : ⁅x, y⁆ ∈ Subgroup.normalizer (T : Set G) := by
    have := (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem
        ((Subgroup.normalizer (T : Set G)).mul_mem hx hy)
        ((Subgroup.normalizer (T : Set G)).inv_mem hx))
      ((Subgroup.normalizer (T : Set G)).inv_mem hy)
    simpa [commutatorElement_def] using this
  refine (barElt_eq_one_iff hxy).1 ?_
  rw [barElt_commutator hx hy hxy]
  exact commutatorElement_eq_one_iff_mul_comm.2 h

theorem barSub_le_of_le_sup {U' : Subgroup G} (hU' : U' ≤ Subgroup.normalizer (T : Set G))
    (h : ∀ u ∈ U, u ∈ Subgroup.normalizer (T : Set G) → u ∈ U' ⊔ T) :
    barSub T U ≤ barSub T U' := by
  intro y hy
  obtain ⟨u, hu, huU, rfl⟩ := exists_eq_barElt_of_mem_barSub hy
  have hmem := h u huU hu
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right U' T hU'
  have hmem' : u ∈ ((U' : Set G) * (T : Set G)) := by
    rw [← hmul]
    exact hmem
  obtain ⟨u', hu', t, ht, rfl⟩ := hmem'
  refine (barElt_mem_barSub_iff hu).2 ⟨u', hU' hu', hu', ?_⟩
  simpa using ht

end Basic

section Sylow

variable {Γ : Type*} [Group Γ]

theorem le_sylow_of_normal_pGroup {Q : Subgroup Γ} (hQn : Q.Normal) (hQ : IsPGroup 2 Q)
    (P : Sylow 2 Γ) : Q ≤ (P : Subgroup Γ) := by
  have hsup : IsPGroup 2 ↥(Q ⊔ (P : Subgroup Γ)) := by
    refine hQ.to_sup_of_normal_left' P.isPGroup' ?_
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hQn.conj_mem h hh g, fun hh => by
      have := hQn.conj_mem _ hh g⁻¹
      simpa [mul_assoc] using this⟩
  have := P.is_maximal' hsup le_sup_right
  rw [← this]
  exact le_sup_left

end Sylow

end CFSG.CGT.Timmesfeld75
