module

public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Goldschmidt75

open Subgroup

variable {G : Type} [Group G]

@[expose] def perfRes (H : Subgroup G) : Subgroup G :=
  (CFSG.perfectResidual H).map H.subtype

theorem perfRes_le (H : Subgroup G) : perfRes H ≤ H :=
  map_subtype_le _

theorem commutator_perfRes [Finite G] (H : Subgroup G) :
    ⁅perfRes H, perfRes H⁆ = perfRes H := by
  have : Group.IsPerfect (CFSG.perfectResidual H) :=
    (CFSG.perfect_residual_characterization (G := H)).2.2.1
  have h : Group.IsPerfect ((CFSG.perfectResidual H).map H.subtype) := Group.IsPerfect.map _
  exact Subgroup.isPerfect_iff.mp h

theorem le_perfRes [Finite G] {H P : Subgroup G} (hPH : P ≤ H) (hP : ⁅P, P⁆ = P) :
    P ≤ perfRes H := by
  have hP' : Group.IsPerfect (P.subgroupOf H) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hPH, hP]
  have h := (CFSG.perfect_residual_transport (G := H) (H := H) (MonoidHom.id H)).2.2
    (P.subgroupOf H) hP'
  intro x hx
  exact ⟨⟨x, hPH hx⟩, h (mem_subgroupOf.mpr hx), rfl⟩

theorem map_perfRes [Finite G] {G' : Type} [Group G'] [Finite G'] (φ : G →* G')
    (H : Subgroup G) : (perfRes H).map φ = perfRes (H.map φ) := by
  obtain ⟨h, -, -⟩ := CFSG.perfect_residual_transport (φ.comp H.subtype)
  have hr : (φ.comp H.subtype).range = H.map φ := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [perfRes, Subgroup.map_map, h]
  revert hr
  generalize (φ.comp H.subtype).range = R
  intro hr
  subst hr
  rfl

theorem normalizer_le_normalizer_perfRes [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (perfRes H : Set G) := by
  intro g hg
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (mem_normalizer_iff.mp hg _).mpr ?_, ?_⟩
      · simpa [mul_assoc] using hx
      · simp [mul_assoc]
  have hmap := map_perfRes (MulAut.conj g).toMonoidHom H
  rw [hH] at hmap
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    rwa [← this]

theorem eq_bot_of_perfect_of_odd [Finite G] {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hodd : Odd (Nat.card P)) : P = ⊥ := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have hsol : Group.IsSolvable P := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isSolvable P hsol

theorem le_of_perfect_of_odd_index [Finite G] {L W : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hWL : (W.subgroupOf L).Normal) (hodd : Odd (W.subgroupOf L).index) : L ≤ W := by
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL
  have hsol : Group.IsSolvable (L ⧸ W.subgroupOf L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have htop : W.subgroupOf L = ⊤ := by
    by_contra hne
    have : Nontrivial (L ⧸ W.subgroupOf L) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (L ⧸ W.subgroupOf L) hsol
  intro x hx
  have : (⟨x, hx⟩ : L) ∈ W.subgroupOf L := htop ▸ mem_top _
  exact mem_subgroupOf.mp this

end CFSG.Goldschmidt75
