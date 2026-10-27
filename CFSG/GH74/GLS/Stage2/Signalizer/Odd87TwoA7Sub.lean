module

public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem open_isSubnormal_of_subnormal {X : Type*} [Group X] {A B : Subgroup X} (hAB : A ≤ B)
    (h : (A.subgroupOf B).IsSubnormal) : CFSG.Open.IsSubnormal A B :=
  (CFSG.Open.IsSubnormal.iff_subgroupOf hAB).2 h

theorem open_isSubnormal_trans {X : Type*} [Group X] {A B C : Subgroup X}
    (h₁ : CFSG.Open.IsSubnormal A B) (h₂ : CFSG.Open.IsSubnormal B C) :
    CFSG.Open.IsSubnormal A C :=
  h₁.trans h₂

theorem isSubnormal_subgroupOf_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {I C : Subgroup G} (hIC : I ≤ C) (h : (I.subgroupOf C).IsSubnormal) :
    ((I.map f).subgroupOf (C.map f)).IsSubnormal := by
  have h1 := h.map (f.subgroupMap_surjective C)
  have h2 : (I.subgroupOf C).map (f.subgroupMap C) = (I.map f).subgroupOf (C.map f) := by
    ext ⟨n, hn⟩
    constructor
    · rintro ⟨⟨g, hgC⟩, hg, hgn⟩
      exact ⟨g, hg, congrArg Subtype.val hgn⟩
    · rintro ⟨g, hgI, rfl⟩
      exact ⟨⟨g, hIC hgI⟩, hgI, Subtype.ext rfl⟩
  rwa [h2] at h1

theorem map_centralizer_center_le {G : Type*} [Group G] (s' : G) :
    (Subgroup.centralizer {s'}).map (QuotientGroup.mk' (Subgroup.center G)) ≤
      Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center G) s'} := by
  have h := Subgroup.map_centralizer_le_centralizer_image {s'}
    (QuotientGroup.mk' (Subgroup.center G))
  rwa [Set.image_singleton] at h

theorem normal_subgroupOf_map_centralizer_center {G : Type*} [Group G] (s' : G) :
    (((Subgroup.centralizer {s'}).map (QuotientGroup.mk' (Subgroup.center G))).subgroupOf
      (Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center G) s'})).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (map_centralizer_center_le s')]
  intro n y hn hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hn
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
  have hg' : g * s' = s' * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hxs : ((x * s' : G) : G ⧸ Subgroup.center G) = ((s' * x : G) : G ⧸ Subgroup.center G) := by
    simpa using Subgroup.mem_centralizer_singleton_iff.mp hy
  obtain ⟨c, hcen, hc⟩ : ∃ c ∈ Subgroup.center G, x⁻¹ * s' * x = s' * c :=
    ⟨(x * s')⁻¹ * (s' * x), QuotientGroup.eq.mp hxs, by group⟩
  have hgc : g * c = c * g := Subgroup.mem_center_iff.mp hcen g
  refine Subgroup.mem_map.mpr ⟨x * g * x⁻¹, ?_, by simp⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * g * x⁻¹ * s' = x * (g * (x⁻¹ * s' * x)) * x⁻¹ := by group
    _ = x * (g * (s' * c)) * x⁻¹ := by rw [hc]
    _ = x * ((g * s') * c) * x⁻¹ := by group
    _ = x * ((s' * g) * c) * x⁻¹ := by rw [hg']
    _ = x * (s' * (g * c)) * x⁻¹ := by group
    _ = x * (s' * (c * g)) * x⁻¹ := by rw [hgc]
    _ = x * ((s' * c) * g) * x⁻¹ := by group
    _ = x * ((x⁻¹ * s' * x) * g) * x⁻¹ := by rw [hc]
    _ = s' * (x * g * x⁻¹) := by group

theorem open_isSubnormal_image_centralizer {G : Type} [Group G] (I' : Subgroup G) (s' : G)
    (hI' : I' ≤ Subgroup.centralizer {s'})
    (hsub : (I'.subgroupOf (Subgroup.centralizer {s'})).IsSubnormal) :
    CFSG.Open.IsSubnormal (I'.map (QuotientGroup.mk' (Subgroup.center G)))
      (Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center G) s'}) :=
  open_isSubnormal_trans
    (open_isSubnormal_of_subnormal (Subgroup.map_mono hI')
      (isSubnormal_subgroupOf_map _ hI' hsub))
    (CFSG.Open.IsSubnormal.step (map_centralizer_center_le s')
      (normal_subgroupOf_map_centralizer_center s') (CFSG.Open.IsSubnormal.refl _))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
