module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10C

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.GSThmB

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem isSubnormal_inf_subgroupOf {X C T : Subgroup H}
    (hX : (X.subgroupOf C).IsSubnormal) : ((X ⊓ T).subgroupOf (T ⊓ C)).IsSubnormal := by
  have h1 := hX.comap (Subgroup.inclusion (inf_le_right : T ⊓ C ≤ C))
  have h2 : (X.subgroupOf C).comap (Subgroup.inclusion (inf_le_right : T ⊓ C ≤ C)) =
      (X ⊓ T).subgroupOf (T ⊓ C) := by
    ext ⟨y, hy⟩
    simp only [mem_comap, mem_subgroupOf, Subgroup.coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨h, (mem_inf.mp hy).1⟩, fun h => h.1⟩
  rwa [h2] at h1

omit [Finite H] in
theorem le_layerIn_of_pComponent {Y J : Subgroup H} (hJY : J ≤ Y)
    (hJ : IsPComponent 2 (J.subgroupOf Y)) : J ≤ layerIn Y := by
  have h1 : J.subgroupOf Y ≤ pLayer Y 2 := le_sSup hJ
  have h2 := map_mono (f := Y.subtype) h1
  rwa [map_subgroupOf_eq_of_le hJY] at h2

theorem le_layerIn_of_pComponent_inf {s t : H} (hst : s * t = t * s)
    (hs : ∃ n : ℕ, s ^ 2 ^ n = 1) (hsch : LBalance.SchreierSections ↥(centralizer ({t} : Set H)))
    {X J : Subgroup H} (hXs : X ≤ centralizer ({s} : Set H))
    (hX : IsPComponent 2 (X.subgroupOf (centralizer ({s} : Set H))))
    (hJ : J ≤ X ⊓ centralizer ({t} : Set H))
    (hJp : IsPComponent 2 (J.subgroupOf (X ⊓ centralizer ({t} : Set H)))) :
    IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set H) ⊓ centralizer ({s} : Set H))) ∧
      J ≤ layerIn (centralizer ({t} : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCA : X ⊓ centralizer ({t} : Set H) ≤
      centralizer ({t} : Set H) ⊓ centralizer ({s} : Set H) :=
    le_inf inf_le_right (inf_le_left.trans hXs)
  have hsub : ((X ⊓ centralizer ({t} : Set H)).subgroupOf
      (centralizer ({t} : Set H) ⊓ centralizer ({s} : Set H))).IsSubnormal :=
    isSubnormal_inf_subgroupOf (by obtain ⟨-, -, h, -, -⟩ := hX; exact h)
  have hJA : IsPComponent 2 (J.subgroupOf
      (centralizer ({t} : Set H) ⊓ centralizer ({s} : Set H))) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJ hCA hsub).mpr hJp
  refine ⟨hJA, ?_⟩
  have h1 := le_layerIn_of_pComponent (hJ.trans hCA) hJA
  have hsM : s ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.mpr hst
  have h2 := lBalancePLayer_inf_centralizer_le_of_sections (p := 2) hsch hsM hs
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h2
  exact h1.trans h2

end CFSG.ComponentClassification.CatLeafProof.X10C
