module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts27

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G]

private def toCz (t : G) (z : ↥(centralizer ({t} : Set G))) :
    ↥(centralizer ({t} : Set G) ⊓ centralizer ({(z : G)} : Set G)) →*
      ↥(centralizer ({z} : Set ↥(centralizer ({t} : Set G)))) where
  toFun c := ⟨⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem toCz_surjective (t : G) (z : ↥(centralizer ({t} : Set G))) :
    Function.Surjective (toCz t z) := by
  rintro ⟨y, hy⟩
  have hyz : (y : G) * (z : G) = (z : G) * (y : G) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  exact ⟨⟨(y : G), Subgroup.mem_inf.mpr
    ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩⟩, rfl⟩

theorem HaradaFacts27.toCzS5 {t : G} {E : Subgroup ↥(centralizer ({t} : Set G))}
    {a z b z₁ : ↥(centralizer ({t} : Set G))}
    {S T T' W0 R0 F : Subgroup ↥(centralizer ({t} : Set G))}
    {ι : Elem2 6 →* ↥(centralizer ({t} : Set G))} {zv : V6}
    (hF : HaradaFacts27 ↥(centralizer ({t} : Set G)) E a z b z₁ S T T' W0 ι zv R0 F) :
    ∃ ψ : ↥(centralizer ({t} : Set G) ⊓ centralizer ({(z : G)} : Set G)) →*
        Equiv.Perm (Fin 5),
      Function.Surjective ψ ∧
        ψ.ker = (R0.map (centralizer ({t} : Set G)).subtype).subgroupOf
          (centralizer ({t} : Set G) ⊓ centralizer ({(z : G)} : Set G)) := by
  obtain ⟨ψ, hψ, hker⟩ := hF.C_hom
  refine ⟨ψ.comp (toCz t z), hψ.comp (toCz_surjective t z), ?_⟩
  ext c
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_map_iff_mem (centralizer ({t} : Set G)).subtype_injective).symm

end CFSG.EvenSporadicStandard.HNRecog
