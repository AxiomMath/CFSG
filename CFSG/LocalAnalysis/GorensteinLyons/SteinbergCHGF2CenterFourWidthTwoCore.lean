module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2FusedCenterFourImage

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement Pointwise

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem centralizer_conj_package {M Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    {z a g : G} (hMC : M = centralizer ({z} : Set G)) (hg : g⁻¹ * z * g = a) :
    ∃ f : centralizer ({a} : Set G) ≃* M, (∀ x, ((f x : M) : G) = g * x * g⁻¹) ∧
      CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({a} : Set G)) =
        Q.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hmap : (centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom = M := by
    have h := conjugate_centralizer_singleton_eq a g⁻¹
    have hz : g * a * g⁻¹ = z := by rw [← hg]; group
    rw [inv_inv, hz, ← hMC] at h
    rw [← h, CFSG.conjugate, inv_inv]
  let f : centralizer ({a} : Set G) ≃* M :=
    ((MulAut.conj g).subgroupMap (centralizer ({a} : Set G))).trans (MulEquiv.subgroupCongr hmap)
  have hf : ∀ x, ((f x : M) : G) = g * x * g⁻¹ := fun x => rfl
  refine ⟨f, hf, ?_⟩
  have hcore := CFSG.pCore_map_iso 2 f.symm
  rw [hQ, CFSG.inSubgroup, CFSG.inSubgroup, ← hcore, map_map, map_map]
  congr 1
  ext x
  have h1 := hf (f.symm x)
  rw [MulEquiv.apply_symm_apply] at h1
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [h1]
  group

end SteinbergCH

open SteinbergCH

end CFSG.LocalAnalysis.GorensteinLyons
