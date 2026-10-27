module

public import CFSG.Dihedral.OriginalCosetModel
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem aSeven_equiv_sylow_aligned (e : G ≃* alternatingGroup (Fin 7)) :
    ∃ f : G ≃* alternatingGroup (Fin 7), f d.t = a7t ∧
      (d.S : Subgroup G).map f.toMonoidHom = a7S := by
  obtain ⟨f, hft⟩ := d.aSeven_equiv_aligned e
  let C := Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup)
  let T : Sylow 2 ASevenCertificateGroup :=
    d.S.mapSurjective (f := f.toMonoidHom) f.surjective
  have hTmap : (T : Subgroup ASevenCertificateGroup) = (d.S : Subgroup G).map f.toMonoidHom :=
    Sylow.coe_mapSurjective (f := f.toMonoidHom) f.surjective d.S
  have hTC : (T : Subgroup ASevenCertificateGroup) ≤ C := by
    rw [hTmap]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    change f x * a7t = a7t * f x
    have hxC : x ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.sylow_le_centralizer hx
    simpa only [map_mul, hft] using
      congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hAC : (a7Sylow : Subgroup ASevenCertificateGroup) ≤ C := by
    change a7S ≤ C
    exact a7S_le_centralizer_t
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq C (T.subtype hTC) (a7Sylow.subtype hAC)
  rw [Sylow.smul_subtype] at hx
  have hxSylow : (x : ASevenCertificateGroup) • T = a7Sylow := Sylow.subtype_injective hx
  let c : MulAut ASevenCertificateGroup := MulAut.conj (x : ASevenCertificateGroup)
  refine ⟨f.trans c, ?_, ?_⟩
  · change (x : ASevenCertificateGroup) * f d.t * (x : ASevenCertificateGroup)⁻¹ = a7t
    rw [hft]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp x.property
    rw [hcomm]
    group
  · have hmap : (T : Subgroup ASevenCertificateGroup).map c.toMonoidHom = a7S := by
      exact congrArg (fun P : Sylow 2 ASevenCertificateGroup => (P : Subgroup ASevenCertificateGroup)) hxSylow
    change (d.S : Subgroup G).map (c.toMonoidHom.comp f.toMonoidHom) = a7S
    rw [← Subgroup.map_map, ← hTmap]
    exact hmap

theorem aSeven_equiv_R_sylow_aligned (hR : d.R ≠ ⊥)
    (e : G ≃* alternatingGroup (Fin 7)) :
    ∃ f : G ≃* alternatingGroup (Fin 7), f d.t = a7t ∧
      (d.S : Subgroup G).map f.toMonoidHom = a7S ∧ d.R.map f.toMonoidHom = a7U := by
  obtain ⟨f, ht, hS⟩ := d.aSeven_equiv_sylow_aligned e
  exact ⟨f, ht, hS, d.R_map_eq_a7U hR f ht⟩

end CFSG.DihedralBlueprint.OriginalData
