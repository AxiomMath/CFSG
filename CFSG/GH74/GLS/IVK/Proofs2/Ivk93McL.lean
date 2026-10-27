module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Quasi
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem ivk93_mcl :
    Ivk93Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  refine ivk93_empty_of_cfg fun J _ _ hJ x _ q L₁ L₂ hc => ?_
  obtain ⟨e⟩ := hJ
  let e' : J ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' x : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hc.ord
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' x).2 hord
  let φ := GHInv.centralizerEquivConj mclP e' x hg hgt
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup ↥mclRho.range := by
    rw [hrange]
    exact hs
  have hnab' : ∃ a b : ↥mclRho.range, a * b ≠ b * a := by
    rw [hrange]
    exact hnab
  have hperf : Group.IsPerfect ↥mclCt := Subgroup.isPerfect_iff.2 mclCt_perfect
  have hqs : IsQuasisimple ↥mclCt :=
    GHInv.isQuasisimple_of_perfect_cover hperf mclRho.rangeRestrict mclRho.rangeRestrict_surjective hs'
      (by
        obtain ⟨a, b, hab⟩ := hnab'
        exact ⟨a, b, hab⟩)
      (by rw [MonoidHom.ker_rangeRestrict]; exact mclRho_ker_le_center)
  have hq : IsQuasisimple ↥(centralizer ({x} : Set J)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs
  exact hc.false_of_quasisimple_centralizer hq

end CFSG.GH74.GLS.IVK.Proofs2
