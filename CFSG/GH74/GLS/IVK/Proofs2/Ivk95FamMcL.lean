module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

theorem ivk95_mcl :
    Ivk95Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := hJ
  let e' : J ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' z : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hz.ord
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' z).2 hord
  let φ := GHInv.centralizerEquivConj mclP e' z hg hgt
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
  have hq : IsQuasisimple ↥(centralizer ({z} : Set J)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs
  refine hz.false_of_quasisimple_centralizer hq (fun q hq5 => ?_)
  rw [Nat.card_congr φ.toEquiv]
  show Nat.card ↥mclCt ≠ _
  rw [(mclT0_facts).2.2.2.1]
  exact (sl2_card_ne_40320 q hq5).symm

end CFSG.GH74.GLS.IVK.Proofs2
