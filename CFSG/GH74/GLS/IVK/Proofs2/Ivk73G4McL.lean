module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4CompTop
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvQuasi
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.Generic.S45.LSporWit
public import CFSG.Sporadic.SmallOddCore.McLLocal

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

theorem mclCt_perfect :
    ⁅mclCt, mclCt⁆ = mclCt := by
  obtain ⟨r, hr, hr0, hgens⟩ : ∃ r ∈ mclRows, r.centOrder = 40320 ∧
      r.centGens = [mclCentTbl 5, mclCentTbl 6] := ⟨_, List.mem_cons_self, rfl, rfl⟩
  have hw := perfWit_of_all perfWit_mcl_2A r hr hr0
  have hspec := (perfWitOK_spec (by norm_num) hw).1
  rw [hgens] at hspec
  rwa [(mclT0_facts).2.2.1] at hspec

theorem mclRho_ker_le_center :
    mclRho.ker ≤ center mclCt := by
  obtain ⟨-, hker⟩ := mclRho_range
  have hz : zpowers (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) = mclRho.ker := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr mclT0_mem_ker)
    rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, mclT0_facts.2.1]
  rw [← hz, zpowers_le, mem_center_iff]
  intro g
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2

theorem mclCt_isComponent_top
    {K : Subgroup mclCt} (hK : CFSG.IsComponent K) : K = ⊤ := by
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hs, -⟩ := mclX_simple
  have hs' : IsSimpleGroup mclRho.range := by
    rw [hrange]
    exact hs
  have hperf : Group.IsPerfect ↥mclCt := Subgroup.isPerfect_iff.2 mclCt_perfect
  exact GHInv.isComponent_eq_top_of_perfect hperf mclRho.rangeRestrict
    mclRho.rangeRestrict_surjective hs'
    (by rw [MonoidHom.ker_rangeRestrict]; exact mclRho_ker_le_center) hK

theorem ivk73_mcl :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  refine ivk73_empty_of_comp_top (P := fun X _ => NativeSporadic.IsSporadic X .McL) ?_ ?_
  · intro L _ _ hL
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥mclP := e.trans mclPermEquiv
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact mcl_outer_card_le
  · intro L _ _ hL y hy2 hy1
    obtain ⟨e⟩ := hL
    let e' : L ≃* ↥mclP := e.trans mclPermEquiv
    have hord : orderOf ((e' y : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' y).2 hord
    exact ⟨↥mclCt, inferInstance, inferInstance, GHInv.centralizerEquivConj mclP e' y hg hgt,
      fun K hK => mclCt_isComponent_top hK⟩

end CFSG.GH74.GLS.IVK
