module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdCovRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67
import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdSchur
import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace HStdList

theorem centerQuot_equiv_of_pSimple {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) {S : Type} [Group S] [Nontrivial S] (f : PSimple 3 L ≃* S) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* S) := by
  haveI : Nontrivial (PSimple 3 L) := f.symm.injective.nontrivial
  obtain ⟨ψ⟩ := hstd_pSimple_equiv_center hL (hstd_ne_top_of_one_lt Finite.one_lt_card)
  exact ⟨ψ.symm.trans f⟩

end HStdList

section Certs


theorem stdCovListAt_holds : StdCovListAt := by
  rintro X _ _ L hL hchev hev ⟨E, hE, hE3⟩
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  haveI : Group.IsPerfect ↥L := ⟨hL.1⟩
  set β := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L with hβ
  have hE' : IsElemAbelian 3 (E.map β) := isElemAbelian_map β hE
  have hE'3 : 3 ^ 3 ≤ Nat.card (E.map β) := by
    rw [Subgroup.card_map_of_injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L)]
    exact hE3
  rcases hchev with ⟨j, hj, ⟨f⟩⟩ | ⟨j, hj, ⟨f⟩⟩
  ·
    cases j with
    | lie d =>
      have hc : d.1.characteristic = 2 := hj
      haveI : Nontrivial (TauCeti.CFSGIndex.lie d).Group :=
        (CFSG.Assembly.lie_finite_simple d).2.toNontrivial
      obtain ⟨e⟩ := HStdList.centerQuot_equiv_of_pSimple hL f
      rcases evenLie hGA hL hev d hc e with h | h
      · exact ⟨_, h, ⟨f⟩⟩
      · exact (no_seven Nat.prime_three (by norm_num) h e hE' hE'3).elim
    | _ => exact (show False from hj).elim
  ·
    cases j with
    | alternating n h =>
      have h5 : n = 5 ∨ n = 6 ∨ n = 8 := by
        simp only [ambiguousChev] at hj
        rcases hj with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
      haveI : Nontrivial (TauCeti.CFSGIndex.alternating n h).Group :=
        alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
      obtain ⟨e⟩ := HStdList.centerQuot_equiv_of_pSimple hL f
      exact (no_seven Nat.prime_three (by norm_num)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, h, rfl, h5⟩)))) e hE' hE'3).elim
    | lie d =>
      haveI : Nontrivial (TauCeti.CFSGIndex.lie d).Group :=
        (CFSG.Assembly.lie_finite_simple d).2.toNontrivial
      obtain ⟨e⟩ := HStdList.centerQuot_equiv_of_pSimple hL f
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        exact (no_seven Nat.prime_three (by norm_num) (sevenIdx_of_ambig_A hj) e hE' hE'3).elim
      | twistedA r q => exact (not_even_of_ambig_twA hGA hL hev hj e).elim
      | _ => exact (show False from hj).elim
    | _ => exact (show False from hj).elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA

end
