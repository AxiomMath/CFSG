module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaMove
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11TransProved
public import CFSG.GH74.KGroups.M11
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Sporadic.Bridge.M11

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.Sporadic.Schreier CFSG.GH74.KGroups
open CFSG.Sporadic.Mathieu (m11gA m11gB)

theorem kFactTenNineWCGammaM11 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp : CFSG.Blueprint.NativeSporadic.IsSporadic K .M11 := ⟨e.trans eC.symm⟩
  obtain ⟨M, hP, hA⟩ := M11.autModel hsp
  refine false_of_transitive_gamma ?_ ?_ ?_ ?_ S A hA3 Y hY hwc
  ·
    intro k hk
    have hgen : ∀ g ∈ ({m11gA, m11gB} : Set (Equiv.Perm (Fin 11))),
        (M.e k : Equiv.Perm (Fin 11)) * g = g * (M.e k : Equiv.Perm (Fin 11)) := by
      intro g hg
      have hgP : g ∈ M.P := by
        rw [hP, M11.Q_closure]
        exact Subgroup.subset_closure hg
      have h := congrArg (fun y : K => ((M.e y : M.P) : Equiv.Perm (Fin 11)))
        (hk (M.e.symm ⟨g, hgP⟩))
      simpa using h
    have hmem : (M.e k : Equiv.Perm (Fin 11)) ∈ CFSG.Blueprint.NativeSporadic.M11 := by
      rw [← M11.Q_subgroup, ← hP]
      exact (M.e k).2
    have hA' := hgen m11gA (Set.mem_insert _ _)
    have hB' := hgen m11gB (Set.mem_insert_of_mem _ rfl)
    have h2 : (M.e k : Equiv.Perm (Fin 11)) = 1 :=
      Certificates.certificate5125.2.2.2.2.2.2.1 _ hmem hA' hB'
    apply M.e.injective
    rw [map_one]
    exact Subtype.ext h2
  ·
    intro φ _
    exact M.inner_of_mem φ (by rw [hP, ← hA]; exact (M.Φ φ).2)
  · intro T a b ha hb ha1 hb1
    exact m11SylowTransitive_proved K ⟨e⟩ T a b ha hb ha1 hb1
  · intro T
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eC.symm)
      (IsPGroup.of_card M11Model.sylowR_card) M11Model.sylowR_index T
    rw [hΦ, Subgroup.card_map_of_injective Φ.injective, M11Model.sylowR_card]
    norm_num

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
