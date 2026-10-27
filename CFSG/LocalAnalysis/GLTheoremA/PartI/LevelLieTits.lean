module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTTits
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  (isSolvable_fixSubgroup_tits false_of_open_quasisimple_of_isSolvable)
open CFSG.Sporadic.Schreier.Tits (titsModelEquiv card_titsD)

private theorem lieRowTits_no_glaPComponent {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {C I : Subgroup S} (hC : Group.IsSolvable ↥C) (hI : GLAPComponent p C I) : False := by
  have hq : CFSG.Open.IsQuasisimple (↥I ⧸ GLAPPrimeCore p ↥I) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isQuasisimple_quotient_of_glaPComponent hp hI
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hI.1)
      (Subgroup.inclusion_injective hI.1)
  haveI : Group.IsSolvable (↥I ⧸ GLAPPrimeCore p ↥I) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥I))
  exact false_of_open_quasisimple_of_isSolvable hq inferInstance

private theorem lieRowTits_kLevel_le_two {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

private theorem lieRowTits_fixSubgroup_one {K : Type*} [Group K] :
    fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

theorem lieRowTits_downLe_two_of_solvable {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a) (hk : catalogIs S (k2 p))
    (hsol : ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → Group.IsSolvable ↥(fixSubgroup β)) :
    DownLe p 2 S := by
  intro β hβ I hI
  by_cases h1 : β = 1
  · subst h1
    rw [lieRowTits_fixSubgroup_one] at hI
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv hp hnc hI
    rw [kLevel_congr p f]
    exact lieRowTits_kLevel_le_two hk
  · exact (lieRowTits_no_glaPComponent hp (hsol β hβ h1) hI).elim

private theorem lieRowTits_nonab {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)

section TitsRows

private theorem lieRowTits_card (hv : (TauCeti.LieTypeIndex.tits).Valid) {S : Type} [Group S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) :
    Nat.card S = 17971200 := by
  obtain ⟨e⟩ := titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  rw [Nat.card_congr e.toEquiv, card_titsD]

theorem kdLieRowTitsThree_holds : KDLieRowTitsThree := by
  unfold KDLieRowTitsThree
  intro hv
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.tits, hv⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := hfin
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := hsimp
  have hcard : Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group = 17971200 :=
    lieRowTits_card hv ⟨MulEquiv.refl _⟩
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group, a * b ≠ b * a :=
    lieRowTits_nonab (by rw [hcard]; norm_num)
  have hk : catalogIs (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.tits, hv⟩, by simp [k2, k2Lie], ⟨MulEquiv.refl _⟩⟩
  refine lieRowTits_downLe_two_of_solvable (p := 3) Nat.prime_three hnc hk ?_
  intro β hβ hβ1
  exact isSolvable_fixSubgroup_tits hv hnc ⟨MulEquiv.refl _⟩ Nat.prime_three (by norm_num)
    hβ hβ1

theorem kdLieRowTitsFive_holds : KDLieRowTitsFive := by
  unfold KDLieRowTitsFive
  intro hv
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.tits, hv⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := hfin
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := hsimp
  have hcard : Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group = 17971200 :=
    lieRowTits_card hv ⟨MulEquiv.refl _⟩
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group, a * b ≠ b * a :=
    lieRowTits_nonab (by rw [hcard]; norm_num)
  have hk : catalogIs (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group (k2 5) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.tits, hv⟩, by simp [k2, k2Lie], ⟨MulEquiv.refl _⟩⟩
  refine lieRowTits_downLe_two_of_solvable (p := 5) (by norm_num) hnc hk ?_
  intro β hβ hβ1
  exact isSolvable_fixSubgroup_tits hv hnc ⟨MulEquiv.refl _⟩ (by norm_num) (by norm_num)
    hβ hβ1

end TitsRows

end CFSG.LocalAnalysis.GLTheoremA
