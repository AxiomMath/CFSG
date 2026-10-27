module

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y]

theorem normalizer_le_of_le_centralizer_of_three_le_pRank (hp : p.Prime)
    {Y₀ E X S : Subgroup Y} (R : Sylow p Y)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hXR : X ≤ R) (hX : 2 ≤ CFSG.Open.pRank p X) (hSR : S ≤ R)
    (hSX : S ≤ centralizer (X : Set Y)) (hS : 3 ≤ CFSG.Open.pRank p S) :
    normalizer (X : Set Y) ≤ Y₀ := by
  have hR : 3 ≤ pRank p (R : Subgroup Y) := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hS.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hSR)
  rw [if_pos hR] at hcore
  exact (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hXR hX
    (hS.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (le_sup_of_le_right (le_inf hSR hSX))))).trans hcore

theorem normalizer_inf_le_of_isElemAbelian [Fact p.Prime] {K Y₀ E : Subgroup Y} [K.Normal]
    (R : Sylow p Y) (hER : E ≤ R) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hZ : K ⊓ centralizer (K : Set Y) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K))
    (hT : IsElemAbelian p ((R : Subgroup Y) ⊓ K))
    (h2 : 2 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ K)) :
    normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀ := by
  have hp : p.Prime := Fact.out
  set T₀ : Subgroup Y := (R : Subgroup Y) ⊓ K with hT₀
  have hRT := sylow_le_sup_inf_centralizer_of_not_dvd R hZ hout
  by_cases h3 : 3 ≤ pRank p (R : Subgroup Y)
  · rw [if_pos h3] at hcore
    refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p inf_le_left h2
      ?_).trans hcore
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    exact h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hRT)
  · rw [if_neg h3] at hcore
    have hR2 : CFSG.Open.pRank p (R : Subgroup Y) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      omega
    have hTC : T₀ ≤ centralizer (T₀ : Set Y) := fun t ht => by
      haveI := hT.1
      exact mem_centralizer_iff.mpr fun s hs =>
        congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : T₀) ⟨t, ht⟩)
    have hRC : (R : Subgroup Y) ≤ centralizer (T₀ : Set Y) := hRT.trans (sup_le hTC inf_le_right)
    have hT₀E : T₀ ≤ E := fun t ht =>
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two hp hR2
        hER hE hEc (mem_inf.mp ht).1 (hT.2 t ht) fun q hq =>
          (mem_centralizer_iff.mp (hRC hq) t ht).symm
    exact (le_sSup ⟨T₀, hT₀E, by omega, rfl⟩ : normalizer (T₀ : Set Y) ≤ GLBCore p 1 E).trans
      hcore

theorem isSolvable_inf_of_normalizer_le {K Y₀ : Subgroup Y} (T : Subgroup K)
    (hmax : ∀ H : Subgroup K, normalizer (T : Set K) ≤ H →
      H = normalizer (T : Set K) ∨ H = ⊤)
    (hsol : Group.IsSolvable (normalizer (T : Set K)))
    (hN : (normalizer (T : Set K)).map K.subtype ≤ Y₀) (hKY₀ : ¬ K ≤ Y₀) :
    Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  have hle : normalizer (T : Set K) ≤ Y₀.subgroupOf K := fun k hk =>
    mem_subgroupOf.mpr (hN (mem_map_of_mem K.subtype hk))
  rcases hmax _ hle with h | h
  · haveI : Group.IsSolvable (Y₀.subgroupOf K) := by
      rw [h]
      exact hsol
    let f : (K ⊓ Y₀ : Subgroup Y) →* Y₀.subgroupOf K :=
      { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_subgroupOf.mpr x.2.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy =>
      Subtype.ext (congrArg (fun z : Y₀.subgroupOf K => ((z : K) : Y)) hxy)
  · exact absurd (fun k hk => mem_subgroupOf.mp (h ▸ mem_top (⟨k, hk⟩ : K))) hKY₀

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
