module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Comp
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem layer_componentsNoD4_conj_statedSp {r f : ℕ} (hr : 1 ≤ r) {K : Type} [Field K]
    [Finite K] (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (x : StatedSp r K)
    (hx3 : x ^ 3 = 1) :
    PerfectInLayer (MulAut.conj (SymplecticFlag.proj r K x)) ∧
      ComponentsNoD4 (MulAut.conj (SymplecticFlag.proj r K x)) := by
  obtain ⟨hlayer, hcomp⟩ := lieCompsCore_conj_sp_card (a6 := False) slFactorFacts_holds
    suFactorFacts_holds spFactorFacts_holds spFourTwoFacts_holds False.elim False.elim False.elim
    Nat.prime_three (by norm_num) Nat.prime_two hf hK hr (by norm_num) False.elim x
    hx3
  refine ⟨hlayer, fun K' hK' => ?_⟩
  obtain ⟨X, _, _, ⟨hX, -⟩, hfac, g, hg, hk⟩ := hcomp K' hK'
  obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hk
  rw [← Nat.card_congr φ.toEquiv]
  unfold SpFactorOver at hfac
  rcases hfac with ⟨m, j, E, _, _, hm, hj, -, hcard, h4, ⟨e⟩⟩
    | ⟨m, j, q', E, _, _, hm, hj, -, hq', hcard, hne, ⟨e⟩⟩
    | ⟨-, -, s, hs, hne, ⟨e⟩⟩
    | ⟨-, -, hK2, ⟨e⟩⟩
  · exact card_centerQuot_sl_ne hm (Nat.mul_pos hf hj)
      (by rw [Nat.card_eq_fintype_card, hcard, hK, pow_mul])
      (fun h2 => by rw [Nat.card_eq_fintype_card]; exact h4 h2) e
  · exact card_centerQuot_su_ne hm (Nat.mul_pos hf hj) (by rw [hq', hK, pow_mul]) hne
      (by rw [Nat.card_eq_fintype_card, hcard]) e
  · exact card_centerQuot_sp_ne hs hf hK (fun h => hne (by rw [h.1, h.2])) e
  · exact card_centerQuot_spFourTwo_ne hK2 e

private theorem layer_componentsNoD4_statedSp {r : ℕ} (hr : 3 ≤ r) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {β : MulAut (StatedProj (StatedSp r K))}
    (hβ : β ∈ innAutDerived (StatedProj (StatedSp r K))) (hβ3 : β ^ 3 = 1) :
    PerfectInLayer β ∧ ComponentsNoD4 β := by
  have hK1 : Nat.card K = 2 ^ 1 := hK.trans (pow_one 2).symm
  obtain ⟨t, ht⟩ := KD264Lie.mem_inner_of_mem_innAutDerived_statedSp Nat.prime_three
    (by norm_num) Nat.prime_two le_rfl hK1 (by omega) (fun h => absurd h.1 (by omega)) hβ hβ3
  have ht3 : t ^ 3 = 1 := by
    obtain ⟨hsimple, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj
      (r := r) (k := K) (by omega) (fun h => absurd h.1 (by omega))
    haveI := hsimple
    have hnc : ∃ u v : StatedProj (StatedSp r K), u * v ≠ v * u := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun u v => h u v⟩⟩
    exact CFSG.mulAutConj_injective_of_center_eq_bot (b3Lie_center_eq_bot hnc)
      (by rw [map_pow, ht, hβ3, map_one])
  obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (r := r) (K := K)
    (by omega) Nat.prime_three (by norm_num) ht3
  have hβeq : β = MulAut.conj (SymplecticFlag.proj r K x) := by rw [← ht, ← hx]
  rw [hβeq]
  exact layer_componentsNoD4_conj_statedSp (by omega) le_rfl hK1 x hx3

theorem triD4NoB_holds : TriD4NoB := by
  rintro S _ _ - - d ⟨n, q, hd⟩ hc hf ⟨e⟩ α _ hα hα3 - - - - J hJ hT -
  have hp : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_B n q, ← hd]
    exact hc
  obtain ⟨r, hr, hne, hcard, ⟨eP⟩⟩ :=
    KD264Lie.exists_mulEquiv_statedProj_of_isSymplecticIdx (d := d) (by rw [hd]; exact Or.inr hp)
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hr3 : 3 ≤ r := by
    by_contra h
    exact hne ⟨by omega, hf⟩
  let e' : S ≃* StatedProj (StatedSp r ↥d.fixedField) := e.trans eP.symm
  obtain ⟨hlayer, hno⟩ := layer_componentsNoD4_statedSp hr3 (hcard.trans hf)
    ((mem_innAutDerived_congr e').2 hα) (by rw [← map_pow, hα3, map_one])
  exact (false_of_componentsNoD4 (LieSemisimple.perfectInLayer_of_congr e' α hlayer)
    (ComponentsNoD4.of_congr e' hno) hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
