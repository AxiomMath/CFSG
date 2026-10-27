module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable def statedProjEquivProjectiveSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem centralizes_of_linear {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) {w : G} (hwU : w ∈ U)
    (hwS : w ∈ Subgroup.centralizer (S : Set G)) : L ≤ Subgroup.centralizer ({w} : Set G) := by
  let e' : L ⧸ Subgroup.center L ≃* projectiveSL n K := e.trans (statedProjEquivProjectiveSL n K)
  exact centralizes_of_family h
    (NoStronglyClosedElemAbelian.of_mulEquiv e' (noStronglyClosed_projectiveSL hn))
    (SylowCentralizingAutInner.of_mulEquiv e' (sylowCentralizingAutInner_projectiveSL hn)) hwU hwS

theorem centralizes_of_statedClassicalModel_psl {G : Type} [Group G] [Finite G]
    {H S U L : Subgroup G} (h : StrongClosureComponent H S U L) {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n 2 f) {w : G}
    (hwU : w ∈ U) (hwS : w ∈ Subgroup.centralizer (S : Set G)) :
    L ≤ Subgroup.centralizer ({w} : Set G) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := hmodel
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  exact centralizes_of_linear h hn e hwU hwS

end CFSG.QuasithinUnique.K1
