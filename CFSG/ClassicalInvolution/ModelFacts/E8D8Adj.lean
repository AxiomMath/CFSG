module

public import CFSG.ClassicalInvolution.ModelFacts.E8D8AdjPair
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (centralQuot_plus finrank_plus fundSet)

variable (p f : ℕ) [Fact p.Prime]

theorem e8D8NoThreeAdj : E8D8NoThreeAdj p f := by
  intro hp2 hq
  obtain ⟨-, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : Module.finrank (GaloisField p f) (Fin 8 ⊕ Fin 8 → GaloisField p f) = 16 := by
    rw [finrank_plus]
  have cq := centralQuot_plus (p := p) (f := f) hp2 (by norm_num : 4 ≤ 8) (by norm_num : 3 ≤ 8) hq
  unfold D8NoThreeAdjPairs
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by norm_num : 3 ≤ 8)]
  intro P hfund hadj hcomm
  choose ι hι using fun i j => cq.map_mem _ (hfund i j)
  exact ModelFacts.E8D8.false_of_three_adjacent_pairs hodd (by omega) (by omega)
    (fun i j => (P i j).map (spinAction (quadPlus 8 (GaloisField p f)))) ι hι
    (fun i => cq.modelAdj (hfund i 0) (hfund i 1) (hadj i).1)
    (fun i i' h j j' => (cq.commutes_iff (hfund i j)).mpr (hcomm i i' h j j'))

end CFSG.ClassicalInvolution.RouteD.TypeE8
