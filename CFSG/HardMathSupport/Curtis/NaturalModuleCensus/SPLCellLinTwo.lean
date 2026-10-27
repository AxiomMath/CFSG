module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellTransport
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.G2

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb (isCyclic_of_le_range sylow_isCyclic_sl2)

open scoped IsMulCommutative

theorem lin_two_false {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Ē : Subgroup (projectiveSL 2 K))
    (hE : CFSG.Open.IsElemAbelian p Ē) (hcard : Nat.card Ē = p ^ 4) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Ē := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 g g.2)⟩
  have hcyc : IsCyclic Ē := isCyclic_of_le_range (p := p) (proj 2 K) (sylow_isCyclic_sl2 h4 hp hp2)
    (Q := Ē) (fun x _ => (proj_surjective 2 K x)) hQp
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card Ē := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 g g.2)
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rw [hord, hcard] at hdvd
  have hle := Nat.le_of_dvd hp.pos hdvd
  have : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at this
  omega

theorem splCellFor_projectiveSL_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r : ℕ) :
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCellFor (projectiveSL 2 K) p r :=
  fun Ē _ _ hE hcard _ _ _ _ _ _ _ => lin_two_false h4 hp hp2 Ē hE hcard

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin
