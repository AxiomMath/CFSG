module

public import CFSG.ClassicalInvolution.Asc77.AscE189Main
public import CFSG.ClassicalInvolution.Asc77.AscE187All

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem E189E4.of_e187 (h4 : E187E4C p f) : E189E4 p f := by
  intro G _ _ Ω K S R W H c K' hK' hne R' hR' hR'K' hRR' A hA hRA hX
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRA
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  have hSyl : IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
      (Subgroup.centralizer (A : Set G)) := by
    have hle : P ≤ (S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G) := le_inf hPS' hP.1
    have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ Subgroup.centralizer (A : Set G)) :=
      S'.isPGroup'.to_le inf_le_left
    have heq := hP.eq_of_le hp2 inf_le_right hle
    rw [heq]
    exact hP
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hp hq hΩ S'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  have c' := c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n
  exact h4 G Ω K S' R W' H c' K' hK' hne R' hR' hR'K' hR'S' A hA hRA hX hSyl

end CFSG.ClassicalInvolution.Asc77
