module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Aut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ExcPar
public import CFSG.GH74.GLS.Stage2.OddAut.OutCyc

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.GH74.GLS.Stage2.OddAut

theorem g2_false_of_rp {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = p ^ f)
    {V Z : Subgroup (MulAut (adjointGroup .G2 K))} (h2 : N2Cfg (adjointGroup .G2 K) p V Z)
    (h3 : N3Full (adjointGroup .G2 K) V Z) : False := by
  classical
  obtain ⟨hAodd, H, hH, hHc, Θ, hΘk⟩ := g2_aut_facts Fact.out hp2 hf K hK
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨-, -, hVe, hVc, -, hZodd, -, -, -⟩ := id h2
  have := hVe
  have hVA : V ≤ diagonalFieldActors .G2 K := by
    intro v hv
    apply hAodd v
    have h1 : v ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ hv
    have h3 : orderOf v ∣ p := orderOf_dvd_of_pow_eq_one h1
    exact Odd.of_dvd_nat hpodd h3
  have hZA : Z ≤ diagonalFieldActors .G2 K := by
    intro z hz
    apply hAodd z
    exact Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard Z hz)
  obtain ⟨v, hvV, hv1, hΘv⟩ := exists_mem_ker_of_isCyclic (r := p) Θ hVc
  have hvinn : v ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
    rw [← hΘk]
    exact hΘv
  exact false_of_rp_data (holds_adjointGroup_tag .G2 K p) center_adjointGroup_eq_bot
    (pCharData_adjoint .G2 K p) (conj_mem_diagonalFieldActors .G2 K) hVA hZA h2 h3
    ⟨v, hvV, hv1, hvinn⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
