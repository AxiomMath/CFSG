module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.RankThree.PartOne.KS.PlaneWitness

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.RankThree.PartOne

theorem noOuterFixesCentralizer_of_conjWitness {A : Type} [Group A] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ConjWitness A p) : NoOuterFixesCentralizer p A := by
  intro σ hσ2 hσ s hs
  by_contra hno
  push Not at hno
  have hσ1 : σ ≠ 1 := fun h1 => hσ (h1 ▸ (innerAut A).one_mem)
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hσs : σ s = s := hno s rfl
  have hc : σ * MulAut.conj s = MulAut.conj s * σ := by
    ext y
    simp [MulAut.conj_apply, hσs]
  obtain ⟨l, hl, hdvd⟩ := h σ s hord hs hc
  have hconj : ∀ g ∈ l, MulAut.conj g * σ * (MulAut.conj g)⁻¹ = σ := by
    intro g hg
    have hσg : σ g = g := hno g (hl g hg).symm
    ext y
    simp [MulAut.conj_apply, hσg, mul_assoc]
  have hprod : (l.map fun g => MulAut.conj g * σ * (MulAut.conj g)⁻¹).prod = σ ^ l.length := by
    rw [List.map_congr_left hconj, List.map_const', List.prod_replicate]
  rw [hprod] at hdvd
  have h2 : p ∣ 2 := hdvd.trans (hord ▸ orderOf_pow_dvd l.length)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
