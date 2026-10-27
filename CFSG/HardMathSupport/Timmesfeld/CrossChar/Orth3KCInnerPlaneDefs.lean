module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Fixed

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal
open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2
section Layer
variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
theorem OddOrderIsometry.residue_cases3 (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hpne : p ≠ 2)
    (hK4 : 4 ≤ Nat.card K)
    {w₀ : V ≃ₗ[K] V} (hw : w₀ ∈ supportedBlock Q x (X - 1)) (hwp : w₀ ^ p = 1) :
    w₀ = 1 ∨ finrank K (fixedSpace x) = 2 ∨
      (FixedLayerListed Q x ∧ w₀ ∈ supportedFixedDerived Q x) := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  set g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    ⟨restrictFixed Q x ⟨w₀, hw⟩, restrictFixed_mem_orthogonalGroup _⟩ with hg
  have hgp : g ^ p = 1 := Subtype.ext (by
    show (restrictFixed Q x ⟨w₀, hw⟩) ^ p = 1
    rw [← map_pow]
    have : (⟨w₀, hw⟩ : ↥(supportedBlock Q x (X - 1))) ^ p = 1 := Subtype.ext hwp
    rw [this, map_one])
  by_cases h1 : finrank K (fixedSpace x) ≤ 1
  · left
    exact hx.eq_one_of_restrictFixed_eq_one hw (eq_one_of_finrank_le_one hQW h1 hp2 hgp)
  by_cases h2 : finrank K (fixedSpace x) = 2
  · exact Or.inr (Or.inl h2)
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  by_cases hlist : FixedLayerListed Q x
  · exact Or.inr (Or.inr ⟨hlist,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.orth3_mem_supportedFixedDerived
      hx hp hpne hK4 h3 hw hwp⟩)
  · exfalso
    exact hlist ⟨h3, by rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega⟩
end Layer
end CFSG.RankThree.PartOne.KCOrthogonal