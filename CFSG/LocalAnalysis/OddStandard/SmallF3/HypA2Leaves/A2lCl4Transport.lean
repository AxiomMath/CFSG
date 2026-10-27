module

public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

theorem cl24_index_of_proj {S : Type} [Group S] [Finite S] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (e : S ≃* StatedProj (StatedOmega Q₀)) (m : ℕ)
    (hcore : ∀ (X : Type) [MulAction (elementaryGroup Q) X]
      [MulAction.IsPretransitive (elementaryGroup Q) X] [Finite X], 2 ≤ Nat.card X →
      m + 1 ≤ Nat.card X)
    (H : Subgroup S) (hH : H ≠ ⊤) : m + 1 ≤ H.index := by
  let ψ : S ≃* ProjElementary Q := e.trans (statedProjEquiv hQ hE)
  let π : elementaryGroup Q →* S :=
    ψ.symm.toMonoidHom.comp
      (QuotientGroup.mk' ((scalars K (ι → K)).subgroupOf (elementaryGroup Q)))
  have hπ : Function.Surjective π :=
    ψ.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  let X := S ⧸ H
  letI : MulAction (elementaryGroup Q) X := MulAction.compHom X π
  haveI : Finite X := Quotient.finite _
  haveI : MulAction.IsPretransitive (elementaryGroup Q) X :=
    MulAction.isPretransitive_compHom (G := X) hπ
  have h2 : 2 ≤ Nat.card X := by
    have hlt : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH
    rw [Subgroup.index] at hlt
    exact hlt
  have hmain : m + 1 ≤ Nat.card X := hcore X h2
  rwa [Subgroup.index]

end CFSG.OddStandard.SmallF3.HypA2Leaves
