module

public import CFSG.ClassicalInvolution.Q3.Q3VRowClose

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

@[expose] def SpChain3 (m : ℕ) {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ U : Fin (m + 1) → Subgroup G, U (Fin.last m) ∈ conjClass3 K ∧
    (∀ i j : Fin (m + 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
    (∀ i j : Fin (m + 1), i.val + 1 = j.val → j.val + 1 < m + 1 →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) ∧
    (∀ i j : Fin (m + 1), i.val + 1 = m + 1 → j.val + 2 = m + 1 →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j))

@[expose] def WeakCT3SpHyp (m : ℕ) : Prop :=
  ∀ {X : Type} [Group X] (U : Fin (m + 1) → Subgroup X),
    (∀ i j : Fin (m + 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) →
    (∀ i j : Fin (m + 1), i.val + 1 = j.val → j.val + 1 < m + 1 →
      ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    (∀ i j : Fin (m + 1), i.val + 1 = m + 1 → j.val + 2 = m + 1 →
      ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    ∃ Ψ : StatedSp (m + 1) (GaloisField 3 1) →* X,
      Ψ.ker ≤ Subgroup.center (StatedSp (m + 1) (GaloisField 3 1)) ∧
      (Models.SymplecticPairs.longBlock (GaloisField 3 1) (m + 1) (Fin.last m)).range.map Ψ =
        U (Fin.last m)

theorem weakCT3SpHyp_of_rankOne (m : ℕ)
    (h : ∀ {X : Type} [Group X] (U : Fin (m + 1) → Subgroup X),
      (∀ i j : Fin (m + 1), i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) →
      (∀ i j : Fin (m + 1), i.val + 1 = j.val → j.val + 1 < m + 1 →
        ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
      (∀ i j : Fin (m + 1), i.val + 1 = m + 1 → j.val + 2 = m + 1 →
        ∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
      ∃ Ψ : StatedSp (m + 1) (GaloisField 3 1) →* X,
        Ψ.ker ≤ Subgroup.center (StatedSp (m + 1) (GaloisField 3 1)) ∧
        ∀ k, (CFSG.LieType.CurtisTits.rankOne
          (CFSG.LieType.Universal.Symplectic.rootDatum (m + 1) (GaloisField 3 1)).rootGroup
          k).map Ψ = U k) :
    WeakCT3SpHyp m := by
  intro X _ U hcomm hpair hsp
  obtain ⟨Ψ, hker, hblk⟩ := h U hcomm hpair hsp
  refine ⟨Ψ, hker, ?_⟩
  rw [Models.SymplecticPairs.range_longBlock_eq_rankOne (by show ¬ m + 1 < m + 1; omega)]
  exact hblk (Fin.last m)

@[expose] def ChainPiece3Sp (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), Q3W.RouteD3Setup K z →
      Q3W.LocalShapeC3 1 (CompData.model .PSp m) (conjClass3 K) z →
      Q3W.LocalOddThreeFree3 (conjClass3 K) z → SpChain3 m K

theorem oddLieType_of_spChain3 {m : ℕ} (hm : 2 ≤ m) (hct : WeakCT3SpHyp m) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hR : Q3W.RouteD3Setup K z)
    (hshape : Q3W.LocalShapeC3 1 (CompData.model .PSp m) (conjClass3 K) z)
    (hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z) (hch : SpChain3 m K) :
    Blueprint.OddLieType G := by
  obtain ⟨U, hU, hcomm, hpair, hsp⟩ := hch
  obtain ⟨Ψ, hker, hlong⟩ := hct U hcomm hpair hsp
  exact oddLieType_of_psi_psp3_rank hm hnab hR hshape hO3 Ψ hker (hlong ▸ hU)

end CFSG.ClassicalInvolution.Q3.Q3V
