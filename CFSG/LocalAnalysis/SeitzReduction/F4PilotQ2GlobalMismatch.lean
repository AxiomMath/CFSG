module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2PairMismatch
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2GlobalTables
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowCat

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)

theorem twoOverlapKindPairs_eq : twoOverlapKindPairs = consistentKindPairsTwo :=
  rfl

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def coreCentCard (e : L ≃* adjointGroup .F4 K)
    (W U : Subgroup (adjointGroup .F4 K)) : ℕ :=
  Nat.card (centralizer (subgroupToG e U : Set G) ⊓ centralizerPerfectCore (subgroupToG e W) :
    Subgroup G)

theorem coreCentCard_map_conj [Finite G] (e : L ≃* adjointGroup .F4 K)
    (W U : Subgroup (adjointGroup .F4 K)) (m : adjointGroup .F4 K) :
    coreCentCard e (W.map (MulAut.conj m).toMonoidHom) (U.map (MulAut.conj m).toMonoidHom) =
      coreCentCard e W U := by
  unfold coreCentCard
  rw [subgroupToG_map_conj, subgroupToG_map_conj, ← map_centralizerPerfectCore,
    ← map_centralizer_mulEquiv, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
  exact Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem coreCentCard_trans_symm (e : L ≃* adjointGroup .F4 K) (ψ : MulAut (adjointGroup .F4 K))
    (W U : Subgroup (adjointGroup .F4 K)) :
    coreCentCard (e.trans ψ.symm) W U =
      coreCentCard e (W.map ψ.toMonoidHom) (U.map ψ.toMonoidHom) := by
  unfold coreCentCard
  rw [subgroupToG_trans_symm, subgroupToG_trans_symm]

end Transport

section Pieces

@[expose] def TwoOverlapInvInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∃ (T₀ UL US : Subgroup (adjointGroup .F4 K)) (m : adjointGroup .F4 K),
      T₀.map (graphAutF4 K).toMonoidHom = T₀.map (MulAut.conj m).toMonoidHom ∧
      US.map (graphAutF4 K).toMonoidHom = UL.map (MulAut.conj m).toMonoidHom ∧
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → ∀ κ : Sp6Kind, TwoKindAt e t X₀ κ →
          Nat.card (centralizerPerfectCore (subgroupToG e T₀)) = twoDiagPieceOrder κ ∧
          (κ.IsGraphKind → coreCentCard e T₀ UL = twoOverlapInvOrderL κ ∧
            coreCentCard e T₀ US = twoOverlapInvOrderS κ)

theorem mem_consistentKindPairsTwo_of_overlapInvInput (hP : TwoOverlapInvInput) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ κ' : Sp6Kind} (hκ : TwoKindAt e t X₀ κ)
    (hκ' : TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ κ') :
    (κ, κ') ∈ consistentKindPairsTwo := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨T₀, UL, US, m, hm, hmU, htab⟩ := hP K hK2 X₀ hXJ hcyc hX₀
  obtain ⟨hT, hL⟩ := htab G L e t hw κ hκ
  obtain ⟨hT', hS'⟩ := htab G L (e.trans (graphAutF4 K).symm) t hw κ' hκ'
  rw [subgroupToG_trans_symm, hm, card_centralizerPerfectCore_subgroupToG_map_conj, hT] at hT'
  rw [← twoOverlapKindPairs_eq]
  refine mem_twoOverlapKindPairs_of_compat ⟨hT', fun hg hg' => ?_⟩
  have h1 := (hS' hg').2
  rw [coreCentCard_trans_symm, hm, hmU, coreCentCard_map_conj, (hL hg).1] at h1
  exact h1

theorem twoMismatchInput_of_overlapInvInput (hP : TwoOverlapInvInput) : TwoMismatchInput := by
  intro κ κ' hne G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  exact hne (mem_consistentKindPairsTwo_of_overlapInvInput hP hw e hXJ hcyc hX₀ hκ hκ')

end Pieces

section Rows

theorem twoRowsCatInput_of_overlapInvInput (hP : TwoOverlapInvInput)
    (hF : TwoFieldPairInput) (hS : TwoSwapPairInput) (hE : TwoE6PairInput)
    (hT : TwoTwistedE6PairInput) : TwoRowsCatInput :=
  twoRowsCatInput_of_pairRows (twoMismatchInput_of_overlapInvInput hP) hF hS hE hT

end Rows

end CFSG.SeitzReduction.F4Pilot
