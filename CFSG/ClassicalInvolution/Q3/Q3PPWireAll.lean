module

public import CFSG.ClassicalInvolution.Q3.Q3PPWire
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeWire
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeShape
public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3NM

@[expose] def MFComp (c : CompData) : Prop :=
  FixedOddFree (c.G ⧸ Subgroup.center c.G) ∨ FixedOddFreeFund c

theorem mfComp_m11 : MFComp CompData.m11 := Or.inl (fixedOddFree_of_kind_m11 rfl)

theorem mfComp_psl3 : MFComp (CompData.model .PSL 3) := Or.inr fixedOddFreeFund_psl3

theorem mfComp_psu3 : MFComp (CompData.model .PSU 3) := Or.inr fixedOddFreeFund_psu3

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem exists_lieSystem_z₁ (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) :
    ∃ (ι : Type) (_ : Finite ι), Nonempty (LieSystemData3 ι
      (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) := by
  have hnc : ¬ ({z₁} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have hmem : z₁ ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact Q3W.not_subset_center_of_ne_one hnab h.cls₁.ne_one (Set.singleton_subset_iff.mpr hmem)
  exact hR.ih {z₁} hnc

theorem mfComp_of_third [Finite ι] (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂)) (h1 : TwinFreeAt (conjClass3 K) K₁ z₁)
    (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0)) :
    MFComp (D.kind i) := by
  rcases h.kind_cases_of_third_final hR hnab hN hXN h1 h2 D hi with
    hm | ⟨t, n, ht, -, hk⟩ | ⟨t, ht, -, hk⟩
  · rw [hm]
    exact mfComp_m11
  · rcases ht with rfl | rfl
    · rw [hk]
      exact hG2
    · rw [hk]
      exact hTD4
  · rcases ht with rfl | rfl
    · rw [hk]
      exact mfComp_psl3
    · rw [hk]
      exact mfComp_psu3

theorem oddCoreIn_layer_prod_eq_bot_of_kinds [Finite ι] (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0)) :
    oddCoreIn (centralizingLayer (conjClass3 K) {z₁ * z₂}) = ⊥ :=
  h.oddCoreIn_layer_prod_eq_bot_of_third hOA hR hnab hN hXN h1 h2 D hi
    (h.mfComp_of_third hR hnab hN hXN h1 h2 D hi hG2 hTD4)
    (h.kleinAt_of_third hR hnab hN hXN h1 h2 D hi)

theorem alphaCore_edge_eq_bot_of_noTriple (hOA : OddAutLayerRigidHyp) (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hTwin : NonClassicalAt (conjClass3 K) (z₁ * z₂) →
      ¬ (TwinFreeAt (conjClass3 K) K₁ z₁ ∧ TwinFreeAt (conjClass3 K) K₂ z₂) →
      alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥)
    (hG2 : MFComp (CompData.model .G2 0)) (hTD4 : MFComp (CompData.model .trialityD4 0)) :
    alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
  by_cases hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂)
  · by_cases ht : TwinFreeAt (conjClass3 K) K₁ z₁ ∧ TwinFreeAt (conjClass3 K) K₂ z₂
    · obtain ⟨ι, hι, ⟨D⟩⟩ := h.exists_lieSystem_z₁ hR hnab
      have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
      obtain ⟨i, hi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₂, hK₂, rfl⟩)
      exact h.alphaCore_edge_eq_bot_of_oddCoreIn_layer_eq_bot hR
        (h.oddCoreIn_layer_prod_eq_bot_of_kinds hOA hR hnab hN hXN ht.1 ht.2 D hi hG2 hTD4)
    · exact hTwin hXN ht
  · unfold NonClassicalAt at hXN
    push Not at hXN
    obtain ⟨M, hM, m, hm, rfl⟩ := hXN
    have hO := oddCoreIn_centralizingLayer_le hR.inClass.conjInvariant (z₁ * z₂)
    rw [Q3OF.involutionOddCore_eq_bot_of_member hR hM hm] at hO
    exact h.alphaCore_edge_eq_bot_of_oddCoreIn_layer_eq_bot hR (le_bot_iff.mp hO)

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
