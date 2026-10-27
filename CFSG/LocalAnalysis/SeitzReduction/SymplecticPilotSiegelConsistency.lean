module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSiegelPieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsTables

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.F4Pilot (ordSL)

section Root

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {F : Type}
  [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F}
  {k : Fin n}

theorem card_filter_pair {j : Fin n} (h : j.val + 1 < n) :
    (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1).card = 2 := by
  rw [filter_pair_eq h]
  exact card_pair_succ h

theorem natCard_simpleRootSL2 {j : Fin n} (h : j.val + 1 < n) :
    Nat.card (simpleRootSL2 F j) = ordSL 2 (Nat.card F) := by
  have h2 : 1 ≤ (Finset.univ.filter fun i : Fin n => j.val ≤ i.val ∧ i.val ≤ j.val + 1).card := by
    rw [card_filter_pair h]
    omega
  rw [← siegelBlock_pair_eq_simpleRootSL2 h, natCard_siegelBlock h2, card_filter_pair h]

theorem FieldNeighbourParam.natCard_pieceCore_short [CharP F 2]
    (P : FieldNeighbourParam e t ι σ k) (hK : 4 ≤ Nat.card K) {j : Fin n} (h : j.val + 1 < n)
    (hkj : k ≠ j) (hk1 : k.val ≠ j.val + 1) :
    Nat.card (pieceCore e {j}) = ordSL 2 (Nat.card F) := by
  rw [P.pieceCore_singleton_eq_map hK hkj (fun _ => hk1), card_map_of_injective P.injective,
    Nat.card_congr (subgroupOfEquivOfLe (simpleRootSL2_le_spBlock_compl hkj fun _ => hk1)).toEquiv,
    natCard_simpleRootSL2 h]

omit [Finite F] in
theorem SwapNeighbourParam.natCard_pieceCore_short [Finite K] [CharP K 2]
    (P : SwapNeighbourParam e t k) (hK : 4 ≤ Nat.card K) {j : Fin n} (h : j.val + 1 < n)
    (hkj : k ≠ j) (hk1 : k.val ≠ j.val + 1) :
    Nat.card (pieceCore e {j}) = ordSL 2 (Nat.card K) ^ 2 := by
  rw [P.pieceCore_singleton_eq_map hK hkj (fun _ => hk1), card_map_of_injective P.injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (subgroupOfEquivOfLe (simpleRootSL2_le_spBlock_compl hkj fun _ => hk1)).toEquiv,
    natCard_simpleRootSL2 h, sq]

end Root

section Consistency

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {F : Type} [Field F] [Finite F] {n : ℕ} {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F}
  {σ : F ≃+* F}

theorem false_of_fieldNeighbourParam_of_siegelSwapParam [CharP F 2] (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n)
    (hF : Nat.card F = Nat.card K ^ 2)
    (P : FieldNeighbourParam e t ι σ ⟨2, by omega⟩) (S : SiegelSwapParam e t) : False := by
  have h1 := P.natCard_pieceCore_short hK (j := ⟨0, by omega⟩) (by simp; omega)
    (by simp [Fin.ext_iff]) (by simp)
  have h2 := S.natCard_pieceCore_singleton hK hn (j := ⟨0, by omega⟩) (by simp; omega)
  have hlt := ordSL_two_sq_lt_ordSL_two_sq (q := Nat.card K) (by omega)
  rw [h1, hF] at h2
  omega

theorem false_of_swapNeighbourParam_of_siegelFieldParam [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n)
    (hF : Nat.card F = Nat.card K ^ 2)
    (P : SwapNeighbourParam e t ⟨2, by omega⟩) (S : SiegelFieldParam e t ι σ) : False := by
  have h1 := P.natCard_pieceCore_short hK (j := ⟨0, by omega⟩) (by simp; omega)
    (by simp [Fin.ext_iff]) (by simp)
  have h2 := S.natCard_pieceCore_singleton hK hn (j := ⟨0, by omega⟩) (by simp; omega)
  have hlt := ordSL_two_sq_lt_ordSL_two_sq (q := Nat.card K) (by omega)
  rw [h1, hF] at h2
  omega

end Consistency

end CFSG.SeitzReduction.SymplecticPilot
