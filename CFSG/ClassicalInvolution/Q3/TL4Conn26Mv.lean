module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)

namespace LinkMove

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem closure_pair_mem (hL : TightLargeHypR r n Y R S t) {B : Subgroup Y}
    (hB : IsElemAbelian 2 B) (htB : t ∈ B) {a : Y} (haB : a ∈ B) (ha1 : a ≠ 1) (hat : a ≠ t) :
    Subgroup.closure ({t, a} : Set Y) ∈ CFSG.Open.signalizerFunctorEk 2 2 B := by
  have ht := hL.datum.isUniqueInvolution_core
  have ha2 : a * a = 1 := (sq a).symm.trans (hB.2 a haB)
  have hta : t * a = a * t := by
    have h := hB.1.is_comm.comm ⟨t, htB⟩ ⟨a, haB⟩
    exact congrArg Subtype.val h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact htB
    · exact haB
  · rw [Balance.Bootstrap.card_closure_pair_eq_four ht.sq ha2 ht.ne_one ha1 hat.symm hta]
    norm_num

theorem oddCoreOf_layerY_le_rankTwoSpan (hL : TightLargeHypR r n Y R S t) {B : Subgroup Y}
    (hB : IsElemAbelian 2 B) (h8 : Nat.card B = 8)
    (hBt : B ≤ Subgroup.centralizer ({t} : Set Y)) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤ rankTwoSpan B := by
  have hΩ := hL.datum.hypOmegaGen
  have hnorm : B ≤ Subgroup.normalizer
      (oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) : Set Y) := by
    intro a ha
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq,
      layerY_conjSub_eq hΩ.conjInvariant (hBt ha)]
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two _ _ hB (by rw [h8]; norm_num) hnorm
    (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

end Cit3

end LinkMove

end CFSG.ClassicalInvolution.Q3.TL4
