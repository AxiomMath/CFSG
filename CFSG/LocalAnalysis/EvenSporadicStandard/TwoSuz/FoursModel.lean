module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.FoursAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterPerfect
public import Certificates.Certificate25010

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Sporadic.SuzOddCore CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Words

theorem outer_lettersOK_iff {k : ℕ} {w : List ℤ} :
    lettersOK k w = true ↔ ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k := by
  simp [lettersOK, List.all_eq_true]

theorem lettersOK_outerInvW {k : ℕ} {w : List ℤ} (hw : lettersOK k w = true) :
    lettersOK k (outerInvW w) = true := by
  rw [outer_lettersOK_iff] at hw ⊢
  intro l hl
  simp only [outerInvW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  exact ⟨by simpa using this.1, by simpa using this.2⟩

theorem rep_wordArr_outerEvalS {H : Type*} [Group H] (q : H →* Equiv.Perm (Fin 1782)) {a c : H}
    (hqa : Rep 1782 b0Arr (q a)) (hqc : Rep 1782 b1Arr (q c))
    (hinv0 : isInvA 1782 b0Arr (invCand 1782 b0Arr) = true)
    (hinv1 : isInvA 1782 b1Arr (invCand 1782 b1Arr) = true) {w : List ℤ}
    (hw : lettersOK 2 w = true) :
    Rep 1782 (wordArr 1782 #[b0Arr, b1Arr] w)
      (q (outerEvalS (fun j => if j = 0 then a else c) w)) := by
  have hA : ∀ j < 2, Rep 1782 (#[b0Arr, b1Arr] : Array (Array ℕ))[j]!
      (q ((fun j => if j = 0 then a else c) j)) := by
    intro j hj
    interval_cases j
    · exact hqa
    · exact hqc
  have hAinv : ∀ j < 2, Rep 1782 ((#[b0Arr, b1Arr] : Array (Array ℕ)).map (invCand 1782))[j]!
      (q ((fun j => if j = 0 then a else c) j))⁻¹ := by
    intro j hj
    rw [getElem!_map_of_lt (by simp; omega)]
    interval_cases j
    · exact rep_inv_of_isInvA hqa hinv0
    · exact rep_inv_of_isInvA hqc hinv1
  rw [map_outerEvalS]
  exact rep_outerEvalS hA hAinv w hw

theorem rep_wordArr_outerEvalS_inv {H : Type*} [Group H] (q : H →* Equiv.Perm (Fin 1782))
    {a c : H} (hqa : Rep 1782 b0Arr (q a)) (hqc : Rep 1782 b1Arr (q c))
    (hinv0 : isInvA 1782 b0Arr (invCand 1782 b0Arr) = true)
    (hinv1 : isInvA 1782 b1Arr (invCand 1782 b1Arr) = true) {w : List ℤ}
    (hw : lettersOK 2 w = true) :
    Rep 1782 (wordArr 1782 #[b0Arr, b1Arr] (outerInvW w))
      (q (outerEvalS (fun j => if j = 0 then a else c) w))⁻¹ := by
  have h := rep_wordArr_outerEvalS q hqa hqc hinv0 hinv1 (lettersOK_outerInvW hw)
  rwa [outerEvalS_invW _ _ fun l hl => ((outer_lettersOK_iff.1 hw) l hl).1, map_inv] at h

end Words

section Witness


theorem exists_fours_witness {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) :
    ∃ x₁ : L, x₁ * x₁ = 1 ∧ q x₁ ≠ 1 ∧ ∀ i : ℕ, (i = 2 ∨ i = 3) →
      ∃ l c : suzM, (l : Equiv.Perm (Fin 1782)) * suzInv i * (l : Equiv.Perm (Fin 1782))⁻¹ *
        (suzInv i)⁻¹ = (c : Equiv.Perm (Fin 1782)) * (q x₁ : Equiv.Perm (Fin 1782)) *
          (c : Equiv.Perm (Fin 1782))⁻¹ := by
  obtain ⟨ψ, a, c, hψ, hψt, hψ0, hψ1, hr0, hr1, hinv0, hinv1⟩ :=
    exists_twisted_gens q hq ht hker hcen
  have hcert := Certificates.certificate25010
  simp only [foursWitnessCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcert
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hlx⟩, hl2⟩, hc2⟩, hl3⟩, hc3⟩, hsq⟩, hne⟩, hp2⟩, hp3⟩ := hcert
  set gensL : ℕ → L := fun j => if j = 0 then a else c with hgensL
  set q' : L →* Equiv.Perm (Fin 1782) := suzM.subtype.comp q with hq'
  have hrep : ∀ {w : List ℤ}, lettersOK 2 w = true →
      Rep 1782 (wordArr 1782 #[b0Arr, b1Arr] w) (q' (outerEvalS gensL w)) := fun hw =>
    rep_wordArr_outerEvalS q' hr0 hr1 hinv0 hinv1 hw
  have hU0 : ∀ j < 2, ψ (gensL j) = outerLvl0.letterU hv (2 * j) := by
    intro j hj
    refine Units.ext ?_
    rw [GenSys.outer_val_letterU_even]
    interval_cases j
    · rw [outerLvl0_mats_zero]
      exact hψ0
    · rw [outerLvl0_mats_one]
      exact hψ1
  have hψx : ψ (outerEvalS gensL foursWitnessX) =
      outerLvl0.evalU hv (foursWitnessX.map zCode) :=
    GenSys.outer_transfer outerLvl0 hv ψ hU0 hlx
  refine ⟨outerEvalS gensL foursWitnessX, ?_, ?_, ?_⟩
  · apply hψ
    rw [map_mul, hψx, map_one]
    refine Units.ext ?_
    rw [Units.val_mul, ← GenSys.ofMt_eval outerLvl0 hv, ← ofMt_mulM, hsq, ofMt_oneM]
    rfl
  · intro h1
    have h1' : q' (outerEvalS gensL foursWitnessX) = 1 := congrArg Subtype.val h1
    have h2 := (eqA_iff (hrep hlx) (rep_idA (n := 1782))).2 h1'
    rw [foursWordArr] at hne
    rw [hne] at h2
    exact Bool.false_ne_true h2
  · intro i hi
    have hp : foursWitnessPermOK i = true := by
      rcases hi with rfl | rfl
      · exact hp2
      · exact hp3
    have hTr : Rep 1782 (tArr i) (suzInv i) := rep_suzInv (by omega)
    have hLc : lettersOK 2 (foursWitnessL i) = true ∧ lettersOK 2 (foursWitnessC i) = true := by
      rcases hi with rfl | rfl
      · exact ⟨hl2, hc2⟩
      · exact ⟨hl3, hc3⟩
    obtain ⟨hl, hc⟩ := hLc
    simp only [foursWitnessPermOK, Bool.and_eq_true] at hp
    have hττ : suzInv i * suzInv i = 1 := eq_of_eqA (rep_compA hTr hTr) rep_idA hp.1
    have hR1 := rep_compA (rep_compA (rep_compA (hrep hl) hTr)
      (rep_wordArr_outerEvalS_inv q' hr0 hr1 hinv0 hinv1 hl)) hTr
    have hR2 := rep_compA (rep_compA (hrep hc) (hrep hlx))
      (rep_wordArr_outerEvalS_inv q' hr0 hr1 hinv0 hinv1 hc)
    have key := eq_of_eqA hR1 hR2 hp.2
    refine ⟨q (outerEvalS gensL (foursWitnessL i)), q (outerEvalS gensL (foursWitnessC i)), ?_⟩
    rw [inv_eq_of_mul_eq_one_right hττ]
    exact key

end Witness

section Condition


theorem foursGroupCondition_of_isSporadic {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hc : Nat.card (center L) = 2)
    (hQ : IsSporadic (L ⧸ center L) .Suz) : CFSG.EvenSmallLie.FoursGroupCondition L := by
  have := hperf
  obtain ⟨e⟩ := hQ
  let f : (L ⧸ center L) ≃* suzM := e.trans suzEquivM
  let q : L →* suzM := f.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerq : q.ker = center L := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, q]
    rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]
  have hfin : Finite (center L) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  have hne : center L ≠ ⊥ := fun h => by
    rw [h] at hc
    simp at hc
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht2 : orderOf (a : L) = 2 := by
    have hd : orderOf a ∣ 2 := hc ▸ orderOf_dvd_natCard a
    have h1 : orderOf a ≠ 1 := fun h1 => ha (orderOf_eq_one_iff.1 h1)
    rw [Subgroup.orderOf_coe]
    exact ((Nat.dvd_prime Nat.prime_two).1 hd).resolve_left h1
  have hcenter : center L = zpowers (a : L) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 a.2) ?_
    rw [Nat.card_zpowers, ht2, hc]
  have hker : q.ker = zpowers (a : L) := hkerq.trans hcenter
  have htt : (a : L) * (a : L) = 1 := by
    have := pow_orderOf_eq_one (a : L)
    rwa [ht2, sq] at this
  obtain ⟨x₁, hx₁, hx₁q, hw⟩ := exists_fours_witness q hq ht2 hker hcenter.ge
  exact foursGroupCondition_of_witness q hq htt hker hcenter hx₁ hx₁q hw

end Condition

end CFSG.EvenSporadicStandard.TwoSuz
