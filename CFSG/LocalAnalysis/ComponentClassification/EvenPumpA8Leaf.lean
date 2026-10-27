module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA8Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpL4Order
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpLeaf

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem card_of_alt8 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 8)) :
    Nat.card X = 20160 := by
  rw [SolMax.card_of_mulEquiv_alt (by norm_num) e]
  decide

private theorem a8PumpOutcome_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 8)) :
    A8PumpOutcome S := by
  obtain ⟨hmn, hpar⟩ := SolMax.alt_outcome_of_alternating hn θ h (by norm_num) eP
  exact Or.inl ⟨n, Nat.even_iff.mpr (by omega), hmn, ⟨θ⟩⟩

private theorem false_of_oddLie_alt8
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 8)) : False := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (L ⧸ center L) = 20160 := by
    rw [← Nat.card_congr eZ.toEquiv, card_of_alt8 eP]
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact lieModel_odd_card_ne_L34 hO hp2 hadm' hm' hcard
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega

private theorem evenLie_alt8
    (hT : CatFC.EvenOuterTypedInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 8)) :
    LieModel S .PSL 4 2 2 ∨ OddLieType S ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      Nonempty (S ≃* NativeSporadic.He) := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  have hPcard := card_of_alt8 eP
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, hPt, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · exfalso
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    rcases hU with ho | ⟨n, -, hn7, hθ⟩ | hL | hH
    · exact .inr (.inl ho)
    · exact .inr (.inr (.inl ⟨n, by omega, hθ⟩))
    · exfalso
      obtain ⟨-, h64, -⟩ :=
        PSL3Four.excludes_alternating_models_stated.{0} S (statedClassicalModel_of_lieModel_psl hL)
      have h1 : Nat.card (P ⧸ Open.fusionZStar P) ∣ Nat.card (centralizer ({t} : Set S)) :=
        (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hPt)
      rw [h64 t ht2, hPcard] at h1
      norm_num at h1
    · exact .inr (.inr (.inr hH))
  ·
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    rcases hT S τ n f hadm hm σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm', himp⟩ |
        ⟨⟨eA⟩⟩ | hU
    · obtain ⟨h1, h2, h3⟩ :=
        CatFC.eq_psl_four_one_of_lieModel_two_of_alt8 hO hadm' hm' ⟨eL.trans eP⟩
      obtain ⟨rfl, rfl, rfl⟩ := himp h1 h2
      subst h3
      exact .inl hm
    · exfalso
      have h1 := card_of_alt8 (eA.symm.trans (eL.trans eP))
      have h2 := SolMax.card_of_mulEquiv_alt (by norm_num)
        (MulEquiv.refl (alternatingGroup (Fin 6)))
      rw [h1] at h2
      revert h2
      decide
    · exfalso
      have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact lieModel_odd_card_ne_L34 hO (by norm_num) hadm3 hU
        (by rw [Nat.card_congr eL.toEquiv, hPcard])

theorem a8PumpLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hT : CatFC.EvenOuterTypedInput) (hspor : A8PumpSporadicClause) : A8PumpLeaf := by
  intro S _ _ hs hna hcat σ P h hPex ⟨eP⟩
  have : IsSimpleGroup S := hs
  have hodd : OddLieType S → False := fun ho => false_of_oddLie_alt8 hGLS hO hna ho h eP
  have hsp : NativeSporadic.SporadicRep S → A8PumpOutcome S := fun hsp =>
    hspor S hna hsp σ P h hPex ⟨eP⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | hsp'
  · exact a8PumpOutcome_of_alternating hn θ h eP
  · exact (hodd ho).elim
  · rcases evenLie_alt8 hT hO hna he h eP with hL | ho | ⟨n, hn, ⟨θ⟩⟩ | hH
    · exact .inr (.inl hL)
    · exact (hodd ho).elim
    · exact a8PumpOutcome_of_alternating hn θ h eP
    · exact hsp ⟨.He, hH⟩
  · exact hsp hsp'

end CFSG.ComponentClassification.EvenPump
