module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEven
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def IsA10Type (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 10))

theorem card_of_isA10Type {K : Type} [Group K] (h : IsA10Type K) : Nat.card K = 1814400 := by
  obtain ⟨e⟩ := h
  rw [SolMax.card_of_mulEquiv_alt (by norm_num) e]
  decide

theorem ten_le_of_properFixedComponent_alternating {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 5 ≤ n) (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (_h : ProperFixedComponent σ P) (hA : IsA10Type (P ⧸ Open.fusionZStar P)) : 10 ≤ n := by
  obtain ⟨eA⟩ := hA
  have h1 := card_dvd_of_fusionZStar_equiv eA.toEquiv
  rw [SolMax.card_of_mulEquiv_alt (by norm_num) (MulEquiv.refl _),
    SolMax.card_of_mulEquiv_alt (by omega) θ] at h1
  by_contra hlt
  have hn9 : n ≤ 9 := by omega
  interval_cases n <;> revert h1 <;> decide

theorem not_isA10Type_of_properFixedComponent_oddLie
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsA10Type (P ⧸ Open.fusionZStar P) := by
  intro hA
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (L ⧸ center L) = 1814400 := by
    rw [← Nat.card_congr eZ.toEquiv, card_of_isA10Type hA]
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact OddStandard.AltStdSec.lieModel_card_ne_alt10 hO hadm' hm' hcard
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [hcard] at hle
    norm_num at hle

theorem not_isA10Type_of_properFixedComponent_evenLie
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S)
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P) :
    ¬ IsA10Type (P ⧸ Open.fusionZStar P) ∨ TBLit.UList S := by
  have hσ1 := h.ne_one
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) hσ1
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, hPc, -⟩ := h.inner hna ht
    rcases oddCore_eq_bot_or_uList_of_evenLieType hna heven ht2 with hcore | hU
    · refine .inl fun _ => ?_
      have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore _ hPc
      exact involutionCentralizersComponentFree_of_evenLieType heven t ht2 _
        ⟨hq, hPc.choose_spec.2.1⟩
    · exact .inr hU
  ·
    refine .inl ?_
    intro hA
    obtain ⟨τ, n, f, hadm, hm⟩ := heven
    obtain ⟨eL⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe h.2.1)
    have hcard : Nat.card ((P.subgroupOf (fixedSubgroup σ)) ⧸
        Open.fusionZStar (P.subgroupOf (fixedSubgroup σ))) = 1814400 := by
      rw [Nat.card_congr eL.toEquiv, card_of_isA10Type hA]
    rcases hEO S τ n f hadm hm σ hσ2 hout _ h.2.2.1 with ⟨τ', n', f', hadm', hm'⟩ | hA6 | hU
    · exact OddStandard.AltStdSec.lieModel_card_ne_alt10 hO hadm' hm' hcard
    · obtain ⟨eA⟩ := hA6
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hcard
      norm_num [Nat.factorial] at hcard
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      exact OddStandard.AltStdSec.lieModel_card_ne_alt10 hO hadm3 hU hcard

theorem not_isA10Type_of_properFixedComponent_held
    {S : Type} [Group S] [Finite S] (eS : S ≃* NativeSporadic.He) {σ : MulAut S}
    {P : Subgroup S} (_h : ProperFixedComponent σ P) :
    ¬ IsA10Type (P ⧸ Open.fusionZStar P) := by
  intro hA
  have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  rw [card_of_isA10Type hA, Nat.card_congr eS.toEquiv, Sporadic.He.card_He] at h1
  norm_num at h1

theorem not_isA10Type_of_properFixedComponent_l34
    {S : Type} [Group S] [Finite S] (hL : GrSLit.IsL34Type S) {σ : MulAut S}
    {P : Subgroup S} (_h : ProperFixedComponent σ P) :
    ¬ IsA10Type (P ⧸ Open.fusionZStar P) := by
  intro hA
  have h1 := card_dvd_of_fusionZStar_equiv (Equiv.refl (P ⧸ Open.fusionZStar P))
  rw [card_of_isA10Type hA, card_of_isL34Type hL] at h1
  norm_num at h1

end CFSG.ComponentClassification.EvenPump
