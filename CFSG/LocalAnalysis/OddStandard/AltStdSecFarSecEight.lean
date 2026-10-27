module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEight
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEightLinear

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.CatLeaf

section Gen

theorem le_of_isSimpleGroup_of_index_lt {X : Type*} [Group X] [Finite X] {W L : Subgroup X}
    [W.Normal] (hL : IsSimpleGroup L) (hlt : W.index < Nat.card L) : L ≤ W := by
  have := hL
  set f : L →* X ⧸ W := (QuotientGroup.mk' W).comp L.subtype with hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h
    have h1 := Nat.card_le_card_of_injective f hinj
    have h2 : Nat.card (X ⧸ W) = W.index := rfl
    omega
  · intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ f.ker := h ▸ mem_top _
    exact (QuotientGroup.eq_one_iff _).1 h1

theorem exists_orderOf_eight_alternating_ten : ∃ g : alternatingGroup (Fin 10), orderOf g = 8 := by
  set σ : Perm (Fin 10) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6 *
    swap 6 7 * swap 8 9 with hσ
  have hA : σ ∈ alternatingGroup (Fin 10) := by
    rw [mem_alternatingGroup]
    decide +kernel
  refine ⟨⟨σ, hA⟩, ?_⟩
  rw [Subgroup.orderOf_mk]
  have h1 : orderOf σ = 2 ^ (2 + 1) := orderOf_eq_prime_pow (by decide +kernel) (by decide +kernel)
  rw [h1]
  norm_num

end Gen

section Eleven

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

noncomputable def secLqEquiv (hm : 6 ≤ m) :
    ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) ≃*
      alternatingGroup (Fin (m - 1)) := by
  refine (ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective _ _ ?_).symm.trans
    (secLEquiv O hR)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro b hb
  have hb1 : QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))) (b : secQ (secP O R)) = 1 := hb
  have : (b : secQ (secP O R)) ∈ secL O hR ⊓ CFSG.oddCore (secQ (secP O R)) :=
    Subgroup.mem_inf.2 ⟨b.2, (QuotientGroup.eq_one_iff _).1 hb1⟩
  rw [secL_inf_oddCore O hR hm] at this
  exact Subtype.ext this

theorem false_of_l44Outcome (hm : m = 11)
    (h : L44Outcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))) :
    False := by
  subst hm
  obtain ⟨W, hWN, hCW, -, hLie⟩ := h
  have := hWN
  obtain ⟨K, _iK, _fK, hK, ⟨eW⟩⟩ := exists_projectiveSL_of_lieModel_four hLie
  have hout : Nat.card (Outer W) ∣ 4 := by
    rw [Nat.card_congr (equivalence eW).toEquiv]
    exact card_outer_dvd_four hK
  have hidx : W.index ≤ 4 :=
    (index_le_card_outer W hCW).trans (Nat.le_of_dvd (by norm_num) hout)
  set eL := secLqEquiv O hR (by norm_num) with heL
  have hsimple : IsSimpleGroup
      ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) :=
    isSimpleGroup_of_alt (by norm_num) eL
  have hL : Nat.card ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) =
      1814400 := by
    rw [card_eq_of_equiv_alt (by norm_num) eL]
    decide
  have hLW := le_of_isSimpleGroup_of_index_lt (W := W) hsimple (by omega)
  obtain ⟨g, hg⟩ := exists_orderOf_eight_alternating_ten
  set l := eL.symm g with hl
  have hl8 : orderOf l = 8 := by rw [hl, MulEquiv.orderOf_eq]; exact hg
  have hw8 :
      orderOf (eW ⟨(l : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))), hLW l.2⟩) = 8 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hl8
  exact orderOf_ne_eight_of_card_four hK _ hw8


theorem false_of_hsOutcome (hm : m = 11)
    (h : HSOutcome
      (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))) :
    False := by
  subst hm
  obtain ⟨W, hWN, hCW, -, ⟨eW⟩⟩ := h
  have := hWN
  have hout : Nat.card (Outer W) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      (eW.trans CFSG.Sporadic.Schreier.hsPermEquiv)
  have hidx : W.index ≤ 2 := (index_le_card_outer W hCW).trans hout
  have hW : Nat.card W = 44352000 := (Nat.card_congr eW.toEquiv).trans CFSG.Sporadic.HS.card_HS
  have hL : Nat.card ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) =
      1814400 := by
    rw [card_eq_of_equiv_alt (by norm_num) (secLqEquiv O hR (by norm_num))]
    decide
  have hdvd := card_subgroup_dvd_card
    ((secL O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R)))))
  rw [hL, ← W.card_mul_index, hW] at hdvd
  have h0 : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨k, hk⟩ : ∃ k, W.index = k := ⟨_, rfl⟩
  rw [hk] at hdvd hidx h0
  interval_cases k <;> omega

end Eleven

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)


theorem conj_mem_secL_eleven (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hm : m = 11) (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G)))
    (g : secQ (secP O R)) {x : secQ (secP O R)} (hx : x ∈ secL O hR) :
    g * x * g⁻¹ ∈ secL O hR := by
  subst hm
  have hKX : CFSG.SectionRank.IsKGroupCat (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) :=
    (hK.quotient _).quotient _
  have hOX : CFSG.oddCore (secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R))) = ⊥ :=
    ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _
  have hsh := exactShape_secQ O hR (by norm_num)
  rcases section_dichotomy hOX hsh (by norm_num) with h1 | h2 | h3
  · exact absurd h1 (secT_notMem_center O hR (by norm_num))
  · exact absurd h2 (not_wreath_of_order O hR (by norm_num))
  · rcases exactShape_almostSimple_eight hGLS hO hKX hOX hsh h3 with h4 | h5 | h6
    · exact conj_mem_secL_of_normal O hR (by norm_num) (normal_of_sym O hR (by norm_num) h4) g hx
    · exact (false_of_hsOutcome O hR rfl h5).elim
    · exact (false_of_l44Outcome O hR rfl h6).elim

include hR in
theorem l0Normal_eleven (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hm : m = 11) (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer (secP O R : Set G))) :
    L0Normal O R :=
  l0Normal_of_secL O hR (conj_mem_secL_eleven O hR hGLS hO hm hK) (by omega)

end Main


theorem shapeTwoCentDoubleAt_twelve (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hR2 : RankTwoAlternatingStandard) : ShapeTwoCentDoubleAt 12 := by
  refine centDoubleAt_of_l0 hR2 (m := 11) (by norm_num) ?_
  intro G _ _ z O h4 hK hne
  obtain ⟨hKE, hKy⟩ := isKGroupCat_secP O h4 hK hne
  exact ⟨l0Normal_eleven O (secR_klein (by norm_num)) hGLS hO rfl hKE,
    l0Normal_eleven O (secR_cyc (by norm_num)) hGLS hO rfl hKy⟩

end CFSG.OddStandard.AltStdSec
