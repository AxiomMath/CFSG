module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.KGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.CoverPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Closing
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Monster.B.Fischer CFSG.RankThree.Native.Fi22U CFSG.Sporadic.FischerOddCore

section Defs

noncomputable def Fi22D : Type := ↥fi22OuterM

noncomputable instance : Group Fi22D := inferInstanceAs (Group ↥fi22OuterM)

instance : Finite Fi22D := inferInstanceAs (Finite ↥fi22OuterM)

@[expose] noncomputable def IsKFi22 : GroupClass := IsOddCentralExt Fi22D

theorem isKFi22_inv : GroupClass.IsoInv IsKFi22 := IsOddCentralExt.isoInv _

end Defs

theorem fi22D_card : Nat.card Fi22D = 18393661440 := card_fi22OuterM

theorem fi22D_card_center : Nat.card (center Fi22D) = 2 := card_center_fi22OuterM

theorem fi22D_isQuasisimple : CFSG.IsQuasisimple Fi22D := fi22OuterM_isQuasisimple

theorem fi22D_card_quotient : Nat.card (Fi22D ⧸ center Fi22D) = 9196830720 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Fi22D)
  rw [fi22D_card, fi22D_card_center] at h
  omega

theorem fi22D_oddCore : CFSG.oddCore Fi22D = ⊥ :=
  oddCore_eq_bot_of_center_two fi22D_isQuasisimple fi22D_card_center
    (by rw [fi22D_card_quotient]; exact ⟨4598415360, by norm_num⟩)

theorem fi22D_classical : LieModel (Fi22D ⧸ center Fi22D) .PSU 6 2 1 :=
  Or.inl ⟨by simp [classicalTags], fi22CentralQuot_classicalModel⟩

theorem fi22_card : Nat.card (Carrier .Fi22) = 64561751654400 := CFSG.Sporadic.Fi22.card_Fi22

theorem fi22_finite : Finite (Carrier .Fi22) :=
  Nat.finite_of_card_ne_zero (by rw [fi22_card]; norm_num)

theorem fi22_simple : IsSimpleGroup (Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22

theorem fi22_nonabelian : ∃ a b : Carrier .Fi22, a * b ≠ b * a := by
  have := fi22_simple
  exact nonabelian_of_isSimpleGroup_of_not_prime (by rw [fi22_card]; norm_num)

theorem fi22_finite_even : ∀ s ∈ [TauCeti.SporadicName.Fi22], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := h
  have := fi22_finite
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, fi22_card]
  decide

theorem fi22_pair_equiv {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic ↥L .Fi22) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : 18393661440 ≤ Nat.card ↥K) :
    Nonempty (↥K ≃* Fi22D) := by
  obtain ⟨Φ, -, hK⟩ := exists_equiv_fi22 hL hu hu2 hKL hKu hcard
  have hmap : (K.subgroupOf L).map Φ.toMonoidHom = fi22OuterM.subgroupOf fi22P := by
    rw [← fi22_centralizer_eq_subgroupOf]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨Φ.symm y, (hK _).2 (by rwa [MulEquiv.apply_symm_apply]), by simp⟩
  let ε : ↥(K.subgroupOf L) ≃* ↥fi22OuterM :=
    (Φ.subgroupMap (K.subgroupOf L)).trans
      ((MulEquiv.subgroupCongr hmap).trans (subgroupOfEquivOfLe fi22OuterM_le_P))
  exact ⟨(Subgroup.subgroupOfEquivOfLe hKL).symm.trans ε⟩

theorem fi22_cover_pair_equiv {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi22 L) (hQ : fiLoc 18393661440 H L K u) :
    Nonempty (↥((K.subgroupOf L).map (q ↥L)) ≃* Fi22D) := by
  obtain ⟨huL, hu2, hKu, hcard⟩ := cover_pair_quotient hcov hQ
  obtain ⟨e⟩ := hcov.2.2
  have hY : IsSporadic ↥(⊤ : Subgroup (↥L ⧸ center ↥L)) .Fi22 :=
    ⟨Subgroup.topEquiv.trans e⟩
  exact fi22_pair_equiv (G := ↥L ⧸ center ↥L) (L := ⊤) (K := bar (K.subgroupOf L)) hY
    (Subgroup.mem_top _) hu2 le_top hKu hcard

theorem fi22D_fixes_of_pair {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic ↥L .Fi22) (hQ : fiLoc 18393661440 G L K u)
    (h : InvolutionFixesElem ↥K 16) : InvolutionFixesElem Fi22D 16 := by
  obtain ⟨huL, hu2, hKL, hKu, -, hsz⟩ := hQ
  have hcard : 18393661440 ≤ Nat.card ↥K :=
    hsz.trans (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)
  obtain ⟨f⟩ := fi22_pair_equiv hL huL hu2 hKL hKu hcard
  exact involutionFixesElem_of_mulEquiv f h

theorem fi22_cq_card_of_pair {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}
    (hL : IsSporadic ↥L .Fi22) (hQ : fiLoc 18393661440 G L K u) :
    Nat.card (↥K ⧸ center ↥K) = 9196830720 := by
  obtain ⟨huL, hu2, hKL, hKu, -, hsz⟩ := hQ
  have hcard : 18393661440 ≤ Nat.card ↥K :=
    hsz.trans (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective)
  obtain ⟨f⟩ := fi22_pair_equiv hL huL hu2 hKL hKu hcard
  obtain ⟨e⟩ : Nonempty ((↥K ⧸ center ↥K) ≃* (Fi22D ⧸ center Fi22D)) := ⟨cqEquivOfMulEquiv f⟩
  rw [Nat.card_congr e.toEquiv, fi22D_card_quotient]

theorem fi22_rowIsK : ∀ s ∈ [TauCeti.SporadicName.Fi22], ∀ (H : Type) [Group H]
    (L K : Subgroup H) (u : H), OddCover s L → fiLoc 18393661440 H L K u → IsKFi22 ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  have := oddCover_finite fi22_finite hcov
  have hcov' : OddCover .Fi22 (⊤ : Subgroup ↥L) := oddCover_top_of_cover hcov
  have hQ' := fiLoc_restrict hQ
  obtain ⟨e⟩ := fi22_cover_pair_equiv hcov' hQ'
  have h1 : IsOddCentralExt Fi22D ↥(K.subgroupOf L) :=
    isOddCentralExt_of_cover hcov'.2.1 le_top hQ'.2.2.2.2.1 e
  exact isKFi22_inv _ _ (Subgroup.subgroupOfEquivOfLe hQ.2.2.1) h1

theorem fi22_rowExists : ∀ s ∈ [TauCeti.SporadicName.Fi22], ∀ (H : Type) [Group H] [Finite H]
    (L : Subgroup H), OddCover s L →
      ∃ (K : Subgroup H) (u : H), fiLoc 18393661440 H L K u := by
  intro s hs H _ _ L hcov
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := hcov.2.2
  let E : (↥L ⧸ center ↥L) ≃* ↥fi22P := e.trans fi22PermEquiv
  set t₂ : ↥fi22P := ⟨fi22ExtRep 2, fi22ExtRep_two_mem⟩ with ht₂
  have ht2 : orderOf t₂ = 2 := by
    rw [ht₂, Subgroup.orderOf_mk]
    exact orderOf_fi22ExtRep (by norm_num)
  have hsq : t₂ * t₂ = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
  have hne : t₂ ≠ 1 := fun h => by
    rw [h, orderOf_one] at ht2
    omega
  obtain ⟨f⟩ : Nonempty (↥((centralizer ({t₂} : Set ↥fi22P)).map E.symm.toMonoidHom) ≃* Fi22D) :=
    ⟨((centralizer ({t₂} : Set ↥fi22P)).equivMapOfInjective E.symm.toMonoidHom
        E.symm.injective).symm.trans
      ((MulEquiv.subgroupCongr fi22_centralizer_eq_subgroupOf).trans
        (subgroupOfEquivOfLe fi22OuterM_le_P))⟩
  have hKb : (centralizer ({t₂} : Set ↥fi22P)).map E.symm.toMonoidHom ≤
      centralizer ({E.symm t₂} : Set (↥L ⧸ center ↥L)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show E.symm x * E.symm t₂ = E.symm t₂ * E.symm x
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hx]
  refine exists_fiLoc_of_cover hcov.odd_center (ū := E.symm t₂)
    (by rw [← map_mul, hsq, map_one]) (fun h => hne (E.symm.injective (by rw [h, map_one]))) hKb
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv f.symm fi22D_isQuasisimple) ?_
  rw [card_quotient_oddCore_of_mulEquiv f fi22D_oddCore, fi22D_card]

theorem fi22_rowFit : ∀ s ∈ [TauCeti.SporadicName.Fi22], ∀ (H : Type) [Group H] [Finite H]
    (L K : Subgroup H), OddCover s L → K ≤ L → CFSG.IsQuasisimple ↥K →
      IsKFi22 (↥K ⧸ CFSG.oddCore ↥K) → SolStd (K.subgroupOf L) →
        twoAdic (autCentralizer L K) ≤ 2 → ∃ u : H, fiLoc 18393661440 H L K u := by
  intro s hs H _ _ L K hcov hKL hKq hK _ _
  exact fiLoc_of_oddCentralExt_quot fi22D_card_center
    (not_isMulCommutative_of_quasisimple fi22D_isQuasisimple) (by rw [fi22D_card]) hKL hKq hK

theorem outTwoCovers_fi22 : OutTwoCovers [.Fi22] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  exact outTwo_of_quotient hM.1.1 (fi22_outTwo_of_isSporadic hM.2.2)

theorem fi22_kNotExc (X : Type) [Group X] (hX : IsKFi22 X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_oddCentralExt (c := 2639) fi22D_card_quotient (by norm_num) (by norm_num)
    (by norm_num) X hX

theorem fi22_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Fi22] X)
    (hY : IsKFi22 (Y ⧸ CFSG.oddCore Y)) : ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 64561751654400) fi22_finite fi22_simple fi22_nonabelian
    fi22_card (by decide) (by rw [fi22D_card_quotient]; norm_num) hX hY

theorem fi22_pRank_pinned (hfix : Fi22FixesElem) : 3 ≤ CFSG.pRank 2 (Carrier .Fi22) := by
  have := fi22_finite
  have hcover := oddCover_top_of_simple fi22_finite fi22_simple fi22_nonabelian
  obtain ⟨K₀, u₀, hloc⟩ := fi22_rowExists .Fi22 (List.mem_singleton_self _) (Carrier .Fi22) ⊤ hcover
  have hfixK := hfix (Carrier .Fi22) ⊤ K₀ u₀ hcover hloc
  refine three_le_pRank_of_subgroup_fixes (by norm_num) hfixK ?_
  rw [fi22_cq_card_of_pair (L := ⊤) ⟨Subgroup.topEquiv⟩ hloc]
  exact ⟨4598415360, by norm_num⟩

theorem fi22D_pRank (hfix : Fi22FixesElem) : 3 ≤ CFSG.pRank 2 Fi22D := by
  have := fi22_finite
  have hcover := oddCover_top_of_simple fi22_finite fi22_simple fi22_nonabelian
  obtain ⟨K₀, u₀, hloc⟩ := fi22_rowExists .Fi22 (List.mem_singleton_self _) (Carrier .Fi22) ⊤ hcover
  have hfixK := hfix (Carrier .Fi22) ⊤ K₀ u₀ hcover hloc
  have hfixD : InvolutionFixesElem Fi22D 16 :=
    fi22D_fixes_of_pair (L := ⊤) ⟨Subgroup.topEquiv⟩ hloc hfixK
  have hev : Even (Nat.card (Fi22D ⧸ center Fi22D)) := by
    rw [fi22D_card_quotient]
    exact ⟨4598415360, by norm_num⟩
  exact three_le_pRank_of_fixesElem (X := Fi22D) (n := 16) (by norm_num) hfixD hev

theorem fi22_atlasFacts (hfix : Fi22FixesElem) :
    RowAtlasFacts [.Fi22] (fun _ => fiLoc 18393661440) IsKFi22 where
  pRank_K := fun X _ hX => three_le_pRank_of_oddCentralExt (fi22D_pRank hfix) hX
  pRank_L := fun X _ hX => three_le_pRank_of_isLS fi22_finite
    (fun Y _ hY => by
      obtain ⟨g⟩ := hY
      rw [pRank_two_eq_of_mulEquiv' g]
      exact fi22_pRank_pinned hfix) hX
  rowExists := fi22_rowExists
  rowFit := fi22_rowFit

@[expose] noncomputable def stage3Row_fi22 (hfix : Fi22FixesElem) :
    Stage3Row [.Fi22] (fun _ => fiLoc 18393661440) where
  IsK := IsKFi22
  m := fun _ => 2
  rec36 := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact Rec36.old 16 (lemma36DataQ_fi22 hfix)
  outTwo := outTwoCovers_fi22
  hyp31Row :=
    { isK_inv := isKFi22_inv
      isL_inv := IsLS.isoInv _
      quasi_K := fun X _ hX => ⟨hX.1, (fi22_atlasFacts hfix).pRank_K X hX⟩
      quasi_L := fun X _ hX => ⟨(by obtain ⟨s, hs, hq, -⟩ := hX; exact hq),
        IsLS.center_eq_oddCore fi22_finite_even hX, (fi22_atlasFacts hfix).pRank_L X hX⟩
      K_not_exc := fun X _ hX => fi22_kNotExc X hX
      K_ne_L := fun _ _ _ _ hX hY => fi22_kNeL hX hY }
  rowIsK := fi22_rowIsK
  rowExists := fi22_rowExists
  rowFit := fi22_rowFit
  inOrTwoSylow := Or.inl fun s hs H _ L K u hcov hQ => by
    rcases List.mem_singleton.1 hs with rfl
    have := oddCover_finite fi22_finite hcov
    obtain ⟨-, huK, -⟩ := (lemma36DataQ_fi22 hfix).data ↥L ⊤ (K.subgroupOf L)
      ⟨u, hQ.1⟩ (oddCover_top_of_cover hcov) (fiLoc_restrict hQ)
    exact huK

end CFSG.EvenSporadicStandard.Induction.Fi
