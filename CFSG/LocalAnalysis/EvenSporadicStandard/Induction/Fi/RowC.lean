module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.CoverPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InFinal

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Sporadic CFSG.Sporadic.Fi24

section Defs

@[expose] noncomputable def IsKFi24 : GroupClass := IsOddCentralExt Fi23D

theorem isKFi24_inv : GroupClass.IsoInv IsKFi24 := IsOddCentralExt.isoInv _

end Defs

section Facts

attribute [-instance] Subgroup.mul

theorem fi24inK_equiv : Nonempty (↥fi24inK ≃* Fi23D) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (sb_mem_D23 : IsConj CFSG.Sporadic.Fi23.d sb)
  have e4 : ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)) ≃*
      ↥(centralizer ({sb} : Set CFSG.Sporadic.Fi23.J)) :=
    (CFSG.Fischer.centralizerEquiv (MulAut.conj c) CFSG.Sporadic.Fi23.d).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]))
  exact ⟨((fi24inK.equivMapOfInjective jR jR_injective).trans
    ((MulEquiv.subgroupCongr fi24inK_map_jR).trans (leEquiv.symm.trans e4.symm))).trans
      fi23DEquiv.symm⟩

theorem fi24_pair_equiv {Y : Type} [Group Y] [Finite Y] (hY : IsSporadic Y .Fi24Prime) {uY : Y}
    {KY : Subgroup Y} (hu2 : orderOf uY = 2) (hKu : ∀ k ∈ KY, k * uY = uY * k)
    (hKp : ⁅KY, KY⁆ = KY) (hcard : 2 * 64561751654400 ≤ Nat.card ↥KY) :
    Nonempty (↥KY ≃* Fi23D) := by
  obtain ⟨f, -, hfK⟩ := fi24in_exists_pinned_equiv hY hu2 hKu hKp hcard
  obtain ⟨g⟩ := fi24inK_equiv
  exact ⟨(KY.equivMapOfInjective f.toMonoidHom f.injective).trans
    ((MulEquiv.subgroupCongr hfK).trans g)⟩

theorem fi24_card : Nat.card (Carrier .Fi24Prime) = 1255205709190661721292800 :=
  CFSG.Sporadic.Fi24.card_Fi24prime

theorem fi24_finite : Finite (Carrier .Fi24Prime) :=
  Nat.finite_of_card_ne_zero (by rw [fi24_card]; norm_num)

theorem fi24_simple : IsSimpleGroup (Carrier .Fi24Prime) :=
  CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime

theorem fi24_nonabelian : ∃ a b : Carrier .Fi24Prime, a * b ≠ b * a := by
  have := fi24_simple
  exact nonabelian_of_isSimpleGroup_of_not_prime (by rw [fi24_card]; norm_num)

theorem fi24_finite_even : ∀ s ∈ [TauCeti.SporadicName.Fi24Prime], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := h
  have := fi24_finite
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, fi24_card]
  decide

theorem fi24_outTwo_of_isSporadic {Y : Type} [Group Y] (h : IsSporadic Y .Fi24Prime) :
    OutTwo Y := by
  obtain ⟨e⟩ := h
  let e1 : Y ≃* ↥J := e.trans fi24EquivJ
  exact OutTwo.of_mulEquiv e1.symm fi24in_base_J.outTwo

theorem fi24_cover_pair_equiv {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi24Prime L) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    Nonempty (↥((K.subgroupOf L).map (q ↥L)) ≃* Fi23D) := by
  obtain ⟨huL, -, hu2, hKu, hKp, hcard⟩ := fi24in_data hcov hQ
  obtain ⟨e⟩ := hcov.2.2
  exact fi24_pair_equiv (Y := ↥L ⧸ center ↥L) ⟨e⟩ hu2 hKu hKp hcard

theorem fi24_rowIsK : ∀ s ∈ [TauCeti.SporadicName.Fi24Prime], ∀ (H : Type) [Group H]
    (L K : Subgroup H) (u : H), OddCover s L → fiLoc (2 * 64561751654400) H L K u →
      IsKFi24 ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  have := oddCover_finite fi24_finite hcov
  have hcov' : OddCover .Fi24Prime (⊤ : Subgroup ↥L) := oddCover_top_of_cover hcov
  have hQ' := fiLoc_restrict hQ
  obtain ⟨e⟩ := fi24_cover_pair_equiv hcov' hQ'
  have h1 : IsOddCentralExt Fi23D ↥(K.subgroupOf L) :=
    isOddCentralExt_of_cover hcov'.2.1 le_top hQ'.2.2.2.2.1 e
  exact isKFi24_inv _ _ (Subgroup.subgroupOfEquivOfLe hQ.2.2.1) h1

theorem fi24_rowExists : ∀ s ∈ [TauCeti.SporadicName.Fi24Prime], ∀ (H : Type) [Group H]
    [Finite H] (L : Subgroup H), OddCover s L →
      ∃ (K : Subgroup H) (u : H), fiLoc (2 * 64561751654400) H L K u := by
  intro s hs H _ _ L hcov
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := hcov.2.2
  let E : (↥L ⧸ center ↥L) ≃* ↥J := e.trans fi24EquivJ
  obtain ⟨g⟩ := fi24inK_equiv
  obtain ⟨f⟩ : Nonempty (↥(fi24inK.map E.symm.toMonoidHom) ≃* Fi23D) :=
    ⟨(fi24inK.equivMapOfInjective E.symm.toMonoidHom E.symm.injective).symm.trans g⟩
  have hKb : fi24inK.map E.symm.toMonoidHom ≤ centralizer ({E.symm tJ} : Set (↥L ⧸ center ↥L)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x * tJ = tJ * x :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    show E.symm x * E.symm tJ = E.symm tJ * E.symm x
    rw [← map_mul, ← map_mul, hx']
  refine exists_fiLoc_of_cover hcov.odd_center (ū := E.symm tJ)
    (by rw [← map_mul, tJ_mul_tJ, map_one])
    (fun h => tJ_ne_one (E.symm.injective (by rw [h, map_one])))
    hKb (CFSG.LocalCores.isQuasisimple_of_mulEquiv f.symm fi23D_isQuasisimple) ?_
  rw [card_quotient_oddCore_of_mulEquiv f fi23D_oddCore, fi23D_card]

theorem fi24_rowFit : ∀ s ∈ [TauCeti.SporadicName.Fi24Prime], ∀ (H : Type) [Group H] [Finite H]
    (L K : Subgroup H), OddCover s L → K ≤ L → CFSG.IsQuasisimple ↥K →
      IsKFi24 (↥K ⧸ CFSG.oddCore ↥K) → SolStd (K.subgroupOf L) →
        twoAdic (autCentralizer L K) ≤ 2 →
          ∃ u : H, fiLoc (2 * 64561751654400) H L K u := by
  intro s hs H _ _ L K hcov hKL hKq hK _ _
  exact fiLoc_of_oddCentralExt_quot fi23D_card_center
    (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple) (by rw [fi23D_card]) hKL hKq hK

theorem outTwoCovers_fi24 : OutTwoCovers [.Fi24Prime] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  exact outTwo_of_quotient hM.1.1 (fi24_outTwo_of_isSporadic hM.2.2)

theorem fi24_kNotExc (X : Type) [Group X] (hX : IsKFi24 X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  fi23_kNotExc X hX

theorem fi24_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Fi24Prime] X)
    (hY : IsKFi24 (Y ⧸ CFSG.oddCore Y)) : ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 1255205709190661721292800) fi24_finite fi24_simple
    fi24_nonabelian fi24_card (by decide) (by rw [fi23D_card_quotient]; norm_num) hX hY

theorem fi24_pair_equiv_of_center_bot {H : Type} [Group H] [Finite H] {L K : Subgroup H}
    {u : H} (hcov : OddCover .Fi24Prime L) (hZ : center ↥L = ⊥)
    (hQ : fiLoc (2 * 64561751654400) H L K u) : Nonempty (↥K ≃* Fi23D) := by
  have hinj : Function.Injective (q ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  obtain ⟨e⟩ := fi24_cover_pair_equiv hcov hQ
  exact ⟨((Subgroup.subgroupOfEquivOfLe hQ.2.2.1).symm.trans
    ((K.subgroupOf L).equivMapOfInjective (q ↥L) hinj)).trans e⟩

theorem fi23D_fixes_of_fi24 (hfix : Fi24InFixesElem) : InvolutionFixesElem Fi23D 16 := by
  have := fi24_finite
  have hcover := oddCover_top_of_simple fi24_finite fi24_simple fi24_nonabelian
  have hZ := center_top_eq_bot_of_simple fi24_simple fi24_nonabelian
  obtain ⟨K₀, u₀, hloc⟩ := fi24_rowExists .Fi24Prime (List.mem_singleton_self _)
    (Carrier .Fi24Prime) ⊤ hcover
  obtain ⟨f⟩ := fi24_pair_equiv_of_center_bot hcover hZ hloc
  exact involutionFixesElem_of_mulEquiv f (hfix (Carrier .Fi24Prime) ⊤ K₀ u₀ hcover hloc)

theorem fi23D_pRank_of_fi24 (hfix : Fi24InFixesElem) : 3 ≤ CFSG.pRank 2 Fi23D := by
  have hev : Even (Nat.card (Fi23D ⧸ center Fi23D)) := by
    rw [fi23D_card_quotient]
    exact ⟨32280875827200, by norm_num⟩
  exact three_le_pRank_of_fixesElem (X := Fi23D) (n := 16) (by norm_num) (fi23D_fixes_of_fi24 hfix)
    hev

theorem fi24_pRank_pinned (hfix : Fi24InFixesElem) : 3 ≤ CFSG.pRank 2 (Carrier .Fi24Prime) := by
  obtain ⟨g⟩ := fi24inK_equiv
  have h1 : InvolutionFixesElem ↥fi24inK 16 :=
    involutionFixesElem_of_mulEquiv g.symm (fi23D_fixes_of_fi24 hfix)
  obtain ⟨e⟩ : Nonempty ((↥fi24inK ⧸ center ↥fi24inK) ≃* (Fi23D ⧸ center Fi23D)) :=
    ⟨cqEquivOfMulEquiv g⟩
  have hev : Even (Nat.card (↥fi24inK ⧸ center ↥fi24inK)) := by
    rw [Nat.card_congr e.toEquiv, fi23D_card_quotient]
    exact ⟨32280875827200, by norm_num⟩
  have h2 : 3 ≤ CFSG.pRank 2 ↥J :=
    three_le_pRank_of_subgroup_fixes (K := fi24inK) (by norm_num) h1 hev
  let e1 : Carrier .Fi24Prime ≃* ↥J := fi24EquivJ
  rw [pRank_two_eq_of_mulEquiv' e1]
  exact h2

theorem fi24_atlasFacts (hfix : Fi24InFixesElem) :
    RowAtlasFacts [.Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)) IsKFi24 where
  pRank_K := fun X _ hX => three_le_pRank_of_oddCentralExt (fi23D_pRank_of_fi24 hfix) hX
  pRank_L := fun X _ hX => three_le_pRank_of_isLS fi24_finite
    (fun Y _ hY => by
      obtain ⟨g⟩ := hY
      rw [pRank_two_eq_of_mulEquiv' g]
      exact fi24_pRank_pinned hfix) hX
  rowExists := fi24_rowExists
  rowFit := fi24_rowFit

@[expose] noncomputable def stage3Row_fi24 (hfix : Fi24InFixesElem) :
    Stage3Row [.Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)) where
  IsK := IsKFi24
  m := fun _ => 2
  rec36 := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact Rec36.old 16 (lemma36DataQ_fi24in hfix)
  outTwo := outTwoCovers_fi24
  hyp31Row :=
    { isK_inv := isKFi24_inv
      isL_inv := IsLS.isoInv _
      quasi_K := fun X _ hX => ⟨hX.1, (fi24_atlasFacts hfix).pRank_K X hX⟩
      quasi_L := fun X _ hX => ⟨(by obtain ⟨s, hs, hq, -⟩ := hX; exact hq),
        IsLS.center_eq_oddCore fi24_finite_even hX, (fi24_atlasFacts hfix).pRank_L X hX⟩
      K_not_exc := fun X _ hX => fi24_kNotExc X hX
      K_ne_L := fun _ _ _ _ hX hY => fi24_kNeL hX hY }
  rowIsK := fi24_rowIsK
  rowExists := fi24_rowExists
  rowFit := fi24_rowFit
  inOrTwoSylow := Or.inl fun s hs H _ L K u hcov hQ => by
    rcases List.mem_singleton.1 hs with rfl
    have := oddCover_finite fi24_finite hcov
    obtain ⟨-, huK, -⟩ := (lemma36DataQ_fi24in hfix).data ↥L ⊤ (K.subgroupOf L)
      ⟨u, hQ.1⟩ (oddCover_top_of_cover hcov) (fiLoc_restrict hQ)
    exact huK

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi
