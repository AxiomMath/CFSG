module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.KGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Pair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RankFacts

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

section Defs

noncomputable def Fi23D : Type :=
  ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J))

noncomputable instance : Group Fi23D :=
  inferInstanceAs (Group ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)))

instance : Finite Fi23D :=
  inferInstanceAs (Finite ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)))

noncomputable def fi23DEquiv :
    Fi23D ≃* ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)) :=
  MulEquiv.refl _

@[expose] noncomputable def IsKFi23 : GroupClass := IsOddCentralExt Fi23D

theorem isKFi23_inv : GroupClass.IsoInv IsKFi23 := IsOddCentralExt.isoInv _

end Defs

theorem fi23D_card : Nat.card Fi23D = 129123503308800 :=
  CFSG.Sporadic.Fi23.card_centralizer_d

theorem fi23D_card_center : Nat.card (center Fi23D) = 2 :=
  CFSG.Sporadic.Fi23.card_center_C

theorem fi23D_isQuasisimple : CFSG.IsQuasisimple Fi23D := isQuasisimple_centralizer_d

theorem fi23D_card_quotient : Nat.card (Fi23D ⧸ center Fi23D) = 64561751654400 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Fi23D)
  rw [fi23D_card, fi23D_card_center] at h
  omega

theorem fi23D_oddCore : CFSG.oddCore Fi23D = ⊥ :=
  oddCore_eq_bot_of_quasisimple fi23D_isQuasisimple fi23D_card_center
    (by rw [fi23D_card_quotient]; exact ⟨32280875827200, by norm_num⟩)

theorem fi23D_cq : Nonempty ((Fi23D ⧸ center Fi23D) ≃* Carrier .Fi22) :=
  ⟨CFSG.Sporadic.Fi23.quotCenterEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm⟩

theorem fi23_card : Nat.card (Carrier .Fi23) = 4089470473293004800 :=
  CFSG.Sporadic.Fi23.card_Fi23

theorem fi23_finite : Finite (Carrier .Fi23) :=
  Nat.finite_of_card_ne_zero (by rw [fi23_card]; norm_num)

theorem fi23_simple : IsSimpleGroup (Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23

theorem fi23_nonabelian : ∃ a b : Carrier .Fi23, a * b ≠ b * a := by
  have := fi23_simple
  exact nonabelian_of_isSimpleGroup_of_not_prime (by rw [fi23_card]; norm_num)

theorem fi23_finite_even : ∀ s ∈ [TauCeti.SporadicName.Fi23], ∀ (Y : Type) [Group Y],
    IsSporadic Y s → Finite Y ∧ Even (Nat.card Y) := by
  intro s hs Y _ h
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := h
  have := fi23_finite
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, fi23_card]
  decide

theorem fi23_pair_equiv {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    Nonempty (↥K ≃* Fi23D) := by
  obtain ⟨e⟩ := hL
  let ψ : ↥L ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  obtain ⟨huL, hu2, hKL, hKu, hKq, hsz⟩ := hQ
  have hX : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hle := fi23_card_inf_centralizer_le ⟨e⟩ huL hu2
  have hKcard : 129123503308800 ≤ Nat.card ↥K := by
    have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    omega
  have hKX : K = L ⊓ centralizer ({u} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hX (hle.trans hKcard)
  have hcard : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = 129123503308800 :=
    le_antisymm hle (hKcard.trans (Subgroup.card_le_of_le hX))
  have hx2 : orderOf (ψ ⟨u, huL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  have hcardJ : Nat.card ↥(centralizer ({ψ ⟨u, huL⟩} : Set CFSG.Sporadic.Fi23.J)) =
      129123503308800 := by
    rw [← @fi23_card_inf_centralizer_eq H CFSG.Sporadic.Fi23.J _ (inferInstance) L ψ u huL]
    exact hcard
  have hconj := fi23J_isConj_d_of_card hx2 hcardJ
  obtain ⟨e1⟩ := @nonempty_inf_centralizer_mulEquiv H CFSG.Sporadic.Fi23.J _ (inferInstance) L ψ u
    huL
  obtain ⟨c, hcx⟩ := isConj_iff.1 hconj
  have e2 : ↥(centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J)) ≃*
      ↥(centralizer ({ψ ⟨u, huL⟩} : Set CFSG.Sporadic.Fi23.J)) :=
    (CFSG.Fischer.centralizerEquiv (MulAut.conj c) CFSG.Sporadic.Fi23.d).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hcx]))
  exact ⟨(MulEquiv.subgroupCongr hKX).trans (e1.trans e2.symm)⟩

theorem fi23_rowIsK (hmult : OddMultTrivial .Fi23) : ∀ s ∈ [TauCeti.SporadicName.Fi23],
    ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L →
      fiLoc (2 * 64561751654400) H L K u → IsKFi23 ↥K := by
  intro s hs H _ L K u hcov hQ
  rcases List.mem_singleton.1 hs with rfl
  have hL := oddCover_isSporadic fi23_finite hmult hcov
  have := oddCover_finite fi23_finite hcov
  obtain ⟨hL'⟩ := hL
  obtain ⟨f⟩ := fi23_pair_equiv (H := ↥L) (L := ⊤) ⟨Subgroup.topEquiv.trans hL'⟩
    (fiLoc_restrict hQ)
  exact oddCentralExt_of_mulEquiv hQ.2.2.2.2.1
    ((Subgroup.subgroupOfEquivOfLe hQ.2.2.1).symm.trans f)

theorem fi23_rowExists (hmult : OddMultTrivial .Fi23) : ∀ s ∈ [TauCeti.SporadicName.Fi23],
    ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H), OddCover s L →
      ∃ (K : Subgroup H) (u : H), fiLoc (2 * 64561751654400) H L K u := by
  intro s hs H _ _ L hcov
  rcases List.mem_singleton.1 hs with rfl
  have hL := oddCover_isSporadic fi23_finite hmult hcov
  obtain ⟨K₀, u₀, -, -, -, hloc⟩ := exists_fiLoc_pair_of_isSporadic_fi23 hL (le_refl L)
  exact ⟨K₀, u₀, hloc⟩

theorem fi23_rowFit : ∀ s ∈ [TauCeti.SporadicName.Fi23], ∀ (H : Type) [Group H] [Finite H]
    (L K : Subgroup H), OddCover s L → K ≤ L → CFSG.IsQuasisimple ↥K →
      IsKFi23 (↥K ⧸ CFSG.oddCore ↥K) → SolStd (K.subgroupOf L) →
        twoAdic (autCentralizer L K) ≤ 2 → ∃ u : H, fiLoc (2 * 64561751654400) H L K u := by
  intro s hs H _ _ L K hcov hKL hKq hK _ _
  exact fiLoc_of_oddCentralExt_quot fi23D_card_center
    (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple) (by rw [fi23D_card]) hKL hKq hK

theorem outTwoCovers_fi23 (hmult : OddMultTrivial .Fi23) : OutTwoCovers [.Fi23] := by
  intro s hs H _ M hM
  rcases List.mem_singleton.1 hs with rfl
  obtain ⟨e⟩ := oddCover_isSporadic fi23_finite hmult hM
  have hinn : AllInner ↥M :=
    AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  intro α β
  exact Or.inl (hinn α)

theorem fi23_kNotExc (X : Type) [Group X] (hX : IsKFi23 X) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f :=
  kNotExc_of_oddCentralExt (c := 50543) fi23D_card_quotient (by norm_num) (by norm_num)
    (by norm_num) X hX

theorem fi23_kNeL {X Y : Type} [Group X] [Group Y] (hX : IsLS [.Fi23] X)
    (hY : IsKFi23 (Y ⧸ CFSG.oddCore Y)) :
    ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) :=
  kNeL_of_oddCentralExt (cardS := 4089470473293004800) fi23_finite fi23_simple fi23_nonabelian
    fi23_card (by decide) (by rw [fi23D_card_quotient]; norm_num) hX hY

theorem fi23D_fixes_of_pair {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hQ : fiLoc (2 * 64561751654400) H L K u)
    (h : InvolutionFixesElem ↥K 16) : InvolutionFixesElem Fi23D 16 := by
  obtain ⟨f⟩ := fi23_pair_equiv hL hQ
  exact involutionFixesElem_of_mulEquiv f h

theorem fi23_cq_card_of_pair {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    Nat.card (↥K ⧸ center ↥K) = 64561751654400 := by
  obtain ⟨f⟩ := fi23_pair_equiv hL hQ
  obtain ⟨e⟩ : Nonempty ((↥K ⧸ center ↥K) ≃* (Fi23D ⧸ center Fi23D)) := ⟨cqEquivOfMulEquiv f⟩
  rw [Nat.card_congr e.toEquiv, fi23D_card_quotient]

theorem fi23_pinned_pair :
    ∃ (K₀ : Subgroup (Carrier .Fi23)) (u₀ : Carrier .Fi23),
      fiLoc (2 * 64561751654400) (Carrier .Fi23) ⊤ K₀ u₀ := by
  have := fi23_finite
  obtain ⟨K₀, u₀, -, -, -, hloc⟩ := exists_fiLoc_pair_of_isSporadic_fi23 (H := Carrier .Fi23)
    (K := ⊤) (L := ⊤) ⟨Subgroup.topEquiv⟩ le_rfl
  exact ⟨K₀, u₀, hloc⟩

theorem fi23_pRank_pinned (hfix : Fi23FixesElem) : 3 ≤ CFSG.pRank 2 (Carrier .Fi23) := by
  have := fi23_finite
  obtain ⟨K₀, u₀, hloc⟩ := fi23_pinned_pair
  have hfixK := hfix (Carrier .Fi23) ⊤ K₀ u₀
    (oddCover_top_of_simple fi23_finite fi23_simple fi23_nonabelian) hloc
  refine three_le_pRank_of_subgroup_fixes (by norm_num) hfixK ?_
  rw [fi23_cq_card_of_pair (L := ⊤) ⟨Subgroup.topEquiv⟩ hloc]
  exact ⟨32280875827200, by norm_num⟩

theorem fi23D_pRank (hfix : Fi23FixesElem) : 3 ≤ CFSG.pRank 2 Fi23D := by
  have := fi23_finite
  obtain ⟨K₀, u₀, hloc⟩ := fi23_pinned_pair
  have hfixK := hfix (Carrier .Fi23) ⊤ K₀ u₀
    (oddCover_top_of_simple fi23_finite fi23_simple fi23_nonabelian) hloc
  have hfixD : InvolutionFixesElem Fi23D 16 :=
    fi23D_fixes_of_pair (L := ⊤) ⟨Subgroup.topEquiv⟩ hloc hfixK
  have hev : Even (Nat.card (Fi23D ⧸ center Fi23D)) := by
    rw [fi23D_card_quotient]
    exact ⟨32280875827200, by norm_num⟩
  exact three_le_pRank_of_fixesElem (X := Fi23D) (n := 16) (by norm_num) hfixD hev

theorem fi23_atlasFacts (hmult : OddMultTrivial .Fi23) (hfix : Fi23FixesElem) :
    RowAtlasFacts [.Fi23] (fun _ => fiLoc (2 * 64561751654400)) IsKFi23 where
  pRank_K := fun X _ hX => three_le_pRank_of_oddCentralExt (fi23D_pRank hfix) hX
  pRank_L := fun X _ hX => three_le_pRank_of_isLS fi23_finite
    (fun Y _ hY => by
      obtain ⟨g⟩ := hY
      rw [pRank_two_eq_of_mulEquiv' g]
      exact fi23_pRank_pinned hfix) hX
  rowExists := fi23_rowExists hmult
  rowFit := fi23_rowFit

@[expose] noncomputable def stage3Row_fi23 (hmult : OddMultTrivial .Fi23) (hfix : Fi23FixesElem) :
    Stage3Row [.Fi23] (fun _ => fiLoc (2 * 64561751654400)) where
  IsK := IsKFi23
  m := fun _ => 2
  rec36 := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact Rec36.old 16 (lemma36DataQ_fi23 hmult hfix)
  outTwo := outTwoCovers_fi23 hmult
  hyp31Row :=
    { isK_inv := isKFi23_inv
      isL_inv := IsLS.isoInv _
      quasi_K := fun X _ hX => ⟨hX.1, (fi23_atlasFacts hmult hfix).pRank_K X hX⟩
      quasi_L := fun X _ hX => ⟨(by obtain ⟨s, hs, hq, -⟩ := hX; exact hq),
        IsLS.center_eq_oddCore fi23_finite_even hX,
        (fi23_atlasFacts hmult hfix).pRank_L X hX⟩
      K_not_exc := fun X _ hX => fi23_kNotExc X hX
      K_ne_L := fun _ _ _ _ hX hY => fi23_kNeL hX hY }
  rowIsK := fi23_rowIsK hmult
  rowExists := fi23_rowExists hmult
  rowFit := fi23_rowFit
  inOrTwoSylow := Or.inl fun s hs H _ L K u hcov hQ => by
    rcases List.mem_singleton.1 hs with rfl
    have := oddCover_finite fi23_finite hcov
    obtain ⟨-, huK, -⟩ := (lemma36DataQ_fi23 hmult hfix).data ↥L ⊤ (K.subgroupOf L)
      ⟨u, hQ.1⟩ (oddCover_top_of_cover hcov) (fiLoc_restrict hQ)
    exact huK

end CFSG.EvenSporadicStandard.Induction.Fi
