module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuReachRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzEightModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem invFixesNotLam_of_szEightModel (hSz : SzEightModel) {K : Type} [Group K] [Finite K]
    (hK : SuzukiModel K 2 3) (b : ℕ) : InvolutionFixesNotLam K b := by
  intro α hα1 hα2
  have hnot := (hSz K hK).2 α hα1 hα2
  refine ⟨fun hL => hnot ?_, fun _ hL => hnot hL.2.1⟩
  exact hL.2.1.of_injective (f := MonoidHom.inl _ _) (inl_injective' _ _)

section LocalQ

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem ruLemma36_data' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel)
    (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    orderOf u = 2 ∧ u ∈ L ∧ u ∉ K ∧ K ≤ L ⊓ centralizer ({u} : Set H) ∧
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic ∧
      CFSG.IsQuasisimple ↥K ∧ Group.IsSolvable ↥(autCentralizer L K) ∧
      twoAdic (autCentralizer L K) ≤ 2 ∧ ElemBound 4 ↥(autCentralizer L K) ∧
      (∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) ∧
      InvolutionFixesNotLam ↥K (2 * 4) :=
  ⟨hQ.2.1, hQ.1, ruPair_not_mem hf hL hQ, fun k hk =>
    ⟨hQ.2.2.1 hk, mem_centralizer_singleton_iff.2 (hQ.2.2.2.1 k hk)⟩,
    ruPair_characteristic hf hL hQ, ruPair_isQuasisimple hf hL hQ, ruAut_solvable hf hL hQ,
    ruPair_twoAdic_aut hf hL hQ, ruAut_elemBound hf hL hQ, ruAut_inner hL,
    invFixesNotLam_of_szEightModel hSz (hS H L K u hL hQ) _⟩

end LocalQ

section Row


section Opaque

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem ruK_quasi' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel) {X : Type}
    [Group X] (h : IsKPinned .Ru (fun n => n = 29120) X) :
    CFSG.IsQuasisimple X ∧ 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨u, K, hQ, ⟨e⟩⟩ := ruPinned_of_isK h
  have := ru_finite
  have hKq := ruPinned_quasisimple hf hQ
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hKq,
    three_le_pRank_of_szEight e (hSz ↥K (hS (Carrier .Ru) ⊤ K u ru_top_sporadic hQ)).1⟩

theorem ruL_quasi' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel)
    (hmult : OddMultTrivial .Ru) {X : Type} [Group X] (hX : IsLS [.Ru] X) :
    CFSG.IsQuasisimple X ∧ center X = CFSG.oddCore X ∧ 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨s', hs', hq, hodd, hsp⟩ := hX
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨f⟩ := hsp
  have := ru_finite
  have : Finite (center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have : Finite (X ⧸ center X) := Finite.of_equiv _ f.symm.toEquiv
  have : Finite X := Finite.of_subgroup_quotient (center X)
  have hc : center X = ⊥ := hmult X hq hodd ⟨f⟩
  obtain ⟨e⟩ := isSporadic_of_center_eq_bot hc ⟨f⟩
  have := ru_isSimpleGroup
  have hev : Even (Nat.card (Carrier .Ru)) := by rw [card_carrier_ru]; decide
  have hbot : CFSG.oddCore X = ⊥ :=
    oddCore_eq_bot_of_mulEquiv e.symm (oddCore_eq_bot_of_isSimpleGroup hev)
  obtain ⟨K, u, hQ⟩ := hf.exists_pair (Carrier .Ru) ⊤ ru_top_sporadic
  obtain ⟨E, hsq, hcE, hcard⟩ := (hSz ↥K (hS (Carrier .Ru) ⊤ K u ru_top_sporadic hQ)).1
  refine ⟨hq, by rw [hc, hbot], ?_⟩
  refine three_le_pRank_of_elemAbelian ((E.map K.subtype).map e.symm.toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show e.symm (y : Carrier .Ru) * e.symm (y : Carrier .Ru) = 1
    rw [← map_mul]
    have h1 : (y : Carrier .Ru) * (y : Carrier .Ru) = 1 := congrArg Subtype.val (hsq y hy)
    rw [h1, map_one]
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    show e.symm (y : Carrier .Ru) * e.symm (z : Carrier .Ru) =
      e.symm (z : Carrier .Ru) * e.symm (y : Carrier .Ru)
    rw [← map_mul, ← map_mul]
    have h1 : (y : Carrier .Ru) * (z : Carrier .Ru) = (z : Carrier .Ru) * (y : Carrier .Ru) :=
      congrArg Subtype.val (hcE y hy z hz)
    rw [h1]
  · rw [Subgroup.card_map_of_injective e.symm.injective,
      Subgroup.card_map_of_injective K.subtype_injective, hcard]

theorem ruHyp31Row' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel)
    (hmult : OddMultTrivial .Ru) :
    Hyp31Row (IsKPinned .Ru (fun n => n = 29120)) (IsLS [.Ru]) where
  isK_inv := isKPinned_isoInv .Ru _
  isL_inv := fun _ _ _ _ e h => isLS_of_mulEquiv e h
  quasi_K := fun _ _ h => ruK_quasi' hf hS hSz h
  quasi_L := fun _ _ h => ruL_quasi' hf hS hSz hmult h
  K_not_exc := fun _ _ h => ruK_not_exc hf h
  K_ne_L := fun _ _ _ _ hX hY => ruK_ne_L hX hY

theorem ruLemma36ruDataQ' (hf : RuLocalFacts) (hS : RuSuzukiModel) (hSz : SzEightModel)
    (hmult : OddMultTrivial .Ru) (hno : RuNoOtherHered) :
    Lemma36ruDataQ [.Ru] .Ru RuPair 2 4 where
  m_le := le_refl 2
  data := fun _ _ _ _ _ _ hcov hQ =>
    ruLemma36_data' hf hS hSz (hcov.isSporadic_of_mult hmult) hQ
  noOther := hno

@[expose] noncomputable def stage3Row_ru' (hf : RuLocalFacts) (hS : RuSuzukiModel)
    (hSz : SzEightModel) (hmult : OddMultTrivial .Ru) (hno : RuNoOtherHered)
    (hTwo : TwoSylowStd [.Ru]) : Stage3Row [.Ru] (fun _ => RuPair) where
  IsK := IsKPinned .Ru (fun n => n = 29120)
  m := fun _ => 2
  rec36 := fun s' hs' => by
    rcases List.mem_singleton.1 hs' with rfl
    exact Rec36.ru 4 (ruLemma36ruDataQ' hf hS hSz hmult hno)
  outTwo := outTwoCovers_ru hmult
  hyp31Row := ruHyp31Row' hf hS hSz hmult
  rowIsK := fun s' hs' H _ L K u hcov hQ => by
    rcases List.mem_singleton.1 hs' with rfl
    obtain ⟨e⟩ := oddCover_isSporadic ru_finite hmult hcov
    exact isKPinned_of_pair e hQ
  rowExists := fun s' hs' H _ _ L hcov => by
    rcases List.mem_singleton.1 hs' with rfl
    exact hf.exists_pair H L (oddCover_isSporadic ru_finite hmult hcov)
  rowFit := fun s' hs' H _ _ L K hcov hKL _ hK hstd _ => by
    rcases List.mem_singleton.1 hs' with rfl
    exact ru_fit hmult hcov hKL hK hstd
  inOrTwoSylow := Or.inr hTwo

end Opaque

end Row

end CFSG.EvenSporadicStandard.Induction
