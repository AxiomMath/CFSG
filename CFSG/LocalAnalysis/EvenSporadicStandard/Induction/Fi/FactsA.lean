module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.NoUp

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Monster.B.Fischer CFSG.RankThree.Native.Fi22U CFSG.Sporadic.FischerOddCore

section Facts

@[expose] def FiKnownA : GroupClass := fun X _ =>
  IsSporadic X .Fi22 ∨ IsSporadic X .Fi23 ∨ IsSporadic X .Fi24Prime ∨ IsU62 X

theorem fiKnownA_isoInv : GroupClass.IsoInv FiKnownA := fun _ _ _ _ e h =>
  h.imp (isSporadic_equiv e) fun h => h.imp (isSporadic_equiv e) fun h =>
    h.imp (isSporadic_equiv e) (isU62_isoInv _ _ e)

theorem isU62_card {X : Type} [Group X] (h : IsU62 X) : Nat.card X = 9196830720 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, fi22D_card_quotient]

theorem isU62_lieModel {X : Type} [Group X] (h : IsU62 X) : LieModel X .PSU 6 2 1 := by
  obtain ⟨e⟩ := h
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm fi22D_classical

theorem ka_cq_u62 {X : Type} [Group X] (h : IsOddCentralExt Fi22D X) : IsU62 (X ⧸ center X) :=
  oddCentralExt_cqEquiv h

theorem ka_card_cq {X : Type} [Group X] (h : IsOddCentralExt Fi22D X) :
    Nat.card (X ⧸ center X) = 9196830720 :=
  isU62_card (ka_cq_u62 h)

theorem ka_even_center {X : Type} [Group X] (h : IsOddCentralExt Fi22D X) :
    Even (Nat.card (center X)) := by
  have := oddCentralExt_finite h
  exact oddCentralExt_even_card_center (by rw [fi22D_card_center]; exact even_two) h

theorem fi22D_isK : IsOddCentralExt Fi22D Fi22D :=
  oddCentralExt_of_mulEquiv fi22D_isQuasisimple (MulEquiv.refl _)

theorem solomonLocalQ_fiLoc22 {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi22 L) (hQ : fiLoc 18393661440 H L K u) : SolomonLocalQ L K u := by
  obtain ⟨huL, hbar, hmodel⟩ := fiLoc22_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := id hQ
  exact solomonLocalQ_of_cover hcov.1 hcov.odd_center hKq huL
    (hcov.not_mem_centralizer_of_orderOf_two huL hu2) hu2 hKL hKu hmodel hbar

theorem fi22FixesElem_of_atlas (hfix : U62CoversFixesElem) : Fi22FixesElem := by
  intro H _ _ L K u hcov hQ
  have hK : IsOddCentralExt Fi22D ↥K :=
    fi22_rowIsK .Fi22 (List.mem_singleton_self _) H L K u hcov hQ
  have : Finite ↥K := oddCentralExt_finite hK
  exact hfix ↥K (oddCentralExt_perfect hK) (ka_cq_u62 hK)

theorem reachRow_fi22A (pf : FiPinned) (hyp12 : Hyp12Fi) (atl : FiAtlas) :
    Eng.ReachRow (IsOddCentralExt Fi22D) [.Fi22] [.Fi23, .Fi24Prime] [] FiKnownA where
  iso := fiKnownA_isoInv
  fi23_lo := fun s hs => absurd hs List.not_mem_nil
  K_reach := fun X _ hX => Or.inr (Or.inr (Or.inr (ka_cq_u62 hX)))
  K_quot := fun X _ hX => by
    have := oddCentralExt_finite hX
    exact oddCentralExt_quot fi22D_oddCore hX
  K_not_sporadic := fun X _ hX s hs hXs => by
    have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa using hs
    rcases hs' with rfl | rfl | rfl
    · exact not_isSporadic_of_card_ne (ka_card_cq hX) pinCard22 (by norm_num) hXs
    · exact not_isSporadic_of_card_ne (ka_card_cq hX) pinCard23 (by norm_num) hXs
    · exact not_isSporadic_of_card_ne (ka_card_cq hX) pinCard24 (by norm_num) hXs
  K_odd_lo := fun X _ _ _ s hs => absurd hs List.not_mem_nil
  lo := Or.inl fun s hs => absurd hs List.not_mem_nil
  K_iso := fun X Y _ _ hX hY hOX hOY => oddCentralExt_kIso hX hY hOX hOY
  K_cq := fun X Y _ _ hX hY => oddCentralExt_cq_cq hX hY
  not_exc := fun X _ hR => by
    rcases hR with h | h | h | h
    exacts [pinNotExc22 X h, pinNotExc23 X h, pinNotExc24 X h,
      fiNotExc_of_card (c := 2639) (isU62_card h) (by norm_num) (by norm_num) (by norm_num)]
  sp_not_exc := fun s hs => by
    have hs' : s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime := by simpa using hs
    rcases hs' with rfl | rfl | rfl
    exacts [pinNotExc22, pinNotExc23, pinNotExc24]
  rank := fun X _ _ hq hR hodd => by
    rcases hR with h | h | h | h
    · have hev22 : Even (Nat.card (X ⧸ center X)) := by
        rw [card_of_isSporadic pinCard22 h]
        exact ⟨32280875827200, by norm_num⟩
      exact three_le_pRank_of_fixesElem (by norm_num) (atl.fi22Covers X hq.1 h) hev22
    · exfalso
      have hZ := pf.mult23 X hq h
      have : Odd (Nat.card (center X)) := by
        rw [hZ, Subgroup.card_bot]
        exact odd_one
      exact hodd this ⟨.Fi23, by simp, h⟩
    · exact absurd (pf.mult24 X hq h) fun hodd' => hodd hodd' ⟨.Fi24Prime, by simp, h⟩
    · have hevU : Even (Nat.card (X ⧸ center X)) := by
        rw [isU62_card h]
        exact ⟨4598415360, by norm_num⟩
      exact three_le_pRank_of_fixesElem (by norm_num) (atl.u62Covers X hq.1 h) hevU
  up_reach := fun s hs X _ hX => by
    have hs' : s = .Fi23 ∨ s = .Fi24Prime := by simpa using hs
    rcases hs' with rfl | rfl
    exacts [Or.inr (Or.inl hX), Or.inr (Or.inr (Or.inl hX))]
  closure := fun Y _ _ hUY N' hN hidx hkp P hsol hPq hR hns _ hev => by
    rcases hR with h22 | h23 | h24 | hU
    · exact absurd ⟨.Fi22, by simp, h22⟩ hns
    · exact absurd ⟨.Fi23, by simp, h23⟩ hns
    · exact absurd ⟨.Fi24Prime, by simp, h24⟩ hns
    · by_cases hZ : Even (Nat.card ↥(center ↥P))
      ·
        exact Or.inl ((hyp12.lie Y hUY N' hN hidx hkp P hsol hPq hZ).1 (isU62_lieModel hU))
      ·
        have hodd : Odd (Nat.card ↥(center ↥P)) := Nat.not_even_iff_odd.1 hZ
        have hKEven : Eng.KEven (IsOddCentralExt Fi22D) := fun X _ hX => ka_even_center hX
        exact (atl.u62Odd Y hUY N' hN hidx hkp P hsol hPq hU hodd
          (hev hKEven Fi22D fi22D_isK hU hodd)).elim
  pair_into := fun Y _ _ _ N' hN hidx hkp P hsol hPq hR hns _ _ hN' => by
    rcases hR with h22 | h23 | h24 | hU
    · exact absurd ⟨.Fi22, by simp, h22⟩ hns
    · exact absurd ⟨.Fi23, by simp, h23⟩ hns
    · exact absurd ⟨.Fi24Prime, by simp, h24⟩ hns
    · obtain ⟨s, hs, hN'⟩ := hN'
      rcases List.mem_singleton.1 hs with rfl
      have := hN.normal
      have hPN : P ≤ N' := le_of_perfect_of_index_le_two hidx hPq.1
      obtain ⟨t, ht2, hct⟩ := hsol.exists_involution
      obtain ⟨e⟩ := atl.fi22U62 Y N' P hN.normal hN.centralizer_le hN' hPN ⟨t, ht2, hct.le⟩ hPq hU
      exact isOddCentralExt_quot_of_equiv hPq e

theorem fiKnown_fi22A : Eng.FiKnown [.Fi22] IsU62 FiKnownA :=
  ⟨fun _ _ h => h, fun X _ _ hU s hs => by
    rcases List.mem_singleton.1 hs with rfl
    rw [isU62_card hU, pinCard22]
    norm_num⟩

theorem fiRowFacts_fi22 (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) :
    Eng.FiRowFacts IsKFi22 [.Fi22] [.Fi23, .Fi24Prime] [] := by
  have hfix22 : Fi22FixesElem := fi22FixesElem_of_atlas atl.u62Covers
  refine
    { fi23 := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact Or.inl pinFi23Excl22
      reach := ⟨IsU62, FiKnownA, reachRow_fi22A pf hyp12 atl, fiKnown_fi22A⟩
      evenOut := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact hyp12.even22
      thm24 := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact Or.inr ⟨by decide, pinThm24Hex22 lo⟩
      std_row := fiStdRow_of (D := Fi22D) fi22D_card_center
        (not_isMulCommutative_of_quasisimple fi22D_isQuasisimple)
        (by have := fi22D_card; omega) (fun G _ _ L K u hcov hQ => solomonLocalQ_fiLoc22 hcov hQ)
      four_a := fiFourA_of (D := Fi22D) (s' := .Fi22) (n := 18393661440)
        (by rw [fi22D_card_center]; exact even_two) fi22D_card_center
        (not_isMulCommutative_of_quasisimple fi22D_isQuasisimple)
        (by have := fi22D_card; omega)
        (fun G _ _ L K u hcov hQ => by
          obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ := (lemma36DataQ_fi22 hfix22).data G L K u
            hcov hQ
          exact ⟨hsol, htwo⟩)
        (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
          obtain ⟨f⟩ := ka_cq_u62 hX
          exact atl.u62Covers K₂ hperf ⟨e.trans f⟩) }

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi
