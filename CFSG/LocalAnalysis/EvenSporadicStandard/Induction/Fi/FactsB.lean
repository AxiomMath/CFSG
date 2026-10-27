module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.NoUp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Even

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

section Facts


@[expose] def FiKnown3 : GroupClass := fun X _ =>
  IsSporadic X .Fi22 ∨ IsSporadic X .Fi23 ∨ IsSporadic X .Fi24Prime

theorem fiKnown3_isoInv : GroupClass.IsoInv FiKnown3 := fun _ _ _ _ e h =>
  h.imp (isSporadic_equiv e) fun h => h.imp (isSporadic_equiv e) (isSporadic_equiv e)

theorem k3_cq_fi22 {X : Type} [Group X] (h : IsOddCentralExt Fi23D X) :
    IsSporadic (X ⧸ center X) .Fi22 := by
  obtain ⟨e⟩ := oddCentralExt_cqEquiv h
  obtain ⟨f⟩ := fi23D_cq
  exact ⟨e.trans f⟩

theorem k3_card_cq {X : Type} [Group X] (h : IsOddCentralExt Fi23D X) :
    Nat.card (X ⧸ center X) = 64561751654400 :=
  h.card_quotient.trans fi23D_card_quotient

theorem k3_even_center {X : Type} [Group X] (h : IsOddCentralExt Fi23D X) :
    Even (Nat.card (center X)) := by
  have := oddCentralExt_finite h
  exact oddCentralExt_even_card_center (by rw [fi23D_card_center]; exact even_two) h

theorem reachRow_fi22K (pf : FiPinned) (hyp12 : Hyp12Fi)
    (hfix : Fi22CoversFixesElem) (hev : Fi22EvenCover) (S Up : List TauCeti.SporadicName)
    (hSU : ∀ s ∈ S ++ Up, s = .Fi23 ∨ s = .Fi24Prime)
    (h23 : TauCeti.SporadicName.Fi23 ∈ S ++ Up) (h24 : TauCeti.SporadicName.Fi24Prime ∈ S ++ Up) :
    Eng.ReachRow (IsOddCentralExt Fi23D) S Up [.Fi22] FiKnown3 where
  iso := fiKnown3_isoInv
  fi23_lo := fun s hs => by
    rcases List.mem_singleton.1 hs with rfl
    exact pinFi23Excl22
  K_reach := fun X _ hX => Or.inl (k3_cq_fi22 hX)
  K_quot := fun X _ hX => by
    have := oddCentralExt_finite hX
    exact oddCentralExt_quot fi23D_oddCore hX
  K_not_sporadic := fun X _ hX s hs hXs => by
    rcases hSU s hs with rfl | rfl
    · exact not_isSporadic_of_card_ne (k3_card_cq hX) pinCard23 (by norm_num) hXs
    · exact not_isSporadic_of_card_ne (k3_card_cq hX) pinCard24 (by norm_num) hXs
  K_odd_lo := fun X _ hX hodd _ _ => absurd hodd (Nat.not_odd_iff_even.2 (k3_even_center hX))
  lo := Or.inl fun s hs X Y _ _ hX hY => by
    rcases List.mem_singleton.1 hs with rfl
    obtain ⟨e⟩ := hX
    obtain ⟨f⟩ := k3_cq_fi22 hY
    exact ⟨e.trans f.symm⟩
  K_iso := fun X Y _ _ hX hY hOX hOY => oddCentralExt_kIso hX hY hOX hOY
  K_cq := fun X Y _ _ hX hY => oddCentralExt_cq_cq hX hY
  not_exc := fun X _ hR => by
    rcases hR with h | h | h
    exacts [pinNotExc22 X h, pinNotExc23 X h, pinNotExc24 X h]
  sp_not_exc := fun s hs => by
    rcases hSU s hs with rfl | rfl
    exacts [pinNotExc23, pinNotExc24]
  rank := fun X _ _ hq hR hodd => by
    rcases hR with h | h | h
    · have hev22 : Even (Nat.card (X ⧸ center X)) := by
        rw [card_of_isSporadic pinCard22 h]
        exact ⟨32280875827200, by norm_num⟩
      exact three_le_pRank_of_fixesElem (by norm_num) (hfix X hq.1 h) hev22
    · exfalso
      have hZ := pf.mult23 X hq h
      have : Odd (Nat.card (center X)) := by
        rw [hZ, Subgroup.card_bot]
        exact odd_one
      exact hodd this ⟨.Fi23, h23, h⟩
    · exact absurd (pf.mult24 X hq h) fun hodd' => hodd hodd' ⟨.Fi24Prime, h24, h⟩
  up_reach := fun s hs X _ hX => by
    rcases hSU s (List.mem_append_right S hs) with rfl | rfl
    exacts [Or.inr (Or.inl hX), Or.inr (Or.inr hX)]
  closure := fun Y _ _ hY N' hN hidx hkp P hsol hPq hR hns hlo _ => by
    rcases hR with h22 | h23' | h24'
    · have hZ : ¬ Odd (Nat.card ↥(center ↥P)) := fun hodd =>
        hlo hodd ⟨.Fi22, List.mem_singleton_self _, h22⟩
      obtain ⟨s'', hs'', hN'⟩ := hyp12.even22 Y hY N' hN hidx hkp P hsol hPq h22 hZ
      rcases List.mem_cons.1 hs'' with rfl | hs''
      · exact Or.inr (Or.inl hN')
      · rcases List.mem_singleton.1 hs'' with rfl
        exact Or.inr (Or.inr hN')
    · exact absurd ⟨.Fi23, h23, h23'⟩ hns
    · exact absurd ⟨.Fi24Prime, h24, h24'⟩ hns
  pair_into := fun Y _ _ _ N' hN hidx hkp P hsol hPq hR hns hlo _ _ => by
    rcases hR with h22 | h23' | h24'
    · have hZ : Even (Nat.card ↥(center ↥P)) := Nat.not_odd_iff_even.1 fun hodd =>
        hlo hodd ⟨.Fi22, List.mem_singleton_self _, h22⟩
      obtain ⟨e⟩ := hev ↥P hPq h22 hZ
      exact isOddCentralExt_quot_of_equiv hPq e
    · exact absurd ⟨.Fi23, h23, h23'⟩ hns
    · exact absurd ⟨.Fi24Prime, h24, h24'⟩ hns

theorem fiKnown_fi22K (S : List TauCeti.SporadicName) :
    Eng.FiKnown S (fun _ _ => False) FiKnown3 :=
  ⟨fun _ _ h => h.imp id fun h => h.imp id Or.inl, fun _ _ _ h => h.elim⟩

theorem reach_fi22K (pf : FiPinned) (hyp12 : Hyp12Fi)
    (hfix : Fi22CoversFixesElem) (hev : Fi22EvenCover) (S Up : List TauCeti.SporadicName)
    (hSU : ∀ s ∈ S ++ Up, s = .Fi23 ∨ s = .Fi24Prime)
    (h23 : TauCeti.SporadicName.Fi23 ∈ S ++ Up) (h24 : TauCeti.SporadicName.Fi24Prime ∈ S ++ Up) :
    ∃ U R : GroupClass, Eng.ReachRow (IsOddCentralExt Fi23D) S Up [.Fi22] R ∧ Eng.FiKnown S U R :=
  ⟨fun _ _ => False, FiKnown3, reachRow_fi22K pf hyp12 hfix hev S Up hSU h23 h24,
    fiKnown_fi22K S⟩

theorem fi23_pair_eq (hmult : OddMultTrivial .Fi23) {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hcov : OddCover .Fi23 L)
    (hQ : fiLoc (2 * 64561751654400) H L K u) :
    K = L ⊓ centralizer ({u} : Set H) ∧ u ∈ K ∧ Nat.card (center ↥K) = 2 := by
  have hL := oddCover_isSporadic fi23_finite hmult hcov
  obtain ⟨huL, hu2, hKL, hKu, -, hsz⟩ := hQ
  have hX : K ≤ L ⊓ centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hle := fi23_card_inf_centralizer_le hL huL hu2
  have hKcard : 129123503308800 ≤ Nat.card ↥K := by
    have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    omega
  have hKX : K = L ⊓ centralizer ({u} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hX (hle.trans hKcard)
  have hcard : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = 129123503308800 :=
    le_antisymm hle (hKcard.trans (Subgroup.card_le_of_le hX))
  have hZ := fi23_card_center_inf_centralizer hL huL hu2 hcard
  refine ⟨hKX, ?_, by rw [hKX]; exact hZ⟩
  rw [hKX]
  exact ⟨huL, mem_centralizer_singleton_iff.2 rfl⟩

theorem solomonLocalQ_fi23 (hmult : OddMultTrivial .Fi23) {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hcov : OddCover .Fi23 L)
    (hQ : fiLoc (2 * 64561751654400) H L K u) : SolomonLocalQ L K u := by
  obtain ⟨hKX, huK, hZK⟩ := fi23_pair_eq hmult hcov hQ
  obtain ⟨huL, hu2, hKL, hKu, hKq, -⟩ := id hQ
  have hL := oddCover_isSporadic fi23_finite hmult hcov
  have hu'2 : orderOf (⟨u, huL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu2
  have hK' : K.subgroupOf L = centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hx' : (x : H) ∈ L ⊓ centralizer ({u} : Set H) := hKX ▸ hx
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hx'.2)
    · intro h
      rw [hKX]
      exact ⟨x.2, mem_centralizer_singleton_iff.2 (congrArg Subtype.val h)⟩
  have hqK' : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hKq
  have hZ' : Nat.card (center ↥(K.subgroupOf L)) = 2 := by
    rw [card_center_congr (Subgroup.subgroupOfEquivOfLe hKL)]
    exact hZK
  have hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l := by
    obtain ⟨e⟩ := hL
    exact AllInner.of_mulEquiv e.symm CFSG.Sporadic.FischerOddCore.fi23_mulAut_eq_conj
  have hC : Nat.card (autCentralizer L K) ≤ 4 :=
    (card_autCentralizer_le_of_allInner hinn huK hKX).trans (by rw [hZK]; norm_num)
  exact
    { u_order := hu2
      u_mem := Subgroup.le_normalizer huL
      u_not_central := hcov.not_mem_centralizer_of_orderOf_two huL hu2
      K_le := hKL
      u_mem_centralizer_K := mem_centralizer_iff.2 hKu
      standard_in_L := solStd_of_centralizer_eq hK' hu'2 hqK' hZ'
      autCentralizer_two := twoAdic_le_two_of_card_le_four _ hC }

theorem fi23FixesElem_of_atlas (hmult : OddMultTrivial .Fi23) (hfix : Fi22CoversFixesElem) :
    Fi23FixesElem := by
  intro H _ _ L K u hcov hQ
  have hK : IsOddCentralExt Fi23D ↥K :=
    fi23_rowIsK hmult .Fi23 (List.mem_singleton_self _) H L K u hcov hQ
  have : Finite ↥K := oddCentralExt_finite hK
  exact hfix ↥K (oddCentralExt_perfect hK) (k3_cq_fi22 hK)

theorem fiRowFacts_fi23 (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) :
    Eng.FiRowFacts IsKFi23 [.Fi23] [.Fi24Prime] [.Fi22] := by
  have hmult : OddMultTrivial .Fi23 := fun L _ _ hq _ hcq => pf.mult23 L hq hcq
  have hfix23 : Fi23FixesElem := fi23FixesElem_of_atlas hmult atl.fi22Covers
  refine
    { fi23 := fun s hs => Or.inr (by simp)
      reach := reach_fi22K pf hyp12 atl.fi22Covers atl.fi22Even [.Fi23] [.Fi24Prime]
        (fun s hs => by simpa using hs) (by simp) (by simp)
      evenOut := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact fiEvenOut_fi23 pf _
      thm24 := fun s hs => by
        rcases List.mem_singleton.1 hs with rfl
        exact Or.inr ⟨by decide, pinThm24Hex23 lo⟩
      std_row := fiStdRow_of (D := Fi23D) fi23D_card_center
        (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple)
        (by have := fi23D_card; omega) (fun G _ _ L K u hcov hQ => solomonLocalQ_fi23 hmult hcov hQ)
      four_a := fiFourA_of (D := Fi23D) (s' := .Fi23) (n := 2 * 64561751654400)
        (by rw [fi23D_card_center]; exact even_two) fi23D_card_center
        (not_isMulCommutative_of_quasisimple fi23D_isQuasisimple)
        (by have := fi23D_card; omega)
        (fun G _ _ L K u hcov hQ => by
          obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ := (lemma36DataQ_fi23 hmult hfix23).data G L K u
            hcov hQ
          exact ⟨hsol, htwo⟩)
        (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
          obtain ⟨f⟩ := k3_cq_fi22 hX
          exact atl.fi22Covers K₂ hperf ⟨e.trans f⟩) }

end Facts

end CFSG.EvenSporadicStandard.Induction.Fi
