module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InLocal39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Model


theorem fi24in_data {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi24Prime L) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    ∃ huL : u ∈ L, Fi24InCoverBase L K u huL ∧
      Fi24InPair (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) (bar (K.subgroupOf L)) := by
  obtain ⟨huL, hu2, hKL, hKu, hKq, hsz⟩ := hQ
  refine ⟨huL, ?_⟩
  have hodd := hcov.odd_center
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hnc : (⟨u, huL⟩ : ↥L) ∉ center ↥L := fun hz =>
    hcov.not_mem_centralizer_of_orderOf_two huL hu2 (mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩))
  have hu1 := sq_of_orderOf_two huL hu2
  have huY2 : orderOf ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hu1]
      rfl
    · intro h
      exact hnc ((QuotientGroup.eq_one_iff _).1 h)
  have hKu' := central_subgroupOf huL hKu
  have hKuY : ∀ k ∈ bar (K.subgroupOf L), k * ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) * k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := mem_bar.1 hk
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hKu' k' hk']
  have hKperf : ⁅bar (K.subgroupOf L), bar (K.subgroupOf L)⁆ = bar (K.subgroupOf L) := by
    unfold bar
    rw [← Subgroup.map_commutator, hK']
  have hcard : 2 * 64561751654400 ≤ Nat.card (bar (K.subgroupOf L)) :=
    hsz.trans (card_quotient_oddCore_le_bar hodd hKL)
  exact ⟨fi24in_base hcov.2.2 huY2 hKuY hKperf hcard, huY2, hKuY, hKperf, hcard⟩

theorem sol78SettingLocalQ_fi24in : Sol78SettingLocalQ .Fi24Prime fiIn24 fiIn24 := by
  intro H _ _ L K u hcov hQ
  have hQ' : fiLoc (2 * 64561751654400) H L K u := (fiInBase_iff.1 hQ).1
  obtain ⟨huL, hbase, -⟩ := fi24in_data hcov hQ'
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := hQ'
  exact ⟨fi24in_solomonLocalQ_of_base hcov.1 hcov.odd_center hKq huL
    (hcov.not_mem_centralizer_of_orderOf_two huL hu2) hu2 hKL hKu hbase, hQ⟩

theorem sol78Local39Q_fi24in (hpairs : Fi24InPairs) (hgen : Fi24InGenerate) :
    Sol78Local39Q .Fi24Prime fiIn24 := by
  intro H _ _ N L K t u hcov hset hQ
  have hQ' : fiLoc (2 * 64561751654400) H L K u := (fiInBase_iff.1 hQ).1
  obtain ⟨huL, hbase, hpair⟩ := fi24in_data hcov hQ'
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := hQ'
  exact fi24in_local39 hcov.1 hcov.odd_center hKq huL hu2 hKL hKu hset.hyp35 hbase
    (hpairs _ hcov.2.2 _ _ hpair) (hgen _ hcov.2.2 _ _ hpair)

theorem lemma36DataQ_fi24in (hfix : Fi24InFixesElem) :
    Lemma36DataQ .Fi24Prime (fiLoc (2 * 64561751654400)) 2 16 := by
  refine ⟨by norm_num, ?_⟩
  intro H _ _ L K u hcov hQ
  obtain ⟨huL, hbase, -⟩ := fi24in_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, -⟩ := id hQ
  have hC : Nat.card (autCentralizer L K) ≤ 4 :=
    card_autCentralizer_le_of_cover hcov.1.1 hbase.outTwo hbase.card_centralizer_le
  exact ⟨hu2, fi24in_mem_of_base hcov.odd_center huL hu2 hbase,
    fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩,
    fi24in_characteristic_of_base hKq huL hKL hKu hbase, hKq,
    isSolvable_autCentralizer_of_card_le hC, twoAdic_le_two_of_card_le_four _ hC,
    hfix H L K u hcov hQ⟩

end Model

section Core

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem solomonCoreP_fi24in : SolomonCoreP .Fi24Prime fiIn24 :=
  solomonCoreP_of_fusion .Fi24Prime noExc fiIn24 (fun _ _ _ _ _ hQ => hQ.1) fi24FusionData
    (excExcluded_noExc _ _)

end Core

section Closing


theorem sol78Closing_fi24in (hpairs : Fi24InPairs) (hgen : Fi24InGenerate) :
    Sol78Closing [.Fi24Prime] (fun _ => fiIn24) :=
  sol78Closing_of_partsP (S := [.Fi24Prime]) (Q := fun _ => fiIn24) (P := fun _ => fiIn24)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact sol78SettingLocalQ_fi24in)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact sol78Local39Q_fi24in hpairs hgen)
    (fun s hs => by
      rcases List.mem_singleton.1 hs with rfl
      exact solomonCoreP_fi24in)

end Closing

end CFSG.EvenSporadicStandard.Induction
