module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverMore

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic


theorem fiLoc22_data {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi22 L) (hQ : fiLoc 18393661440 H L K u) :
    ∃ huL : u ∈ L, bar (K.subgroupOf L) =
        centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) ∧
      CentralizerModel (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  obtain ⟨huL, hu2, hKL, hKu, hKq, hsz⟩ := hQ
  refine ⟨huL, ?_⟩
  have hodd := hcov.odd_center
  have hu1 := sq_of_orderOf_two huL hu2
  have hKu' := central_subgroupOf huL hKu
  have hnc : (⟨u, huL⟩ : ↥L) ∉ center ↥L := fun hz =>
    hcov.not_mem_centralizer_of_orderOf_two huL hu2 (mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩))
  have huY2 : orderOf ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hu1]
      rfl
    · intro h
      exact hnc ((QuotientGroup.eq_one_iff _).1 h)
  have hKuY : ∀ k ∈ bar (K.subgroupOf L), k * ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) =
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) * k := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := mem_bar.1 hk
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hKu' k' hk']
  have hcard : 18393661440 ≤ Nat.card (bar (K.subgroupOf L)) :=
    hsz.trans (card_quotient_oddCore_le_bar hodd hKL)
  exact fi22_cover_model hcov.2.2 huY2 hKuY hcard

theorem fiIn22_data {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi22 L) (hQ : fiInBase .Fi22 18393661440 H L K u) :
    ∃ huL : u ∈ L, bar (K.subgroupOf L) =
        centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) ∧
      CentralizerModel (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) :=
  fiLoc22_data hcov (fiInBase_iff.1 hQ).1

theorem solomonLocalQ_fi22 {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hcov : OddCover .Fi22 L) (hQ : fiInBase .Fi22 18393661440 H L K u) : SolomonLocalQ L K u := by
  obtain ⟨huL, hbar, hmodel⟩ := fiIn22_data hcov hQ
  obtain ⟨-, hu2, hKL, hKu, hKq, -, -⟩ := hQ
  exact solomonLocalQ_of_cover hcov.1 hcov.odd_center hKq huL
    (hcov.not_mem_centralizer_of_orderOf_two huL hu2) hu2 hKL hKu hmodel hbar

theorem sol78SettingLocalQ_fi22 : Sol78SettingLocalQ .Fi22 fiIn22 fiIn22 := by
  intro H _ _ L K u hcov hQ
  exact ⟨solomonLocalQ_fi22 hcov hQ.1, hQ⟩

theorem sol78Local39Q_fi22 : Sol78Local39Q .Fi22 fiIn22 := by
  intro H _ _ N L K t u hcov hset hQ
  obtain ⟨huL, hbar, hmodel⟩ := fiIn22_data hcov hQ.1
  obtain ⟨-, hu2, hKL, hKu, hKq, -, -⟩ := hQ.1
  exact local39_of_cover hcov.1 hcov.odd_center hKq huL hu2 hKL hKu hset.hyp35 hmodel hbar

end CFSG.EvenSporadicStandard.Induction
