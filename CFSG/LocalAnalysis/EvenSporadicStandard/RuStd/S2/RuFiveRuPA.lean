module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Transport
public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd
open CFSG.RankThree.Native

section Lines


theorem ruFiveLine_mem_Q (j : Fin 31) : ruFiveLine j ∈ ruFiveQ :=
  linesOK_mem ruFiveKeys_lt ruFive_lines_ok j

theorem ruFiveLine_mem_P (j : Fin 31) : ruFiveLine j ∈ ruP :=
  ruFiveQ_le_P (ruFiveLine_mem_Q j)

@[expose] noncomputable def lineP (j : Fin 31) : ruP := ⟨ruFiveLine j, ruFiveLine_mem_P j⟩

@[expose] noncomputable def transP (j : Fin 31) : ruP :=
  ⟨ruFiveTransporter j, (ruFiveTransporter_spec j).1⟩

theorem orderOf_lineP (j : Fin 31) : orderOf (lineP j) = 5 := by
  rw [← Subgroup.orderOf_coe]
  exact linesOK_orderOf ruFive_lines_ok j

theorem transP_conj (j : Fin 31) :
    transP j * lineP (ruFiveRecordOf j) * (transP j)⁻¹ = lineP j :=
  Subtype.ext (ruFiveTransporter_spec j).2

theorem ruFiveRecordOf_cases (j : Fin 31) : ruFiveRecordOf j = 0 ∨ ruFiveRecordOf j = 1 := by
  have h := ruFiveRecordOf_mem j
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem exists_line (q : ruP) (hq : (q : Equiv.Perm (Fin 4060)) ∈ ruFiveQ) (hq1 : q ≠ 1) :
    ∃ j : Fin 31, zpowers q = zpowers (lineP j) := by
  have hq5 : (q : Equiv.Perm (Fin 4060)) ^ 5 = 1 := linesOK_pow ruFiveKeys_lt ruFive_lines_ok hq
  have hqne : (q : Equiv.Perm (Fin 4060)) ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hcard : Nat.card (zpowers (q : Equiv.Perm (Fin 4060))) = 5 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hq5 hqne]
  have hmem : zpowers (q : Equiv.Perm (Fin 4060)) ∈
      {H : Subgroup (Equiv.Perm (Fin 4060)) |
        H ≤ Subgroup.closure (permsA 4060 ruFiveQGens) ∧ Nat.card H = 5} :=
    ⟨zpowers_le.2 hq, hcard⟩
  rw [(linesOK_lines ruFiveKeys_lt ruFive_lines_ok).1] at hmem
  obtain ⟨j, hj⟩ := hmem
  refine ⟨j, Subgroup.map_injective ruP.subtype_injective ?_⟩
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact hj.symm

theorem cover_ruP (q : ruP) (hq : (q : Equiv.Perm (Fin 4060)) ∈ ruFiveQ) (hq1 : q ≠ 1) :
    (∃ (d : ruP) (k : ℤ), d * lineP 0 * d⁻¹ = q ^ k) ∨
      (∃ (d : ruP) (k : ℤ), d * lineP 1 * d⁻¹ = q ^ k) := by
  obtain ⟨j, hj⟩ := exists_line q hq hq1
  have hmem : lineP j ∈ zpowers q := hj ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have h := transP_conj j
  rw [← hk] at h
  rcases ruFiveRecordOf_cases j with hr | hr
  · rw [hr] at h
    exact Or.inl ⟨transP j, k, h⟩
  · rw [hr] at h
    exact Or.inr ⟨transP j, k, h⟩

theorem card_centralizer_lineP_rec (j : Fin 31) :
    Nat.card (centralizer ({lineP j} : Set ruP)) =
      Nat.card (centralizer ({lineP (ruFiveRecordOf j)} : Set ruP)) := by
  rw [← transP_conj j]
  simpa using card_centralizer_equiv (MulAut.conj (transP j)) (lineP (ruFiveRecordOf j))

theorem card_centralizer_lineP₀ :
    Nat.card (centralizer ({lineP 0} : Set ruP)) = 1000 := by
  rw [card_centralizer_subtype ruP (lineP 0)]
  have h := ruFiveC0_spec
  rw [inf_comm] at h
  change Nat.card ↥(ruP ⊓ centralizer ({ruFiveLine 0} : Set (Equiv.Perm (Fin 4060)))) = 1000
  rw [← h.1]
  exact h.2

theorem card_centralizer_lineP₁ :
    Nat.card (centralizer ({lineP 1} : Set ruP)) = 300 := by
  rw [card_centralizer_subtype ruP (lineP 1)]
  have h := ruFiveC1_spec
  rw [inf_comm] at h
  change Nat.card ↥(ruP ⊓ centralizer ({ruFiveLine 1} : Set (Equiv.Perm (Fin 4060)))) = 300
  rw [← h.1]
  exact h.2

end Lines

end CFSG.EvenSporadicStandard.RuStd.S2
