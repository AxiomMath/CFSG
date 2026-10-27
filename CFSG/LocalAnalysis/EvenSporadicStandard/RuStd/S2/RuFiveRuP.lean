module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveRuPA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveModelCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveChecks

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd
open CFSG.RankThree.Native
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Subgroups


theorem mem_centralizer_lineP₀_iff (c : ruP) :
    c ∈ centralizer ({lineP 0} : Set ruP) ↔ (c : Equiv.Perm (Fin 4060)) ∈ ruFiveC0 := by
  rw [ruFiveC0_spec.1, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨congrArg Subtype.val h, c.2⟩, fun h => Subtype.ext h.1⟩

theorem mem_centralizer_lineP₁_iff (c : ruP) :
    c ∈ centralizer ({lineP 1} : Set ruP) ↔ (c : Equiv.Perm (Fin 4060)) ∈ ruFiveC1 := by
  rw [ruFiveC1_spec.1, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨congrArg Subtype.val h, c.2⟩, fun h => Subtype.ext h.1⟩

noncomputable def subA : Subgroup ruP := ruFiveA0.subgroupOf ruP

theorem subA_le : subA ≤ centralizer ({lineP 0} : Set ruP) := fun a ha =>
  (mem_centralizer_lineP₀_iff a).2 (ruFiveA0_spec.1 ha)

theorem subA_normal : ∀ c ∈ centralizer ({lineP 0} : Set ruP), ∀ a ∈ subA, c * a * c⁻¹ ∈ subA := by
  intro c hc a ha
  have hcC : (c : Equiv.Perm (Fin 4060)) ∈ ruFiveC0 := (mem_centralizer_lineP₀_iff c).1 hc
  have haC : (a : Equiv.Perm (Fin 4060)) ∈ ruFiveC0 := ruFiveA0_spec.1 ha
  have hn := ruFiveA0_spec.2.1
  exact hn.conj_mem (⟨a, haC⟩ : ruFiveC0) ha (⟨c, hcC⟩ : ruFiveC0)

theorem card_subA : Nat.card subA = 125 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruFiveA0_spec.2.2.1).toEquiv).trans
    ruFiveA0_spec.2.2.2.1

theorem ruFiveD1_le_C1 : ruFiveD1 ≤ ruFiveC1 := by
  rw [ruFiveD1, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact ruFiveC1.mul_mem (ruFiveC1.mul_mem (ruFiveC1.mul_mem ha hb) (ruFiveC1.inv_mem ha))
    (ruFiveC1.inv_mem hb)

noncomputable def subD : Subgroup ruP := ruFiveD1.subgroupOf ruP

theorem subD_le : subD ≤ centralizer ({lineP 1} : Set ruP) := fun a ha =>
  (mem_centralizer_lineP₁_iff a).2 (ruFiveD1_le_C1 ha)

theorem subD_simple : IsSimpleGroup subD := by
  have := ruFiveD1_spec.1
  exact (Subgroup.subgroupOfEquivOfLe ruFiveD1_spec.2.2.2.1).isSimpleGroup

theorem card_subD : Nat.card subD = 60 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe ruFiveD1_spec.2.2.2.1).toEquiv).trans
    ruFiveD1_spec.2.2.1

theorem lineP_zero_not_mem : lineP 0 ∉ zpowers (lineP 1) := by
  intro h
  have hle : zpowers (lineP 0) ≤ zpowers (lineP 1) := zpowers_le.2 h
  have heq : zpowers (lineP 0) = zpowers (lineP 1) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_lineP, orderOf_lineP]
  have h2 : zpowers (ruFiveLine 0) = zpowers (ruFiveLine 1) := by
    have := congrArg (Subgroup.map ruP.subtype) heq
    rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
  have hinj := (linesOK_lines ruFiveKeys_lt ruFive_lines_ok).2
  exact absurd (hinj h2) (by decide)

theorem y_unique_ruP (q : ruP)
    (hq : (q : Equiv.Perm (Fin 4060)) ∈ ruFiveQ) (hq1 : q ≠ 1)
    (hc : q * lineP 1 = lineP 1 * q) (hcard : Nat.card (centralizer ({q} : Set ruP)) = 1000) :
    q ∈ zpowers (lineP 0) := by
  obtain ⟨j, hj⟩ := exists_line q hq hq1
  have hjm : lineP j ∈ zpowers q := hj ▸ mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hjm
  have hcomm : lineP j * lineP 1 = lineP 1 * lineP j := by
    rw [← hk]
    exact (Commute.zpow_left (show Commute q (lineP 1) from hc) k).eq
  have hcard' : Nat.card (centralizer ({lineP j} : Set ruP)) = 1000 := by
    rw [← centralizer_eq_of_zpowers_eq hj]
    exact hcard
  have hrec : ruFiveRecordOf j = 0 := by
    rcases ruFiveRecordOf_cases j with h | h
    · exact h
    · exfalso
      rw [card_centralizer_lineP_rec, h, card_centralizer_lineP₁] at hcard'
      omega
  have hj0 : j = 0 :=
    ruFiveLines_unique j (congrArg Fin.val hrec) (congrArg Subtype.val hcomm)
  rw [hj0] at hj
  exact hj ▸ mem_zpowers q

end Subgroups

theorem nonempty_fiveData :
    Nonempty (FiveData ruP) := by
  obtain ⟨S, hS⟩ := ruFiveQ_sylow
  have hmemS : ∀ q : ruP, q ∈ (S : Subgroup ruP) ↔
      (q : Equiv.Perm (Fin 4060)) ∈ ruFiveQ := fun q => by
    rw [hS]
    exact Iff.rfl
  obtain ⟨i, j, hi, hj, hi4, hi2, hj2, hji⟩ := ruFiveQ8_exists
  have hiP : i ∈ ruP := by
    rw [ruFiveC0_spec.1] at hi
    exact hi.2
  have hjP : j ∈ ruP := by
    rw [ruFiveC0_spec.1] at hj
    exact hj.2
  refine ⟨{
    Q := S
    Q_exp := fun q hq => Subtype.ext (by
      simpa using linesOK_pow ruFiveKeys_lt ruFive_lines_ok ((hmemS q).1 hq))
    x₀ := lineP 0
    x₁ := lineP 1
    x₀_mem := (hmemS _).2 (ruFiveLine_mem_Q 0)
    x₁_mem := (hmemS _).2 (ruFiveLine_mem_Q 1)
    x₀_order := orderOf_lineP 0
    x₁_order := orderOf_lineP 1
    cover := fun q hq hq1 => cover_ruP q ((hmemS q).1 hq) hq1
    card_C₀ := card_centralizer_lineP₀
    A := subA
    A_le := subA_le
    A_normal := subA_normal
    card_A := card_subA
    qi := ⟨i, hiP⟩
    qj := ⟨j, hjP⟩
    qi_mem := (mem_centralizer_lineP₀_iff _).2 hi
    qj_mem := (mem_centralizer_lineP₀_iff _).2 hj
    qi_pow := Subtype.ext (by simpa using hi4)
    qi_sq := fun h => hi2 (by simpa using congrArg Subtype.val h)
    qj_sq := Subtype.ext (by simpa using hj2)
    qj_conj := Subtype.ext (by simpa using hji)
    card_C₁ := card_centralizer_lineP₁
    D := subD
    D_le := subD_le
    D_simple := subD_simple
    card_D := card_subD
    y := lineP 0
    y_mem := (hmemS _).2 (ruFiveLine_mem_Q 0)
    y_comm := Subtype.ext ruFiveLine_comm_zero_one
    y_not_mem := lineP_zero_not_mem
    y_unique := fun q hq hq1 hc hcard => y_unique_ruP q ((hmemS q).1 hq) hq1 hc hcard }⟩

theorem ruFiveFacts_ruP :
    RuFiveFacts ruP :=
  nonempty_fiveData.elim fun d => d.facts

theorem ruFiveFacts_of_isSporadic
    {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) :
    RuFiveFacts Y := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  exact ruFiveFacts_ruP.of_mulEquiv e.symm

end CFSG.EvenSporadicStandard.RuStd.S2
