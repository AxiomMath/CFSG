module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveCo3
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoFrontier

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3

private theorem gLAPPrimeCoreOf_centralizer_subtype_eq_bot {M : Type*} [Group M] {P : Subgroup M}
    {p : ℕ} {x : M} (hx : x ∈ P)
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set M) ⊓ P) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)) = ⊥ := by
  have hc : (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)).map P.subtype =
      Subgroup.centralizer ({x} : Set M) ⊓ P := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, z.2⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hz)
      simpa using this
    · intro hy
      obtain ⟨hyc, hyP⟩ := Subgroup.mem_inf.1 hy
      refine ⟨⟨y, hyP⟩, Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_), rfl⟩
      simpa using Subgroup.mem_centralizer_singleton_iff.1 hyc
  have hmap := map_glaPPrimeCoreOf_of_injective p P.subtype P.subtype_injective
    (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P))
  rw [hc, h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hmap

theorem sporadicTwoBalanceFive_Co3 :
    SporadicTwoBalanceFive .Co3 := by
  intro S _ _ hS hnab he
  obtain ⟨e⟩ := he
  obtain ⟨hb⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  let eN : S ≃* Blueprint.NativeSporadic.Co3 := e.trans hb.symm
  let f : S ≃* ↥co3P := eN.trans co3PermEquiv
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hinn : innerAut S = ⊤ := (CFSG.Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.2
    S ⟨eN⟩).2
  obtain ⟨Q, hQ⟩ := co3FiveQ_sylow
  have hQmem : ∀ g : ↥co3P, g ∈ Q ↔ (g : Equiv.Perm (Fin 276)) ∈ co3FiveQ := fun g => by
    change g ∈ (Q : Subgroup ↥co3P) ↔ _
    rw [hQ, Subgroup.mem_subgroupOf]
  have hQc : Nat.card Q = 5 ^ 3 := by
    change Nat.card (Q : Subgroup ↥co3P) = _
    rw [hQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3FiveQ_le_P).toEquiv, card_co3FiveQ]
    norm_num
  have hz25P : co3FiveLine 25 ∈ co3P := co3FiveQ_le_P (co3FiveLine_mem_Q 25)
  have hzQ : (⟨co3FiveLine 25, hz25P⟩ : ↥co3P) ∈ Q := (hQmem _).2 (co3FiveLine_mem_Q 25)
  have hzo : orderOf (⟨co3FiveLine 25, hz25P⟩ : ↥co3P) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_co3FiveLine 25
  have hcomm : ∀ a ∈ co3FiveQ, a * co3FiveLine 25 = co3FiveLine 25 * a := fun a ha => by
    have haA : a ∈ co3FiveA := by
      rw [co3FiveA_eq_Q]
      exact ha
    exact Subgroup.mem_centralizer_singleton_iff.1 (co3FiveC25_le_centralizer (co3FiveA_le_C25 haA))
  have hzc : ∀ g ∈ Q, g * ⟨co3FiveLine 25, hz25P⟩ = ⟨co3FiveLine 25, hz25P⟩ * g :=
    fun g hg => Subtype.ext (hcomm _ ((hQmem g).1 hg))
  have hnc : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm' : ∀ a ∈ co3FiveQ, ∀ b ∈ co3FiveQ, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hcon ⟨a, co3FiveQ_le_P ha⟩ ((hQmem _).2 ha) ⟨b, co3FiveQ_le_P hb⟩
        ((hQmem _).2 hb))
    have hle : co3FiveQ ≤ Subgroup.centralizer (co3FiveQ : Set (Equiv.Perm (Fin 276))) ⊓
        co3FiveC25 := fun a ha =>
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb => hcomm' b hb a ha, by
        have haA : a ∈ co3FiveA := by
          rw [co3FiveA_eq_Q]
          exact ha
        exact co3FiveA_le_C25 haA⟩
    have hc5 : Nat.card (Subgroup.centralizer (co3FiveQ : Set (Equiv.Perm (Fin 276))) ⊓
        co3FiveC25 : Subgroup (Equiv.Perm (Fin 276))) = 5 := by
      rw [← co3FiveA_eq_Q]
      exact card_co3FiveCentA
    have h1 := Subgroup.card_le_of_le hle
    rw [card_co3FiveQ, hc5] at h1
    norm_num at h1
  have hO : GLAPPrimeCoreOf 5
      (Subgroup.centralizer ({(⟨co3FiveLine 25, hz25P⟩ : ↥co3P)} : Set ↥co3P)) = ⊥ :=
    gLAPPrimeCoreOf_centralizer_subtype_eq_bot hz25P
      (gLAPPrimeCoreOf_co3FiveRecord_eq_bot 25 (Or.inr rfl))
  exact isLocallyBalancedAbs_two_of_sylow_card_cube Nat.prime_five f hcen hinn Q hQc hzQ hzo hzc
    hnc hO

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
