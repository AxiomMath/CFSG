module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp23

namespace Three

section Comp

theorem commute_of_tightInO2 {X : Type} [Group X] [Finite X] {x : X}
    (hx : CFSG.ClassicalInvolution.Q3.TightInO2 x) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    ∀ y ∈ L, x * y = y * x := by
  obtain ⟨Q, hQn, hQ2, hxQ⟩ := hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  have hsolv : Group.IsSolvable ↥Q := inferInstance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hsolv hQn.isSubnormal).1 L hL
  intro y hy
  have h1 : ⁅y, x⁆ ∈ ⁅L, Q⁆ := Subgroup.commutator_mem_commutator hy hxQ
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h1
  calc x * y = (y * x * y⁻¹ * x⁻¹) * (x * y) := by rw [h1, one_mul]
    _ = y * x := by group

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_centralizes {B : Subgroup G} {c b : G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B)
    (hc1 : c ≠ 1) (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (h : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * y = y * oddQuotMk c ⟨b, hbC⟩) : Hyp51At B c := by
  have hnot : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ¬ MovedByAll B c L := by
    intro L hL hm
    obtain ⟨y, hyL, hy⟩ := hm _ (oddQuotMk_mem_modOdd hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC)
    exact hy (h L hL y hyL)
  exact ⟨fun L L' hL _ hm _ => absurd hm (hnot L hL), fun L hL hm => absurd hm (hnot L hL)⟩

end Comp

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
