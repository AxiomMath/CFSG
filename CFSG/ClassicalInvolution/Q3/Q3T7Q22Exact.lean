module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Asc77.AscT7Z23
public import CFSG.ClassicalInvolution.Asc77.AscT7Z8

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7Z

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77.T7Z
open scoped MatrixGroups


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCore_exactCore_eq_bot (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : c * c = 1)
    (hOc : classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c) = ⊥) {d : ℕ} {ε : Bool}
    (hY : LayerOrthType Ω c d ε) {J : Subgroup G} (hJ : J ∈ ExactLayer.tqMembers Ω c) :
    classicalInvolutionOddCore ↥(ExactLayer.exactCore c J) = ⊥ := by
  classical
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  obtain ⟨t', n', hT, D, hcard, i, hit, hir⟩ := hY
  obtain ⟨hG2', hD4'⟩ := isOrthTag_ne hT
  have hG2 : D.tag i ≠ .G2 := hit ▸ hG2'
  have hD4 : D.tag i ≠ .trialityD4 := hit ▸ hD4'
  have hexp : D.exp i = 1 := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd h hD4
  have hJc : ExactLayer.exactCore c J ∈ ExactLayer.exactFamily Ω c :=
    ExactLayer.exactCore_mem_exactFamily hJ
  have hJY : ExactLayer.exactCore c J ≤ ExactLayer.exactLayer Ω c :=
    ExactLayer.exactCore_le_exactLayer hJ
  have hM : ((ExactLayer.exactCore c J).subgroupOf (ExactLayer.exactLayer Ω c)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))) ∈
      oddQuotientFamily (restrictFamily (ExactLayer.exactFamily Ω c) (ExactLayer.exactLayer Ω c)) :=
    ⟨_, ⟨_, hJc, hJY, rfl⟩, rfl⟩
  obtain ⟨j, R, hR, hMR⟩ := D.fundamental _ hM
  obtain rfl : j = i := Fin.ext (by
    have h1 := i.2
    have h2 := j.2
    omega)
  have hfin : Finite (modelUniv (D.tag j) (D.rank j) 3 (D.exp j) Fact.out).K :=
    ModelFacts.finite_modelUniv (by norm_num) Fact.out (ih8_isFundTag_mf (D.isFundTag j))
      (D.admissible j)
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (D.isFundTag j) (D.admissible j) hG2 hD4 hR
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 one_ne_zero
  have hSL : Nat.card SL(2, GaloisField 3 (D.exp j)) = 24 := by
    rw [hexp, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF3]
    norm_num
  have hcardR : Nat.card ↥R = 24 := (Nat.card_congr eR.toEquiv).trans hSL
  have hmapR : Nat.card ↥(R.map (D.hom j)) ≤ Nat.card ↥R :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd R (D.hom j))
  have hinj : Function.Injective
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOc]
  have hMcard : Nat.card ↥(ExactLayer.exactCore c J) ≤ 24 := by
    have h1 : Nat.card ↥(ExactLayer.exactCore c J) =
        Nat.card ↥((ExactLayer.exactCore c J).subgroupOf (ExactLayer.exactLayer Ω c)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv).symm
    have h2 : Nat.card ↥(((ExactLayer.exactCore c J).subgroupOf (ExactLayer.exactLayer Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)))) =
        Nat.card ↥((ExactLayer.exactCore c J).subgroupOf (ExactLayer.exactLayer Ω c)) :=
      Subgroup.card_map_of_injective hinj
    rw [hMR] at h2
    omega
  obtain ⟨z₀, hz₀⟩ := hΩ.classical J hJ.1
  have hK3 : IsClassicalMember3 J z₀ := hz₀.toQ3 (by norm_num)
  obtain ⟨eQ⟩ := Q3NL.nonempty_equiv_exactCore3 hK3 hc2' hJ.2
  obtain ⟨eJ⟩ := hK3.nonempty_equiv
  have hq24 : Nat.card (↥(ExactLayer.exactCore c J) ⧸
      classicalInvolutionOddCore ↥(ExactLayer.exactCore c J)) = 24 := by
    rw [Nat.card_congr (eQ.trans eJ).toEquiv, natCard_sl2Three]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (classicalInvolutionOddCore ↥(ExactLayer.exactCore c J))
  rw [hq24] at hmul
  have hpos : 0 < Nat.card ↥(classicalInvolutionOddCore ↥(ExactLayer.exactCore c J)) :=
    Nat.card_pos
  apply Subgroup.eq_bot_of_card_eq
  nlinarith

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7Z
