module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3Tr
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Main
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2Out
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2Split
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2Twist
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts


theorem ord3_fg2d : Ord3 FG2d := by
  intro r Y _ _ hr hr2 hr3 hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Stage2.Bender.Thm1.exists_mulEquiv_adjoint_of_lieModel hLM
  have : Fact r.Prime := ⟨hr⟩
  have : CharP K r :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hr hf hK
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hαo : orderOf (MulAut.congr e b) = 3 := by rw [MulEquiv.orderOf_eq, hb]
  have hα3 : (MulAut.congr e b) ^ 3 = 1 := by
    rw [← hαo]
    exact pow_orderOf_eq_one _
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by norm_num)
    omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact le_trans (by omega) (Nat.le_self_pow (by omega) r)
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K r]
    exact hr3
  have h3K : ¬ 3 ∣ Nat.card K := by
    intro h
    rw [hK] at h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  by_cases hinn : IsInnerAut (MulAut.congr e b)
  · obtain ⟨x, hx⟩ := hinn
    have hcen : center ↥(adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
    have hinj : Function.Injective
        (MulAut.conj : ↥(adjointGroup Tag.G2 K) →* MulAut ↥(adjointGroup Tag.G2 K)) :=
      Stage2.Bender.Thm1.mulAut_conj_injective_of_center_bot hcen
    have hxo : orderOf x = 3 := by
      rw [← orderOf_injective _ hinj x, hx, hαo]
    have hx3 : x ^ 3 = 1 := by
      rw [← hxo]
      exact pow_orderOf_eq_one x
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by omega
    rw [← hx]
    rcases hq with h | h
    · exact Or.inl (StepH3G2.exists_rgroup_of_inner_split h hx3)
    · exact Or.inl (StepH3G2.exists_rgroup_of_inner_twist hr2 hf hK h hxo)
  · exact Or.inl (StepH3G2.exists_rgroup_of_outer hK3 hK4 hα3 hinn)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
