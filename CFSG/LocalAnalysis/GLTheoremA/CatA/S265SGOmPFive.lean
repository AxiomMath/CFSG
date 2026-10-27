module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGTor
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Lift

open CFSG.StandardType

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem sq_add_add_one_ne_zero_omP {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) (s : F) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro hs
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs2 : s ^ 2 = s + 1 := by linear_combination hs - (s + 1) * h2
  have hs3 : s ^ 3 = 1 := by linear_combination (s + 1) * hs2 + s * h2
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 3 * k + 2 := ⟨(2 ^ n + 1) / 3 - 1, by omega⟩
  have := Fintype.ofFinite F
  have hpow : s ^ (3 * k + 2) = s := by
    have h := FiniteField.pow_card s
    rwa [Fintype.card_eq_nat_card, hF, hk] at h
  rw [pow_add, pow_mul, hs3, one_pow, one_mul] at hpow
  exact one_ne_zero (by linear_combination hpow - hs2 : (1 : F) = 0)

private theorem ggTorusLift_omP_five
    {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusLift 3 4 (OrthRest.RPlus F 5) := by
  obtain ⟨M, σ, hM, hσ, -, -⟩ := OrthRestTail.exists_rot hF
    (sq_add_add_one_ne_zero_omP hF h3) Nat.prime_three (by norm_num) h3
  have hP := OrthRestTail.torusConcl_of_frame (OrthRestTail.plusFrame F 5) Nat.prime_three
    (by norm_num) hM hσ (by norm_num) (P := ⊥) (SP := ∅) bot_le (Set.empty_disjoint _)
    OrthRestTail.isElemAbelian_bot' bot_le (e := 0) (by rw [Subgroup.card_bot, pow_zero])
  rw [TableBOrth.coe_qPlusForm, add_zero] at hP
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ := OrthRestTail.exists_R_of_torusConcl
    (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (by norm_num)) hP
  obtain ⟨hZ, hZp⟩ := OrthNs.center_data_omegaPlus (K := F) Nat.prime_three (by norm_num)
    (by norm_num : 3 ≤ 5)
  exact OrthRest.ggTorusLift_of_R Nat.prime_three hZ hZp hU hU2 hEU hE hcard

private theorem labelAll_torusLift_omP_five
    {lab : GLALabel}
    (htag : lab.tag = .D) (h3 : 3 ∣ 2 ^ lab.n + 1) (h5 : lab.rank = 5) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 4 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 h5 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with hl3
  · omega
  obtain ⟨F, _, _, hF, hq⟩ := hQ
  have := charP_two_of_card hF
  subst h5
  exact ⟨F, inferInstance, inferInstance, hF, hq, ggTorusLift_omP_five hF h3⟩

end Lift

theorem SG.false_of_omP_five
    {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hB : Nat.card B = 3 ^ 4) {lab : GLALabel}
    (hlab : LabelOf S lab) (htag : lab.tag = .D) (h3 : 3 ∣ 2 ^ lab.n + 1)
    (h5 : lab.rank = 5) : False :=
  SG.false_of_torusLift h hB hlab le_rfl (labelAll_torusLift_omP_five htag h3 h5)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
