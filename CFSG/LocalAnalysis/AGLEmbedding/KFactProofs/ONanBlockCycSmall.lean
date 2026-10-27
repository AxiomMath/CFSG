module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSmall
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabAutIrr
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem aut5Le_alternatingGroup_five : Aut5Le (alternatingGroup (Fin 5)) := by
  refine aut5Le_of_not_sq_dvd ?_
  have h : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
    rw [← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))), Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [h]
  norm_num

theorem aut5Le_of_model_psu_three_three {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSU 3 3 1) : Aut5Le Y := by
  obtain ⟨-, hsimple⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 3 1 h
  obtain ⟨K, _, hU3, hq, hn3, ⟨e⟩⟩ := exists_equiv_primeFormP_gen h
  obtain ⟨⟨eP⟩, -, -, hOutT, -⟩ := unitary_full_diagonal_outer_order hU3 hn3 hq
  have hY : Nat.card Y = 6048 := by
    have h1 := card_unitaryPSU_three_mul_gcd hU3
    rw [← Nat.card_congr (e.trans eP).toEquiv] at h1
    norm_num at h1
    exact h1
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : IsMulCommutative Y := ⟨⟨fun a b => of_not_not fun h => hcon ⟨a, b, h⟩⟩⟩
    let _ : CommGroup Y := { ‹Group Y› with mul_comm := mul_comm' }
    have := IsSimpleGroup.prime_card (α := Y)
    rw [hY] at this
    norm_num at this
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    CFSG.RankThree.PartOne.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab)
  have hOut : Nat.card (Outer Y) = 2 := by
    obtain ⟨⟨e', -⟩, -⟩ := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e)
    rw [Nat.card_congr e'.toEquiv, hOutT]
    norm_num
  have hAut : Nat.card (MulAut Y) = 12096 := by
    rw [card_mulAut_eq_card_outer_mul hinj, hOut, hY]
  refine aut5Le_of_not_sq_dvd ?_
  rw [hAut]
  norm_num

theorem hasE9_or_aut5Le_of_small {Y : Type} [Group Y] [Finite Y] (hS : IsSmallTwo Y) :
    HasE9 Y ∨ Aut5Le Y := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (aut5Le_of_mulEquiv e.symm aut5Le_alternatingGroup_five)
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
  · rcases hd with ⟨q, hq7, hd1⟩ | ⟨q, hq3, hd1⟩
    ·
      obtain rfl : idx = .A 1 q := hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe : q.p = 7 ∧ q.exponent = 1 := by
        have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h7
      rw [hpe.1, hpe.2] at h
      exact hasE9_or_aut5Le_psl_three
        (CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven h)
    ·
      obtain rfl : idx = .twistedA 2 q := hd1
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p = 3 ∧ q.exponent = 1 := by
        have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h3
      rw [hpe.1, hpe.2] at h
      exact Or.inr (aut5Le_of_model_psu_three_three h)

end CFSG.AGLEmbedding.BlockCyc
