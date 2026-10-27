module

public import CFSG.GH74.Generic.Front.OuterModels
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.GH74.Generic

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.L5U5 CFSG.LieType.BorelTits

theorem eq_one_of_odd_of_card_dvd_four {O : Type*} [Group O] (hO : Nat.card O ∣ 4) (o : O)
    (ho : Odd (orderOf o)) : o = 1 := by
  have h1 : orderOf o ∣ 2 ^ 2 := (orderOf_dvd_natCard o).trans (by simpa using hO)
  have hc : Nat.Coprime (orderOf o) (2 ^ 2) := (Nat.coprime_two_right.2 ho).pow_right 2
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hc h1)

theorem outer_odd_trivial_statedSp2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∀ o : Outer ↥(StatedSp 2 F), Odd (orderOf o) → o = 1 := by
  obtain ⟨p, f, hp, hf, hcard⟩ := exists_prime_pow_card F
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hadm : StatedLieAdmissible .PSp 2 p f := ⟨hp, hf, le_rfl, by
    intro h
    have h2 : p ^ f = 2 := (Prod.mk.inj h).2
    rw [hcard, h2] at hodd
    exact absurd hodd (by decide)⟩
  have hqs := Symplectic.isQuasisimple_of_admissible 2 F hadm hcard
  have hmod := Symplectic.statedClassicalModel_center_quotient 2 F hadm hcard
  obtain ⟨-, K', _, _, hK', hJ⟩ := hmod
  have : Group.IsPerfect (StatedSp 2 F) := hqs.1
  have hOut :=
    (SymplecticHigher.perfect_symplectic_central_quotient_outer_prime_control hp hf le_rfl hK'
      (StatedSp 2 F) hJ).2.2.1
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).1 (hcard.symm.trans hF)
  have h4 : Nat.card (Outer ↥(StatedSp 2 F)) ∣ 4 := by simpa using hOut
  exact fun o ho => eq_one_of_odd_of_card_dvd_four h4 o ho

theorem outer_odd_trivial_statedSL4 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∀ o : Outer ↥(StatedSL 4 F), Odd (orderOf o) → o = 1 := by
  obtain ⟨p, f, hp, hf, hcard⟩ := exists_prime_pow_card F
  have hadm : StatedLieAdmissible .PSL (3 + 1) p f :=
    ⟨hp, hf, by norm_num, by simp, by simp⟩
  have hQ := SpecialLinear.isQuasisimple 3 F (by norm_num)
  have hmod := SpecialLinear.statedClassicalModel_center_quotient 3 F hadm hcard
  have hOut := (linear_model_outer_two_part_bound _ (3 + 1) p f hmod).2.2.2.2 (by norm_num)
  obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).1 (hcard.symm.trans hF)
  have h4 : Nat.card (Outer (Matrix.SpecialLinearGroup (Fin 4) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F))) ∣ 4 := by simpa using hOut
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 4) F) := hQ.1
  intro o ho
  let e := equivalence (specialLinearGroupEquivStatedSL 4 F)
  have hinj := centerQuotient_outer_injective (Matrix.SpecialLinearGroup (Fin 4) F)
  have ho' : Odd (orderOf (centerQuotientOuterHom (Matrix.SpecialLinearGroup (Fin 4) F)
      (e.symm o))) := by
    rw [orderOf_injective _ hinj, MulEquiv.orderOf_eq]
    exact ho
  have h1 := eq_one_of_odd_of_card_dvd_four h4 _ ho'
  have h2 : e.symm o = 1 := hinj (by rw [h1, map_one])
  exact e.symm.injective (by rw [h2, map_one])

theorem outerThreeStatement : OuterThreeStatement := by
  intro K _ _ hK o ho
  obtain ⟨F, _, _, hF, h | h⟩ := hK
  · obtain ⟨e⟩ := h
    have h1 := outer_odd_trivial_statedSL4 hF (equivalence e o) (by rwa [MulEquiv.orderOf_eq])
    exact (equivalence e).injective (by rw [h1, map_one])
  · obtain ⟨e⟩ := h
    have h1 := outer_odd_trivial_statedSp2 hF (equivalence e o) (by rwa [MulEquiv.orderOf_eq])
    exact (equivalence e).injective (by rw [h1, map_one])

end CFSG.GH74.Generic
