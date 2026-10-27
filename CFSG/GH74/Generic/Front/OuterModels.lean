module

public import CFSG.GH74.Generic.Front.Props
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier

public section

namespace CFSG.GH74.Generic

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.L5U5 CFSG.LieType.BorelTits

theorem exists_prime_pow_card (F : Type) [Field F] [Finite F] :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F p
  exact ⟨p, n, hn, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem outer_solvable_statedSL4 {F : Type} [Field F] [Finite F] :
    Group.IsSolvable (Outer ↥(StatedSL 4 F)) := by
  obtain ⟨p, f, hp, hf, hF⟩ := exists_prime_pow_card F
  have hadm : StatedLieAdmissible .PSL (3 + 1) p f :=
    ⟨hp, hf, by norm_num, by simp, by simp⟩
  have hQ := SpecialLinear.isQuasisimple 3 F (by norm_num)
  have hmod := SpecialLinear.statedClassicalModel_center_quotient 3 F hadm hF
  have hs := (linear_higher_classical_model_schreier (by norm_num) hmod).2
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 4) F) := hQ.1
  have : Group.IsSolvable (Outer (Matrix.SpecialLinearGroup (Fin 4) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F))) := hs
  have h1 : Group.IsSolvable (Outer (Matrix.SpecialLinearGroup (Fin 4) F)) :=
    solvable_of_centerQuotient _
  exact solvable_of_equiv (specialLinearGroupEquivStatedSL 4 F)

theorem outer_solvable_statedSU4 {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) : Group.IsSolvable (Outer ↥(StatedSU 4 q F)) := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    subst hf0
    simp at hF
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hadm : StatedLieAdmissible .PSU 4 p f := ⟨hp.out, hf, by norm_num, by simp⟩
  have hmod := Unitary.statedClassicalModel_center_quotient (n := 4) (F := F) (p := p) (f := f)
    hadm hF
  have hs := (unitary_classical_model_schreier hmod).2
  have hqs := Unitary.isQuasisimple_SU (n := 4) (p := p) (f := f) hF (by norm_num) (by simp)
  have : Group.IsPerfect (Unitary.SU (unitaryInvolution F p f) 4) := hqs.1
  have : Group.IsSolvable (Outer (Unitary.SU (unitaryInvolution F p f) 4 ⧸
      Subgroup.center (Unitary.SU (unitaryInvolution F p f) 4))) := hs
  have h1 : Group.IsSolvable (Outer (Unitary.SU (unitaryInvolution F p f) 4)) :=
    solvable_of_centerQuotient _
  exact solvable_of_equiv (Unitary.equivStatedSU hF 4)

theorem outer_solvable_statedSp2 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    Group.IsSolvable (Outer ↥(StatedSp 2 F)) := by
  obtain ⟨p, f, hp, hf, hcard⟩ := exists_prime_pow_card F
  have hadm : StatedLieAdmissible .PSp 2 p f := ⟨hp, hf, le_rfl, by
    intro h
    have h2 : p ^ f = 2 := (Prod.mk.inj h).2
    rw [hcard, h2] at hF
    exact absurd hF (by decide)⟩
  have hqs := Symplectic.isQuasisimple_of_admissible 2 F hadm hcard
  have hmod := Symplectic.statedClassicalModel_center_quotient 2 F hadm hcard
  have hs := (CFSG.ComponentClassification.CatalogueBSymplecticTwo.classical_model_two_schreier
    hmod).2
  have : Group.IsPerfect (StatedSp 2 F) := hqs.1
  have : Group.IsSolvable (Outer (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F))) := hs
  exact solvable_of_centerQuotient _

theorem outerSolvableStatement : OuterSolvableStatement := by
  intro K _ hK
  rcases hK with (⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩) | ⟨F, _, _, hodd, ⟨e⟩⟩
  · have := outer_solvable_statedSL4 (F := F)
    exact solvable_of_equiv e.symm
  · have := outer_solvable_statedSU4 (F := F) hF hq
    exact solvable_of_equiv e.symm
  · have := outer_solvable_statedSp2 (F := F) hodd
    exact solvable_of_equiv e.symm

theorem outerStatement_of_three (h : OuterThreeStatement) : OuterStatement :=
  ⟨outerSolvableStatement, h⟩

end CFSG.GH74.Generic
