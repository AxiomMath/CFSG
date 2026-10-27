module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23GOCLie
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Goldschmidt.J1ModelTransport
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.GH74.KGroups.PSL2
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section J1

theorem outCyc_j1
    {L : Type} [Group L] (e : L ≃* NativeSporadic.J1) : OutCyc L := by
  have h1 := (CFSG.Sporadic.Schreier.at_j1_schreier).1
  refine outCyc_of_mulEquiv e (outCyc_of_card_dvd (m := 1) odd_one ?_)
  rw [h1]
  exact one_dvd _

theorem outCyc_goldschmidtJ1
    {L : Type} [Group L] (e : L ≃* goldschmidtJ1) : OutCyc L :=
  outCyc_j1 (e.trans goldschmidtJ1_exact_model_equiv)

end J1

section Ree

theorem outCyc_ree_model
    {L : Type} [Group L] [Finite L] {f : ℕ} (h : ReeTitsModel L .twistedG2 3 f) : OutCyc L := by
  haveI := finite_outer L
  have ho := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case h).1
  have hne : Nat.card (Outer L) ≠ 0 := Nat.card_pos.ne'
  exact outCyc_of_card_dvd (odd_of_ordProj_two_eq_one hne ho) (dvd_mul_left _ _)

end Ree

section ReeOrder


theorem outCyc_ree_order {L : Type} [Group L] [Finite L] [IsSimpleGroup L] {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card L = ordRee (3 ^ (2 * m + 1))) : OutCyc L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨hnonab, -, hTc, -⟩ :=
    CFSG.Goldschmidt.GoldType.sylow_of_ree_or_j1 (K := L) (Or.inl ⟨m, hm, hcard⟩) T
  rcases CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models L hnonab T hTc with
    ⟨f, hf, hmod⟩ | ⟨p, f, hp, hp2, hf, -, h8, hmod⟩ | ⟨f, -, -, hmod⟩ | hJ
  · obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 f) 2 f
      (by omega) (GaloisField.card 2 f (by omega)) hmod
    exact outCyc_psl2_even hf e
  · haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField p f) p f
      (by omega) (GaloisField.card p f (by omega)) hmod
    exact outCyc_psl2_odd (hp.odd_of_ne_two hp2) (by omega) h8 e
  · exact outCyc_ree_model (LieModel.reeTitsModel hmod (by decide)).2
  · obtain ⟨e⟩ := hJ
    exact outCyc_j1 e

end ReeOrder

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.GOC
