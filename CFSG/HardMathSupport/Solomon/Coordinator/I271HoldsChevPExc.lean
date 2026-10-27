module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNN

public section

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  GL83 GL83.CompFam

namespace CFSG.HardMathSupport.Solomon.Coordinator

section ChevPExc

theorem i271ChevPExc_holds : I271ChevPExc := by
  intro X _ _ hXK K B hH hNorm h27 hinn
  obtain ⟨hBN, hAut⟩ := hNorm
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  have hOK : GLAPPrimeCore 3 ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h27
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    let π : ↥K →* CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : π.ker = Subgroup.center ↥K := by
      ext x
      simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hodd : Odd (Nat.card π.ker) := by
      rw [hker]
      exact odd_card_center Nat.prime_three (by norm_num) hOK
    have := (CFSG.SectionRank.OddCover.odd_psl_two_perfect_odd_cover_kernel (p := 3) (f := 3)
      (by norm_num) (by rw [hF]; norm_num) π hπs hker.le hodd).1 (by norm_num)
    rw [← hker]
    exact this
  have hS : IsLTwoTwentySeven ↥K :=
    ⟨F, inferInstance, inferInstance, hF,
      ⟨((QuotientGroup.quotientBot (G := ↥K)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩⟩
  have hgen := hyperplane_gen_of_plane l2FieldPlane_holds hBel (Or.inl hS) hinn
    (by simpa using hAut)
  exact nn_caseA_of_hyperplane hH.comp hBel hH.rank_four (one_le_pRank_inf_normalizer hH) hgen

end ChevPExc

end CFSG.HardMathSupport.Solomon.Coordinator
