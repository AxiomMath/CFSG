module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204U3Bridge
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export

theorem kdL64I204U3_holds :
    KDL64I204U3 := by
  intro p hp hp5 Z _ _ L hLn hU3 hC B hB _ hSC W hBW hW
  have hp2 : p ≠ 2 := by omega
  have hH : Chev204Hyp p L B := chev204Hyp_of_U3p hp hp5 hLn hU3 hC hB hSC
  have hXc : ¬ ChevExc p L B := by
    rintro ⟨h3, -⟩
    omega
  have hA : ∀ q : ℕ, q.Prime → q ≠ 2 → KDAmbSolv q := fun q hq hq2 =>
    kdAmbSolv_holds hq hq2 u42_fixSubgroup_solvable
  have hDC := defCharInnerCoreFree_holds
  have hOut : DefCharOuterCoreFree :=
    defCharOuterCoreFree_of_kdata (kdOutCoreFree_of_outerCent outerCentAll_holds)
      (kdOutCentInner_of_outerCent outerCentAll_holds)
  have hK65 := kd65_holds hp hp2
  have hKD := kdChevInner_of hp hp2 (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hp hp2)
    (hA p hp hp2)
  have hCent : ChevCentralizerStep :=
    chevCentralizerStep_of_kdata
      (fun q hq hq2 => kdChevUnique_of hq hq2 (CFSG.HardMathSupport.Dickson.KD.kdCharP_holds hq hq2)
        (kdOutChevUnique_of_outerCent outerCentAll_holds hq hq2) (hA q hq hq2))
      (fun q hq hq2 => kdOutChev_of_outerCent outerCentAll_holds hq hq2)
      (kdOutExc_of_outerCent outerCentAll_holds (hA 3 Nat.prime_three (by norm_num)))
  have hCyc : ChevCyclicCase :=
    chevCyclicCase_of_nineFold CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      (fun q hq hq2 => kd65_holds hq hq2) kdU43NineFold_holds
  have hAmb : ChevAmbCase := chevAmbCase_holds
  have hSB : IsStronglyBalancedIn p B L :=
    chev204_induction hDC hOut hK65 hKD hCent hCyc hAmb (Nat.card Z) Z rfl L B hH hXc
  have hWN : W ≤ Subgroup.normalizer (L : Set Z) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hLn]
    exact le_top
  have hWcop : Nat.Coprime p (Nat.card W) :=
    (Nat.Coprime.coprime_dvd_right (dvd_mul_left p 2) hW).symm
  have hBW' : B ⊓ Subgroup.normalizer (L : Set Z) ≤ Subgroup.normalizer (W : Set Z) :=
    fun x hx => hBW hx.1
  have hWC : W ≤ Subgroup.centralizer (L : Set Z) := hSB W hWN hWcop hBW'
  rw [hC] at hWC
  exact le_bot_iff.1 hWC

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
