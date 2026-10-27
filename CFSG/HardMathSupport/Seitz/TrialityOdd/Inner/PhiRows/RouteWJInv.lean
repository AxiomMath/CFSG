module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJTorus
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix


section Inv

variable {L : Type} [Field L] [IsAlgClosed L]

theorem monomial_conj_rootDiagUnit {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    n * rootDiagUnit TwistTag.D4.tag a * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag
        (weylTuple (weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩) a) := by
  set v := weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩
  set c := canonicalRep (coxeterSystem TwistTag.D4.tag) L v with hc
  have hh : c * n⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    canonicalRep_mul_inv_mem_torusGroup hn v rfl
  have hh' : n * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    simpa using inv_mem hh
  have hcy : c * rootDiagUnit TwistTag.D4.tag a * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    rw [hc, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm := torusGroup_comm hh' hcy
  calc n * rootDiagUnit TwistTag.D4.tag a * n⁻¹ =
        (n * c⁻¹) * (c * rootDiagUnit TwistTag.D4.tag a * c⁻¹) * (n * c⁻¹)⁻¹ := by group
    _ = c * rootDiagUnit TwistTag.D4.tag a * c⁻¹ := by rw [hcomm, mul_inv_cancel_right]
    _ = _ := canonicalRep_conj_rootDiagUnit v a

theorem jU_inv_eq : jU⁻¹ = jU := by
  rw [jU_eq_simple, CoxeterSystem.inv_simple]

theorem rootChar_jU_smul_zero (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    rootChar b (jU • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ)) = (b 0)⁻¹ := by
  have : jU • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      (![-1, 0, 0, 0] : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [jU, jWordU, wordProd_smul_eq_wordMat_mulVec]
    funext j
    fin_cases j <;> rfl
  rw [this]
  unfold rootChar
  rw [prod_rank_d4]
  simp

theorem jU_smul_single_one :
    jU • (Pi.single 1 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 1 1 := by
  rw [jU, jWordU, wordProd_smul_eq_wordMat_mulVec]
  funext j
  fin_cases j <;> rfl

theorem jU_smul_single_three :
    jU • (Pi.single 3 1 : Fin TwistTag.D4.tag.rank → ℤ) = Pi.single 3 1 := by
  rw [jU, jWordU, wordProd_smul_eq_wordMat_mulVec]
  funext j
  fin_cases j <;> rfl

theorem jRep_inv_conj_comm_of_tuple (b : Fin TwistTag.D4.tag.rank → Lˣ) (h1 : b 1 = (b 0)⁻¹)
    (h3 : b 3 = (b 0)⁻¹) :
    diagramMap TwistTag.D4 L * ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag b * jRep L jU) =
      ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag b * jRep L jU) *
        diagramMap TwistTag.D4 L := by
  have hM : (jRep L jU)⁻¹ ∈ monomialSubgroup TwistTag.D4.tag L := inv_mem (jRep_mem_monomial jU)
  have hW : weylQuotientHom TwistTag.D4.tag L ⟨(jRep L jU)⁻¹, hM⟩ = jU⁻¹ := by
    have : (⟨(jRep L jU)⁻¹, hM⟩ : monomialSubgroup TwistTag.D4.tag L) =
        (⟨jRep L jU, jRep_mem_monomial jU⟩)⁻¹ := rfl
    rw [this, map_inv, weylQuotientHom_jRep]
  have hconj := monomial_conj_rootDiagUnit hM b
  rw [hW, inv_inv] at hconj
  set a' := weylTuple jU⁻¹ b with ha'
  have ha'i : ∀ i, a' i = rootChar b (jU • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) := by
    intro i
    rw [ha', weylTuple, jU_inv_eq, jU_inv_eq]
  have e0 : a' 0 = (b 0)⁻¹ := by rw [ha'i, rootChar_jU_smul_zero]
  have e1 : a' 1 = b 1 := by
    rw [ha'i, jU_smul_single_one, CTTorus.rootChar_single]
  have e3 : a' 3 = b 3 := by
    rw [ha'i, jU_smul_single_three, CTTorus.rootChar_single]
  have hinv : ∀ i, a' (TwistTag.D4.perm.symm i) = a' i := by
    intro i
    fin_cases i
    · show a' 3 = a' 0
      rw [e3, e0, h3]
    · show a' 0 = a' 1
      rw [e0, e1, h1]
    · rfl
    · show a' 1 = a' 3
      rw [e1, e3, h1, h3]
  have hP := diagramMap_pow_conj_rootDiagUnit (L := L) a' 1
  have hfun : (fun i => a' (((TwistTag.D4.perm.symm) ^ 1) i)) = a' := by
    funext i
    simpa using hinv i
  rw [hfun, pow_one, ← hconj] at hP
  have : diagramMap TwistTag.D4 L * ((jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag b * jRep L jU) *
      (diagramMap TwistTag.D4 L)⁻¹ = (jRep L jU)⁻¹ * rootDiagUnit TwistTag.D4.tag b * jRep L jU := hP
  exact mul_inv_eq_iff_eq_mul.1 this

end Inv

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
