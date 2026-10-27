module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld
open CFSG.LieType.SemisimpleCentralizers.HeldLang (card_fixField)

theorem fieldLinComp3_holds : FieldLinComp3 := by
  intro d K _ _ h2 hd u f hu hf hf3 huf3 hfne J hJ
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨A, σ, c, hσord, hg, hstep⟩ := uf_structure hd u f hu hf hf3 huf3 hfne
  obtain ⟨Y, hYC, hYn, hCY, ⟨eY⟩⟩ := lang_fixed hd A σ c hg (u * f) hstep
  haveI : IsSimpleGroup (StatedProj (StatedSL d ↥(CFSG.LieType.SemisimpleCentralizers.HeldLang.fixField σ))) :=
    isSimpleGroup_statedProj_of_three_le hd _
  haveI : Group.IsPerfect (StatedProj (StatedSL d ↥(CFSG.LieType.SemisimpleCentralizers.HeldLang.fixField σ))) :=
    isPerfect_statedProj_of_three_le hd _
  haveI hsimp : IsSimpleGroup ↥Y := eY.isSimpleGroup
  haveI hperf : Group.IsPerfect ↥Y :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  have hJY : J = Y := component_eq_of_fixed hJ hYC hYn hCY
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcardK⟩ := FiniteField.card K 2
  have hKc : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hF := card_fixField Nat.prime_two hn hKc σ
  rw [hσord] at hF
  subst hJY
  refine ⟨d, (n : ℕ) / 3, ↥(CFSG.LieType.SemisimpleCentralizers.HeldLang.fixField σ), inferInstance,
    inferInstance, by omega, ?_, ?_⟩
  · rw [hF]
  · exact nonempty_quotCenter_equiv eY

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
