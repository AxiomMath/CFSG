module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

theorem up34AltLeaf_holds : Up34AltLeaf := by
  intro S _ _ n hn ⟨e⟩ α hpump
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := hpump
  let ψ : MulAut (alternatingGroup (Fin n)) := MulAut.congr e α
  have hψ3 : ψ ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hψ1 : ψ ≠ 1 := by
    intro h1
    exact hα1 ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  have hker : (e : S →* alternatingGroup (Fin n)).ker ≤ Subgroup.center S := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨A, hA, hAT⟩ := isLThreeFour_barOf_of_central (e : S →* alternatingGroup (Fin n))
    e.surjective hker α ψ (fun y => by simp [ψ, MulAut.congr_apply]) hI hI34
  obtain ⟨m, hm5, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn Nat.prime_three (by decide) ψ hψ3 hψ1 A hA
  obtain ⟨hsimp, hnab⟩ := isSimpleGroup_of_isLThreeFour hAT
  have hcen : Subgroup.center (barOf 3 A) = ⊥ := up34_center_eq_bot_of_simple hnab
  let e2 : PSimple 3 A ≃* barOf 3 A :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hAlt' : CFSG.ComponentClassification.CatLeaf.IsAltType (barOf 3 A) :=
    ⟨Fin m, inferInstance, inferInstance, by simpa using (le_trans (le_max_left 5 3) hm5),
      ⟨e2.symm.trans f⟩⟩
  exact CFSG.ComponentClassification.CatLeaf.not_isL34Type_of_isAltType hAlt'
    (isL34Type_of_isLThreeFour hAT)

end CFSG.HardMathSupport.Dickson.Sec6
