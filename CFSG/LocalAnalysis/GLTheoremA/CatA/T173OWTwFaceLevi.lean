module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceFactor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceEmb

import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceDiag
import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_leviFactor_sl3 {F : Type} [Field F] [Finite F]
    {i j : Fin TwistTag.E6.tag.rank} (hij : i ≠ j)
    (hcij : Tag.cartan .E6 i j = -1) (hcji : Tag.cartan .E6 j i = -1)
    (hk : ∃ k : Fin TwistTag.E6.tag.rank,
      ¬ (3 : ℤ) ∣ Tag.cartan .E6 i k + 2 * Tag.cartan .E6 j k) :
    ∃ f : LeviFactor F 3 ({i, j} : Set (Fin TwistTag.E6.tag.rank)),
      ∀ c : F, f.ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F i c ∧
        f.ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F i c ∧
        f.ι (CFSG.Timmesfeld.tv 1 2 c) = xUnit TwistTag.E6.tag F j c ∧
        f.ι (CFSG.Timmesfeld.tv 2 1 c) = yUnit TwistTag.E6.tag F j c := by
  obtain ⟨ι, hιinj, hιrange, hιval⟩ := exists_sl3_e6pair (F := F) hij hcij hcji hk
  exact ⟨{ ι := ι
           injective := hιinj
           range_eq := hιrange
           diag_conj := fun b => exists_diag_conj_sl3 ι hιval b
           diag_mem := fun h hh => mem_range_rootDiagUnitHom_of_diag_sl3 ι hιval hh },
    hιval⟩

theorem exists_leviFactor_sl2 {F : Type} [Field F] [CharP F 2] (k : Fin TwistTag.E6.tag.rank) :
    ∃ f : LeviFactor F 2 ({k} : Set (Fin TwistTag.E6.tag.rank)),
      ∀ c : F, f.ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F k c ∧
        f.ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F k c := by
  let ι : Matrix.SpecialLinearGroup (Fin 2) F →* ModGL TwistTag.E6.tag F :=
    simpleRootSL2 TwistTag.E6.tag F k
  have hιval : ∀ c : F, ι (CFSG.Timmesfeld.tv 0 1 c) = xUnit TwistTag.E6.tag F k c ∧
      ι (CFSG.Timmesfeld.tv 1 0 c) = yUnit TwistTag.E6.tag F k c :=
    fun c => simpleRootSL2_tv k c
  exact ⟨{ ι := ι
           injective := CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo k
           range_eq := range_simpleRootSL2_eq_subsystemGroup k
           diag_conj := fun b => exists_diag_conj_sl2 ι hιval b
           diag_mem := fun h hh => mem_range_rootDiagUnitHom_of_diag_sl2 ι hιval hh },
    hιval⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
