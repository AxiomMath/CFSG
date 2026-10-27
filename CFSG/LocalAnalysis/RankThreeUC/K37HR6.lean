module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRGlue
public import CFSG.RankThree.PartOne.N143.O7
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)
open CFSG.Assembly.RankThreeEven (localRank)
open TauCeti

theorem k37Rest₆_holds : K37Rest₆ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨d, hc, q, hq3, hd⟩ := hO
  obtain ⟨φ, hφ, hker, h3, hodd⟩ := k37R_exists_cover hs.core hc
  obtain ⟨dd, hv⟩ := d
  obtain rfl : dd = .B 3 q := hd
  obtain ⟨hp3, -⟩ := CFSG.RankThree.PartOne.N143.primePower_eq_three hq3
  have hp2 : q.p ≠ 2 := by omega
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl
    (G := (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) (MulEquiv.refl _)
  obtain ⟨-, Kf, _, _, hK3, ⟨eK⟩⟩ := hmodel
  have hK : Nat.card Kf = 3 := by rw [hK3, ← PrimePower.card_def]; exact hq3
  let e' : (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group ≃* ↥CFSG.RankThree.PartOne.N143.O7.Om :=
    eK.trans (CFSG.RankThree.PartOne.N143.O7.modelEquiv hK)
  let φ' : ↥K →* ↥CFSG.RankThree.PartOne.N143.O7.Om := e'.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := e'.surjective.comp hφ
  have hkerφ : φ'.ker = φ.ker := by
    ext x
    simp [φ', MonoidHom.mem_ker]
  have h4 := CFSG.RankThree.PartOne.N143.O7.four_le_localRank_of_cover φ' hφ'
    (hkerφ ▸ hker ▸ le_rfl) (hkerφ ▸ h3)
  exact k37R_false_of_four_le_localRank hs h4

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
