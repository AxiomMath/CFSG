module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankLinCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankOrthCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFFRankCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 SFRRank

private theorem inner_core_of_shape : ∀ i : TauCeti.CFSGIndex, onLie I2017LieRankShape i →
    InnerThree i.Group ∧ CoreThree i.Group
  | .lie ⟨d, hv⟩, hi => by
    rcases hi with ⟨N, hN8, -, rfl⟩ | ⟨k, hk, rfl | rfl⟩
    · exact ⟨innerThree_catA (N - 1) (by omega) hv, coreThree_catA (N - 1) (by omega) hv⟩
    · exact ⟨innerThree_catD k hk hv, coreThree_catD k hk hv⟩
    · exact ⟨innerThree_catTwistedD k hk hv, coreThree_catTwistedD k hk hv⟩
  | .cyclic _ _, hi => (hi : False).elim
  | .alternating _ _, hi => (hi : False).elim
  | .sporadic _, hi => (hi : False).elim

theorem i2017LieRank_of_center (hZ : I2017LieRankCenter) : I2017LieRank := by
  intro Q _ _ hQ α J hα _ _ _ hcat
  have hZ3 := hZ Q hQ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  obtain ⟨hinn, hcore⟩ := inner_core_of_shape i hi
  exact exists_elemAb_fix_of_quotient hZ3 (autRankFour_of_inner (center_quotient_center_eq_bot hQ)
    (innerThree_of_mulEquiv e hinn) (coreThree_of_mulEquiv e hcore)) α hα

section Holds

theorem i2017LieRank_holds : I2017LieRank :=
  i2017LieRank_of_center I2017LieRankCenter_holds

end Holds

end CFSG.LocalAnalysis.GLTheoremA

end
