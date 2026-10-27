module

public import Certificates.Certificate9708
public import Certificates.Certificate9709
public import Certificates.Certificate9710
public import CFSG.LieType.SeitzGeneration.HeisSmallCases
public import CFSG.LieType.SeitzGeneration.OuterSmallSound

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

open CFSG.LocalAnalysis.ComponentInitial

theorem outerB12AtCard_five : OuterB12AtCard 5 := by
  intro ℓ f K _ h hq ω α hω hα hαc
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]; norm_num
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q5) h hq3 (by rw [card_q5, hq])
    isPrimitiveRoot_omega hω
  exact outerB12_le_of_check h ι hι hιω hq hα hαc Certificates.certificate9708

theorem outerB12AtCard_eight : OuterB12AtCard 8 := by
  intro ℓ f K _ h hq ω α hω hα hαc
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]; norm_num
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h hq3 (by rw [card_q8, hq])
    isPrimitiveRoot_omega hω
  exact outerB12_le_of_check h ι hι hιω hq hα hαc Certificates.certificate9709

theorem outerB12AtCard_eleven : OuterB12AtCard 11 := by
  intro ℓ f K _ h hq ω α hω hα hαc
  have hq3 : 3 ∣ ℓ ^ f + 1 := by rw [hq]; norm_num
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q11) h hq3 (by rw [card_q11, hq])
    isPrimitiveRoot_omega hω
  exact outerB12_le_of_check h ι hι hιω hq hα hαc Certificates.certificate9710

end CFSG.LieType.SeitzGeneration.HeisSmall
