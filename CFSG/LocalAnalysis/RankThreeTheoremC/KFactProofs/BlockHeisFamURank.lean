module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamURankWeir

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

theorem heisURankFacts_holds :
    HeisURankFacts := by
  intro L _ _ hperf hodd hrk hsimple n f K _ _ hK hn hf e p hp hp5
  obtain ⟨ρ, hρ, hZ⟩ := heisU_exists_cover hperf hodd hsimple hK hn e
  obtain ⟨hZdvd, hkerdvd⟩ := heisU_card_center_dvd hK (by omega) ρ hρ hZ
  by_cases hdiv : p ∣ Nat.gcd n (2 ^ f + 1)
  · exact Or.inr (heisU_exception hrk hK hf hn hp hp5 hdiv ρ hρ hZ)
  · have hker : ¬ p ∣ Nat.card ρ.ker := fun h => hdiv (h.trans hkerdvd)
    exact Or.inl ⟨hdiv, heisU_div_lt hrk hK hf hp hp5 ρ hker, fun h => hdiv (h.trans hZdvd)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
