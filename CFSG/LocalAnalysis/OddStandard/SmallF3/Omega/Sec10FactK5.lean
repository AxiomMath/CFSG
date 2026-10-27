module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Rank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Iface
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactAutK5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82FactRankK5_of_struct : Asc82FactRankK5 := by
  intro G _ _ K1 K2 hcomm _ e1 e2 E hE
  obtain ⟨hEc, hE2⟩ := hE
  haveI : IsMulCommutative E := hEc
  refine (K5.sl23Pair_of_commuting K1 K2 hcomm e1 e2).rank_le_sixteen E ?_ ?_
  · intro e he f hf
    exact setLike_mul_comm he hf
  · intro e he
    rw [← pow_two]
    exact hE2 e he

theorem asc82FactAutK5_of_struct : Asc82FactAutK5 := by
  intro G _ _ K1 K2 hcomm _ e1 e2 Φ Ψ hΨΦ hΦ2 hidx hΨ hQ hσ
  have hP := K5.sl23Pair_of_commuting K1 K2 hcomm e1 e2
  have hQ' : ∀ q ∈ CFSG.pCore 2 ↥(K1 ⊔ K2), MulAut.conj q ∈ Ψ := fun q hq =>
    hQ q ((mem_twoCoreIn_iff_pCore q.2).mpr hq)
  obtain ⟨ψ, hψΦ, hψΨ, hψ2, hψA, hψB, hψout⟩ := hP.aut_of_pair Φ Ψ hΨΦ hΦ2 hidx hΨ hQ' hσ
  refine ⟨ψ, hψΦ, hψΨ, hψ2, hψA, hψB, ?_⟩
  rintro ⟨k, hkA, hk⟩
  exact hψout ⟨k, hkA, fun y hy => Subtype.ext (hk y hy)⟩

end CFSG.OddStandard.SmallF3.Omega
