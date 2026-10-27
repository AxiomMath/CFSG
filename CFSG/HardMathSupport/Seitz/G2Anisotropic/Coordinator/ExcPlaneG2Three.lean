module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies

public section

open CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti CFSG.LieType.SeitzGeneration

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator


theorem rankLE2_three_cat_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (h3 : 3 ≠ q.p) : RankLE2 3 (Cat ⟨LieTypeIndex.G2 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three h3
  exact RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_three_adjointGroup_G2 K hK3)

theorem excPlaneG2Three : ExcPlaneG2Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨q, rfl⟩, rfl⟩ hr
  exact absurd (rankLE2_three_cat_G2 q hv (by simpa using hpd)) hr

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
