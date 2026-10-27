module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatMod
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatPerfect
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtSZ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39Odd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open Sec3Theta

theorem sec3SHatNormal_of
    (h17 : Step17G24Odd) : Sec3SHatNormal := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  obtain ⟨H, hΩ, hQF, hZQ, hRc⟩ := exists_sec38Hyp_SHat h17 hQ
  obtain ⟨e, b, t, hT⟩ := H.exists_thetaHyp hΩ hQF hRc hZQ
  have hN₁ : nSHat Q₀ Q Zs ≤ H.xsub.N :=
    sec3SHatNormalizer_of h17 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  have hC := hT.closedHyp hN₁ (Sec38Hyp.range_eq_omega h17 H).le
  obtain ⟨T₁, hT₁, hST₁, hcl⟩ := Sec3Closed.exists_sylow_strongly_closed hC
  obtain ⟨N, hN, h6, h7⟩ := hT.exists_goldschmidtN
  have hZ : IsElemAbelian 2 Zs :=
    ⟨isMulCommutative_iff_of_setLike.mpr fun _ ha _ hb => H.comm_of_mem_Zs ha hb,
      fun _ ha => H.sq_eq_one_of_mem_Zs ha⟩
  exact goldschmidtSZ G Zs (sec3SHat (Q₀ ⊔ Q) Zs) T₁ N hZ hC.cardZ hT₁ hST₁ hC.ZS hC.cardS
    hC.commZ hC.sqZ hcl (hN.trans inf_le_left) (hN.trans inf_le_right)
    (fun B hZB hBS _ n => h6 B hZB hBS n) h7

end CFSG.ComponentClassification.AS81
