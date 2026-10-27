module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Lie
public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Spor

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

section Main


theorem no5PumpupAt_of_BM (hBM : NoOrderSixtyFiveBM) : No5PumpupAt := by
  intro Y _ _ hY hnab hK y hy J hJ hcat
  obtain ⟨i, hi, ⟨eC⟩⟩ := hcat
  have hi' : i = TauCeti.CFSGIndex.sporadic .Co1 := hi
  subst hi'
  have hcard : Nat.card (PSimple 5 J) = CFSG.Open.orderCo1 :=
    (Nat.card_congr eC.toEquiv).trans No5.card_co1
  have hC : Nonempty (PSimple 5 J ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) := ⟨eC⟩
  obtain ⟨i2, ⟨eY⟩⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isCatalogGroup_of_isKGroup_of_surjective
      hK (⊤ : Subgroup Y) hnab (Subgroup.topEquiv (G := Y)).toMonoidHom
      (Subgroup.topEquiv (G := Y)).surjective
  cases i2 with
  | cyclic p hp =>
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (eY.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn => exact No5.no5_alt hY hnab hn eY hy hJ hcard
  | lie idx => exact No5.no5_lie hY hnab idx eY hy hJ hC
  | sporadic s => exact No5.no5_spor s eY hBM hy hJ hcard

end Main

end CFSG.LocalAnalysis.GLTheoremA
