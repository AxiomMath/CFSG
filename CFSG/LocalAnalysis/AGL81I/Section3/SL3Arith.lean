module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
  (ThreeTenSl3Order ThreeTenTorusExclusion threeTenSl3Order_of_isPGroup
    dvd_p_add_one_of_sl3Data)

theorem isPSLType_of_mulEquiv {n : ℕ} {F : Type} [CommRing F] {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsPSLType n F X) : IsPSLType n F Y :=
  Nonempty.map (fun e' => e.symm.trans e') h

theorem threeTenSl3Order_of_isSL3 {H : Type} [Group H] [Finite H] {p d : ℕ} (hp : p.Prime)
    (hd : d.Prime) {I D : Subgroup H} (hSL3 : IsSLType 3 (ZMod p) ↥I) (hDI : D ≤ I)
    (hDne : D ≠ ⊥) (hD : IsPGroup d D) : ThreeTenSl3Order p d := by
  have hDne' : D.subgroupOf I ≠ ⊥ := by
    intro hbot
    apply hDne
    have hmap := Subgroup.map_subgroupOf_eq_of_le hDI
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hD' : IsPGroup d (D.subgroupOf I) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDI).symm
  exact threeTenSl3Order_of_isPGroup hp hd hSL3 hDne' hD'

theorem dvd_p_add_one_of_isSL3 {H : Type} [Group H] [Finite H] {p d : ℕ} (hp : p.Prime)
    (hd : d.Prime) (hdp : d ≠ p) {I D : Subgroup H} (hSL3 : IsSLType 3 (ZMod p) ↥I)
    (hDI : D ≤ I) (hDne : D ≠ ⊥) (hD : IsPGroup d D) (htor : ThreeTenTorusExclusion p d) :
    d ∣ p + 1 :=
  dvd_p_add_one_of_sl3Data hp hd hdp
    (threeTenSl3Order_of_isSL3 hp hd hSL3 hDI hDne hD) htor

end CFSG.LocalAnalysis.AGL81I.Section3
