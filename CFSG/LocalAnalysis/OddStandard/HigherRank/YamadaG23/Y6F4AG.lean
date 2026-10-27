module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.G23Facts

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three

theorem y6f4a_no_z4cube_aut_g23 (hG : G23Facts) {Q : Type} [Group Q] [Finite Q] (hQ : HRG23 Q)
    {M : Type} [Group M] (hM : Nonempty (M ≃* (Fin 3 → Multiplicative (ZMod 4))))
    (ρ : M →* MulAut Q) (hρ : Function.Injective ρ) : False := by
  haveI : IsMulCommutative M :=
    IsMulCommutative.of_comm fun a b =>
      hM.some.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hcommR : IsMulCommutative ρ.range := Subgroup.range_isMulCommutative ρ
  have hcardR : Nat.card ρ.range = 64 := by
    rw [(Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm]
    rw [Nat.card_congr hM.some.toEquiv]
    rw [Nat.card_fun, Nat.card_fin]
    have h4 : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [← Nat.card_congr (Multiplicative.ofAdd : ZMod 4 ≃ Multiplicative (ZMod 4))]
      rw [Nat.card_zmod]
    rw [h4]
    norm_num
  have h2 : IsPGroup 2 ↥ρ.range :=
    IsPGroup.of_card (n := 6) (by rw [hcardR]; norm_num)
  obtain ⟨P, hRP⟩ := IsPGroup.exists_le_sylow h2
  obtain ⟨fr, hfr, hfacts⟩ := hG Q hQ P
  obtain ⟨_, _, _, _, h15, _⟩ := hfacts
  obtain ⟨_, _, _, _, h5, _⟩ := h15
  have hRS : ρ.range ≤ fr.Sσ := by rw [hfr]; exact hRP
  have hle : Nat.card ↥ρ.range ≤ 16 := h5 ρ.range hRS hcommR
  rw [hcardR] at hle
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
