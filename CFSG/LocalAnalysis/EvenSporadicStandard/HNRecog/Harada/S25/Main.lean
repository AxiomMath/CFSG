module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.Joint
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.SplusBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMATop
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Top24
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Transport27
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Transport3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma23
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Transport2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.S25

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem nonabelian_of_hData {G : Type} [Group G] [Finite G] {t z b z₁ : G}
    {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}
    (hD : HData G t z b z₁ S Eg T T' W0 ι) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hab
  push_neg at hab
  have hcent : centralizer (ι.range : Set G) = ⊤ := by
    refine top_unique fun x _ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  have hG : (⊤ : Subgroup G) ≤ ι.range := hcent ▸ hD.centralizer_le
  have h64 : Nat.card (Elem2 6) = 64 := by
    rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin 6 → ZMod 2) ≃ Elem2 6)]
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hA : Nat.card ι.range ≤ 64 :=
    h64 ▸ Nat.le_of_dvd (by rw [h64]; norm_num) (Subgroup.card_range_dvd ι)
  have hGle : Nat.card G ≤ Nat.card ι.range := by
    calc Nat.card G = Nat.card (⊤ : Subgroup G) := Subgroup.card_top.symm
      _ ≤ Nat.card ι.range := Subgroup.card_le_of_le hG
  have hH : Nat.card (centralizer ({t} : Set G)) ≤ Nat.card G :=
    Subgroup.card_le_card_group _
  have hcard := hD.card_H
  omega

theorem setting25Exists_of_interfaceAll (hI : HaradaInterfaceAll) (hGH : GH73.GH73TheoremA64K) :
    Setting25Exists := by
  intro G _ _ _ hK t ht E hE
  obtain ⟨a, z, b, z₁, S, T, T', W0, ι, zv, R0, F, hF⟩ :=
    hI ↥(centralizer ({t} : Set G)) E hE
  have hD := hF.toHaradaFacts.toHData ht hE
  have hD2 := hF.toHaradaFacts2.toHData2
  have hD3 := hF.toHaradaFacts3.toHData3 ht
  have hnonab := nonabelian_of_hData hD
  refine ⟨(z : G), (z₁ : G), (centralizer ({t} : Set G)).subtype.comp ι, zv,
    R0.map (centralizer ({t} : Set G)).subtype, F.map (centralizer ({t} : Set G)).subtype, ?_⟩
  rcases harada_lemma_2_3 hnonab hD with ⟨hX, hΩ⟩ | hplus
  · have hS := Setting25.of_hData hD hD2 hΩ hX
    exact ⟨hS, hS.not_isConj_t_z hX, hS.isConj_t_mul_z hX, hF.toHaradaFacts27.toCzS5,
      hF.splus.facts210⟩
  · exact absurd hplus (harada_lemma_2_4 hnonab hK hGH hD hD3)

end CFSG.EvenSporadicStandard.HNRecog.Harada.S25
