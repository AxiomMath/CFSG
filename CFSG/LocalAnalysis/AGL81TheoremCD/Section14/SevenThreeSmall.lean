module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.Adapters.LieModelOrders
import CFSG.HardMathSupport.Solomon.Coordinator.ONCSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeIdInvolve

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree

theorem exists_orderOf_nine_alternatingGroup_nine :
    ∃ x : alternatingGroup (Fin 9), orderOf x = 9 := by
  have hmem : finRotate 9 ∈ alternatingGroup (Fin 9) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
    norm_num
  refine ⟨⟨finRotate 9, hmem⟩, ?_⟩
  rw [Subgroup.orderOf_mk, (isCycle_finRotate_of_le (by norm_num)).orderOf,
    support_finRotate_of_le (by norm_num), Finset.card_univ, Fintype.card_fin]

theorem card_alternatingGroup_nine_dvd_card {Y : Type} [Group Y] [Finite Y] {I : Subgroup Y}
    (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f) : 181440 ∣ Nat.card Y := by
  have h1 : Nat.card (alternatingGroup (Fin 9)) ∣ Nat.card ↥I :=
    Subgroup.card_dvd_of_surjective hf
  have hcard : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [hcard] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card I)

private theorem isHatON_of_threeCover_onan
    {Y : Type} [Group Y]
    (hY : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Z _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Z .ONan) Y) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsHatON Y := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hY
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  exact ⟨hq.1, hZ, ⟨e.trans b'⟩⟩

theorem orderOf_ne_nine_of_threeCover_onan
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Z _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Z .ONan) Y) (g : Y) :
    orderOf g ≠ 9 := by
  have hHat := isHatON_of_threeCover_onan hY
  intro hg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hgQ : g ∈ (Q : Subgroup Y) := hQ (Subgroup.mem_zpowers g)
  have h3 : g ^ 3 = 1 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.inputONSylow_holds Y hHat Q).2.1 g hgQ
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at hdvd
  exact absurd hdvd (by decide)

theorem false_of_threeCover_onan
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Z _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Z .ONan) Y)
    (I : Subgroup Y) (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f) : False :=
  CFSG.AGLEmbedding.not_surjective_of_no_orderOf_nine
    (orderOf_ne_nine_of_threeCover_onan hY) I f hf exists_orderOf_nine_alternatingGroup_nine

theorem false_of_lieModel_l2_27_or_psp4_3 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 2 3 3 ∨ CFSG.Blueprint.LieModel Y .PSp 2 3 1)
    (I : Subgroup Y) (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f) : False := by
  have hdvd := card_alternatingGroup_nine_dvd_card f hf
  have hpsl : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 2 (3 ^ 3) = 9828 := by decide
  have hpsp : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (3 ^ 1) = 25920 := by decide
  rcases hY with h | h
  · have hc : Nat.card Y = 9828 := by
      rw [h.card_eq_lieOrd (by norm_num), hpsl]
    rw [hc] at hdvd
    exact absurd hdvd (by decide)
  · have hc : Nat.card Y = 25920 := by
      rw [h.card_eq_lieOrd (by norm_num), hpsp]
    rw [hc] at hdvd
    exact absurd hdvd (by decide)

theorem false_of_isSpor_j3 {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .J3)
    (I : Subgroup Y) (f : ↥I →* alternatingGroup (Fin 9)) (hf : Function.Surjective f) : False := by
  have hdvd := card_alternatingGroup_nine_dvd_card f hf
  obtain ⟨e⟩ := hY
  have hcard : Nat.card Y = 50232960 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  rw [hcard] at hdvd
  exact absurd hdvd (by decide)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree
