module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsL34
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7d
import CFSG.LargeExtraspecial.S8CBFOut
import CFSG.LargeExtraspecial.S8CorBStatement

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LargeExtraspecial.S8
  (conjOuterCenterQuot mem_sup_centralizer_of_conjOuterCenterQuot_eq_one)

theorem kFactNormalComplement_holds : KFactNormalComplement := by
  intro X _ _ hX J hJ hJnorm q hq hq2 hqJ
  haveI : J.Normal := hJnorm
  let S := ↥J ⧸ Subgroup.center ↥J
  haveI hSsimple : IsSimpleGroup S := hJ.1.2.1
  have hnonab : ∃ a b : S, a * b ≠ b * a := hJ.1.2.2
  have hcat : CFSG.Open.IsCatalogGroup S :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hX J hnonab
      (QuotientGroup.mk' (Subgroup.center ↥J))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have hdvdJS : Nat.card S ∣ Nat.card ↥J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Subgroup.center ↥J)]
    exact dvd_mul_right _ _
  have hqS : ¬ q ∣ Nat.card S := fun h => hqJ (h.trans hdvdJS)
  have hout : CFSG.HasNormalPComplement q (Outer S) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.resOddTrivial_of_lie
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7d.resOddTrivialLie_holds
      q hq hq2 S hSsimple hnonab hcat hqS
  let φ : X →* Outer S := conjOuterCenterQuot J
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  obtain ⟨K₀, hK₀norm, hK₀cop, hK₀q⟩ := hout
  haveI : K₀.Normal := hK₀norm
  let H : Subgroup X := J ⊔ Subgroup.centralizer (J : Set X)
  haveI : (Subgroup.centralizer (J : Set X)).Normal := Subgroup.normal_centralizer
  have hHnorm : H.Normal := by
    dsimp only [H]
    exact Subgroup.sup_normal J _
  haveI : H.Normal := hHnorm
  have hker_le : φ.ker ≤ H := by
    intro x hx
    exact mem_sup_centralizer_of_conjOuterCenterQuot_eq_one J hJperf
      (MonoidHom.mem_ker.mp hx)
  let N₀ : Subgroup X := K₀.comap φ
  have hN₀norm : N₀.Normal := by
    dsimp only [N₀]
    exact Subgroup.Normal.comap hK₀norm φ
  haveI : N₀.Normal := hN₀norm
  let N : Subgroup X := N₀ ⊔ H
  have hNnorm : N.Normal := by
    dsimp only [N]
    exact Subgroup.sup_normal N₀ H
  haveI : N.Normal := hNnorm
  have hHN : H ≤ N := by
    dsimp only [N]
    exact le_sup_right
  have hN₀N : N₀ ≤ N := by
    dsimp only [N]
    exact le_sup_left
  refine ⟨N, hNnorm, hHN, ?_, ?_⟩
  · have hrel : H.relIndex N = H.relIndex N₀ := by
      dsimp only [N]
      exact Subgroup.relIndex_sup_right N₀ H
    have hdvd1 : H.relIndex N₀ ∣ φ.ker.relIndex N₀ :=
      Subgroup.relIndex_dvd_of_le_left N₀ hker_le
    have hrelKer : φ.ker.relIndex N₀ = Nat.card (N₀.map φ) :=
      Subgroup.relIndex_ker N₀ φ
    have hmap_le : N₀.map φ ≤ K₀ := by
      rintro _ ⟨x, hx, rfl⟩
      dsimp only [N₀] at hx
      exact hx
    have hdvd2 : Nat.card (N₀.map φ) ∣ Nat.card K₀ :=
      Subgroup.card_dvd_of_le hmap_le
    have hqK₀ : ¬ q ∣ Nat.card K₀ :=
      (Nat.Prime.coprime_iff_not_dvd hq).mp hK₀cop
    have hdvd : H.relIndex N ∣ Nat.card K₀ := by
      rw [hrel]
      exact hdvd1.trans (hrelKer ▸ hdvd2)
    exact fun h => hqK₀ (h.trans hdvd)
  · have hφbar : Function.Injective
        (QuotientGroup.map N₀ K₀ φ (le_rfl : N₀ ≤ K₀.comap φ)) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_map]
      simpa [N₀] using QuotientGroup.map_mk'_self N₀
    have hN₀q : IsPGroup q (X ⧸ N₀) :=
      IsPGroup.of_injective hK₀q
        (QuotientGroup.map N₀ K₀ φ (le_rfl : N₀ ≤ K₀.comap φ)) hφbar
    have hsurj : Function.Surjective
        (QuotientGroup.map N₀ N (MonoidHom.id X) hN₀N) :=
      QuotientGroup.map_surjective_of_surjective N₀ N (MonoidHom.id X)
        (by simpa using QuotientGroup.mk'_surjective N) hN₀N
    exact IsPGroup.of_surjective hN₀q
      (QuotientGroup.map N₀ N (MonoidHom.id X) hN₀N) hsurj

theorem zkFacts_holds : ZKFacts :=
  zkFacts_of_normalComplement kFactNormalComplement_holds

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
