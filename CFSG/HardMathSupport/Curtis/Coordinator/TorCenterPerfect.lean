module

public import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterNode
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

theorem three_dvd_four_pow_sub_one (e : ℕ) : 3 ∣ 4 ^ e - 1 := by
  have := Nat.sub_dvd_pow_sub_pow 4 1 e
  rw [one_pow] at this
  exact (show 3 ∣ 4 - 1 by norm_num).trans this

theorem exists_perfect_three_dvd_of_compParab {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hP : CompParab L J) {e : ℕ} (he : 2 ≤ e)
    (ι : ↥L ⧸ Subgroup.center ↥L ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 e)) :
    ∃ W : Subgroup Y, W ≤ J ∧ ⁅W, W⁆ = W ∧ 3 ∣ Nat.card W := by
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  have hF4 : 4 ≤ Nat.card (GaloisField 2 e) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  set ψ := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  have hker : ψ.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hsurj : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  obtain ⟨T, hT, hNJ, hneB⟩ := exists_isSylowTwoOf_normalizer_lt_subgroupOf hP
  obtain ⟨T', hNJ', hneB'⟩ := exists_sylow_normalizer_lt_map ψ hsurj hker.le
    (by rw [hker]; exact hP.odd) hT hNJ hneB
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 e) ≃*
      (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (GaloisField 2 e)).trans ι.symm
  obtain ⟨V, hVJ, hV, hVcard⟩ := exists_sl2_perfect_of_borelQuotient (borelQuotient_sl e') hF4
    (fun i => hasSL2Node_sl i) T' ((J.subgroupOf L).map ψ) hNJ' hneB'
  obtain ⟨W₀, hW₀, hW₀le, hW₀map⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker.le hV
    (by rw [MonoidHom.range_eq_top.2 hsurj]; exact le_top)
  have hkJ : ψ.ker ≤ J.subgroupOf L :=
    hker.le.trans ((Subgroup.center_le_normalizer (T : Set ↥L)).trans hNJ)
  have hcomap : ((J.subgroupOf L).map ψ).comap ψ = J.subgroupOf L :=
    Subgroup.comap_map_eq_self hkJ
  have hW₀J : W₀ ≤ J.subgroupOf L :=
    hW₀le.trans (by rw [← hcomap]; exact Subgroup.comap_mono hVJ)
  refine ⟨W₀.map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hW₀J hx)
  · rw [← Subgroup.map_commutator, hW₀]
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    have h3 : 3 ∣ Nat.card V := by
      rw [hVcard, CFSG.AGLEmbedding.ParabPrime.card_sl2, hF, ← pow_mul]
      refine Dvd.dvd.mul_left ?_ _
      have h4 : (2 : ℕ) ^ (e * 2) = 4 ^ e := by rw [pow_mul']; norm_num
      rw [h4]
      exact three_dvd_four_pow_sub_one e
    rw [← hW₀map] at h3
    exact h3.trans (Subgroup.card_map_dvd W₀ ψ)

end CFSG.HardMathSupport.Curtis.Coordinator
