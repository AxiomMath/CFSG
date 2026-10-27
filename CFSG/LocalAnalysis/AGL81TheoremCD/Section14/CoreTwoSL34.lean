module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs
public import CFSG.Quasithin.Background.A3Structure312Iso
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
import CFSG.Models.PGLOrders
import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.Quasithin.Background.A3Structure318Star

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalCores
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem isPSL_of_isL34Type {L : Type} [Group L] (hL : IsL34Type L) :
    CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Subgroup.center L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hL
  exact CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ e

private theorem isPSL_centerQuotient_pCore_two_of_isL34Type {K : Type} [Group K]
    [Finite K] (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hL : IsL34Type (K ⧸ CFSG.pPrimeCore 3 K))
    (hO3ne : CFSG.pPrimeCore 3 K ≠ ⊤) :
    CFSG.Quasithin.IsPSL 3 2 2
      ((K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Type := K ⧸ CFSG.pCore 2 K
  let N : Subgroup Y := (CFSG.pPrimeCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))
  let L : Type := K ⧸ CFSG.pPrimeCore 3 K
  have hO2le : CFSG.pCore 2 K ≤ CFSG.pPrimeCore 3 K :=
    CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num)
  have hNle : N ≤ Subgroup.center Y := map_pPrimeCore_three_le_center hq hO3ne
  have eYN : Y ⧸ N ≃* L :=
    QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K)
      (CFSG.pPrimeCore 3 K) hO2le
  let f : Y →* L := eYN.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f :=
    eYN.surjective.comp (QuotientGroup.mk'_surjective N)
  have hfker : f.ker = N := by
    rw [show f = eYN.toMonoidHom.comp (QuotientGroup.mk' N) from rfl,
      MonoidHom.ker_comp_of_injective _ eYN.toMonoidHom eYN.injective,
      QuotientGroup.ker_mk']
  have hcomap : (Subgroup.center L).comap f = Subgroup.center Y :=
    CFSG.LocalCores.comap_center_eq_of_perfect hq.1 f hf (by rw [hfker]; exact hNle)
  let g : Y →* L ⧸ Subgroup.center L := (QuotientGroup.mk' (Subgroup.center L)).comp f
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective (Subgroup.center L)).comp hf
  have hgker : g.ker = Subgroup.center Y := by
    rw [show g = (QuotientGroup.mk' (Subgroup.center L)).comp f from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  have eYCenter : Y ⧸ Subgroup.center Y ≃* L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq hgker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  exact CFSG.Quasithin.IsPSL.of_mulEquiv eYCenter.symm (isPSL_of_isL34Type hL)

theorem pCore_two_eq_pPrimeCore_three_of_isL34Type
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hL : IsL34Type (K ⧸ CFSG.pPrimeCore 3 K)) :
    CFSG.pCore 2 K = CFSG.pPrimeCore 3 K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Type := K ⧸ CFSG.pCore 2 K
  let q : K →* Y := QuotientGroup.mk' (CFSG.pCore 2 K)
  let N : Subgroup Y := (CFSG.pPrimeCore 3 K).map q
  have hO2le : CFSG.pCore 2 K ≤ CFSG.pPrimeCore 3 K :=
    CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num)
  have hker : ¬ 3 ∣ Nat.card q.ker := by
    have hkerq : q.ker = CFSG.pCore 2 K := QuotientGroup.ker_mk' _
    rw [hkerq]
    intro hdvd
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcoreY : CFSG.pPrimeCore 3 Y = N := by
    have hmap := (CFSG.prime_complement_kernel_core_preimage (p := 3) q
      (QuotientGroup.mk'_surjective _) hker).2
    exact hmap.symm
  have hO3ne : CFSG.pPrimeCore 3 K ≠ ⊤ := by
    intro htop
    obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type hL
    have hsub : Subsingleton (K ⧸ CFSG.pPrimeCore 3 K) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    haveI := hsub
    have hcard1 : Nat.card ((K ⧸ CFSG.pPrimeCore 3 K) ⧸
        Subgroup.center (K ⧸ CFSG.pPrimeCore 3 K)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have h20160 : Nat.card ((K ⧸ CFSG.pPrimeCore 3 K) ⧸
        Subgroup.center (K ⧸ CFSG.pPrimeCore 3 K)) = 20160 := by
      rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSL_three_four]
    omega
  have hNle : N ≤ Subgroup.center Y := map_pPrimeCore_three_le_center hq hO3ne
  have hcenterPSL := isPSL_centerQuotient_pCore_two_of_isL34Type hq hL hO3ne
  have hcenterCard : Nat.card (Subgroup.center Y) ∣ 3 :=
    CFSG.Quasithin.H13.S126P31.card_center_dvd_three_of_quotient
      hq.1.commutator_eq_top
      (center_noTwo_of_pCore_two_eq_bot
        (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (p := 2) (H := K)))
      hcenterPSL
  have hNcard : Nat.card N ∣ 3 := (Subgroup.card_dvd_of_le hNle).trans hcenterCard
  have hNcop : Nat.Coprime 3 (Nat.card N) := by
    rw [← hcoreY]
    exact CFSG.pPrimeCore_coprime_card
  have hNbot : N = ⊥ :=
    Subgroup.card_eq_one.mp (hNcop.symm.eq_one_of_dvd hNcard)
  have hO3le : CFSG.pPrimeCore 3 K ≤ CFSG.pCore 2 K := by
    have hmapbot : (CFSG.pPrimeCore 3 K).map q = ⊥ := by
      change N = ⊥
      exact hNbot
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmapbot
  exact le_antisymm hO2le hO3le

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
