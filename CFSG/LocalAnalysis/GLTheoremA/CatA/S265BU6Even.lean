module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Tr
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Line
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Card
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6A4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6A5
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU6Fix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Timmesfeld.CrossChar (twistedE6InndiagConj)
open CFSG.LieType.Seitz (fixedPoints mem_fixedPoints)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (twE6MatFixDim)


theorem twE6U6Even_holds : TwE6U6Even := by
  intro Ω _ _ S B T x D K hN hS hKcat hB hTB
  have hp : Nat.Prime 3 := Nat.prime_three
  have hc := hN.cfg
  have hpre := hc.std
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := hc.std
  obtain ⟨v, hv2, hv1, hvB⟩ := exists_fixed_involution_of_qsCfg_twE6 hc hS hB hTB
  have hcK : Nat.card (PSimple 3 K) = 9196830720 :=
    CatDistinct.card_isU6two CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hKcat
  have h3K : 3 ∣ Nat.card K :=
    (show 3 ∣ Nat.card (PSimple 3 K) by rw [hcK]; norm_num).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  obtain ⟨d, hdD, hdx⟩ := S171.exists_y hp hc.x1 hpre
  have hd3 : d ^ 3 = 1 := hpre.2.1.2 d hdD
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc.xcen s)
  have hKd : GLAPComponent 3 (S ⊓ Subgroup.centralizer ({d} : Set Ω)) K := by
    rw [← S171.L_cs_eq hp hc.x1 hpre hdD hdx hSx]
    exact (hN.nlAct h3K).comp
  have hKS : K ≤ S := hKd.1.trans inf_le_left
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  have hdp := isPGroup_zpowers_of_pow_eq_one hd3
  have hβ1 : chevAut 3 S ⟨d, hSN d⟩ ≠ 1 := fun h1 =>
    hdx ((hc.centB d (hpre.1 hdD)).1 ((chevAut_eq_one_iff hp hc.comp (hSN d)).1 h1))
  obtain ⟨F, _, _, σ, hF, hσ, e, h, hh3, hh1, _L, _i, hβe, -, -, hcomp, ⟨e3⟩⟩ :=
    exists_twE6LineModel_of_glaPComponent hS (chevAut_pow_eq_one 3 S (hSN d) hd3) hβ1
      (glaPComponent_chevTransfer hp (hSN d) hdp hKd)
  obtain ⟨e0⟩ := nonempty_pSimple_equiv_chevTransfer hp (hSN d) hdp hKd
  have hcJ : Nat.card (↥((chevTransfer 3 S K).map e.toMonoidHom) ⧸
      Subgroup.center ↥((chevTransfer 3 S K).map e.toMonoidHom)) = 9196830720 := by
    rw [← Nat.card_congr (e0.trans e3).toEquiv]
    exact hcK
  have hdim : twE6MatFixDim F σ h = 36 := by
    rcases twE6MatFixDim_eq_28_or_36_of_card_u6two hF hσ hh3 hh1 hcomp hcJ with h28 | h36
    · have := card_centerQuot_twE6Line_of_dim28 hF hσ hh3 hh1 h28 hcomp
      omega
    · exact h36
  obtain ⟨hZ, hinv⟩ := center_eq_bot_and_involution_mem_of_dim36 hF hσ hh3 hh1 hdim hcomp
  have hfix1 : MulAut.congr e (chevAut 3 S ⟨d, hSN d⟩) (e v) = e v := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hvB d (hpre.1 hdD) (hSN d)]
  rw [hβe] at hfix1
  have hle : Subgroup.zpowers (twistedE6InndiagConj F σ h) ≤
      MulAction.stabilizer (MulAut (CFSG.LieType.Chevalley.twistedE6RootGroup F σ)) (e v) :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hfix1)
  have hevJ := hinv (e v) (mem_fixedPoints.2 fun φ hφ => MulAction.mem_stabilizer_iff.1 (hle hφ))
    (by rw [← map_mul, hv2, map_one])
  obtain ⟨w, hwJ, hwv⟩ := Subgroup.mem_map.1 hevJ
  obtain ⟨k, hkK, hkw⟩ := Subgroup.mem_map.1 hwJ
  have hkv : chevQuotHom 3 S k = v := hkw.trans (e.injective hwv)
  have hk : (k : Ω) ∈ K := Subgroup.mem_subgroupOf.1 hkK
  have hkerK : (chevQuotHom 3 K).ker ≤ Subgroup.center ↥K := by
    refine le_center_of_normal_of_isQuasisimple hKcomp.2.2 (chevQuotHom 3 K).normal_ker
      fun htop => ?_
    haveI := (chev_pSimple_simple_nonabelian hp hKd).1
    obtain ⟨y, hy⟩ := exists_ne (1 : PSimple 3 K)
    obtain ⟨s, rfl⟩ := chevQuotHom_surjective 3 K y
    exact hy (by rw [← MonoidHom.mem_ker, htop]; exact Subgroup.mem_top s)
  have hkk : chevQuotHom 3 S (k * k) = 1 := by rw [map_mul, hkv, hv2]
  refine ⟨chevQuotHom 3 K ⟨(k : Ω), hk⟩, orderOf_eq_prime ?_ ?_, fun b hbB hbK => ?_⟩
  ·
    rw [sq, ← map_mul]
    exact chevQuotHom_eq_one_of_le_of_core hc.quasi hc.core hKS (K.mul_mem hk hk) hkk
  ·
    intro h1
    have hkZ := Subgroup.mem_center_iff.1 (hkerK (MonoidHom.mem_ker.2 h1))
    have hcen : (⟨e v, hevJ⟩ : ↥((chevTransfer 3 S K).map e.toMonoidHom)) ∈
        Subgroup.center ↥((chevTransfer 3 S K).map e.toMonoidHom) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨y, hy⟩
      obtain ⟨w', hw'J, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨k', hk'K, rfl⟩ := Subgroup.mem_map.1 hw'J
      have hkk' : k' * k = k * k' := by
        have h3 := congrArg Subtype.val (hkZ ⟨(k' : Ω), Subgroup.mem_subgroupOf.1 hk'K⟩)
        exact Subtype.ext h3
      have hcomm : chevQuotHom 3 S k' * v = v * chevQuotHom 3 S k' := by
        rw [← hkv, ← map_mul, ← map_mul, hkk']
      apply Subtype.ext
      show e (chevQuotHom 3 S k') * e v = e v * e (chevQuotHom 3 S k')
      rw [← map_mul, ← map_mul, hcomm]
    rw [hZ, Subgroup.mem_bot] at hcen
    have h2 : e v = 1 := congrArg Subtype.val hcen
    exact hv1 (e.injective (h2.trans (map_one e).symm))
  ·
    have h1 : chevQuotHom 3 S ((S.normalizerMonoidHom ⟨b, hSN b⟩ k)⁻¹ * k) = 1 := by
      rw [map_mul, map_inv, ← chevAut_chevQuotHom, hkv, hvB b hbB (hSN b), inv_mul_cancel]
    rw [chevAut_chevQuotHom, ← inv_mul_eq_one, ← map_inv, ← map_mul]
    exact chevQuotHom_eq_one_of_le_of_core hc.quasi hc.core hKS _ h1

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
