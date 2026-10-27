module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrPow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrUniModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommUniTransferNormFix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover
import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Uni
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Uni

theorem parabIrrOn_idxTwistedA_of :
    ParabIrrOn (CFSG.AGLEmbedding.IsLieOf CFSG.AGLEmbedding.IdxTwistedA) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hBp hcyc hBY hBP hW hNY hNP hNB hirr
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    Lin.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨K, _, f, t, s, ε, h, I, hε, hI, ⟨C⟩⟩ := exists_uniCover hY hodd hF hpar hne
  have hPY : P ≤ Y := hpar.1
  have hbig := C.exists_big_block hε hI hPY hna
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hperf : Group.IsPerfect ↥Y := ⟨hY.1⟩
  have hr : 1 ≤ t + s := (hI.le t hI.mem).1.trans (Nat.le_add_right t s)
  have hIr : ∀ c ∈ I, 1 ≤ c ∧ c ≤ t + s := fun c hc =>
    ⟨(hI.le c hc).1, (hI.le c hc).2.trans (Nat.le_add_right t s)⟩
  obtain ⟨j₀, hj₀⟩ := hbig
  have h4 := four_le_of_isBigBlock hI hj₀
  have hn3 : 3 ≤ 2 * (t + s) + ε := by omega
  have hq : ¬(2 * (t + s) + ε = 3 ∧ 2 ^ f = 2) := fun hc => absurd hc.1 (by omega)
  have hzero : ∀ b (hb : b ∈ B), C.autHom ⟨b, hBY hb⟩ = 1 := by
    refine forall_eq_one_of_actsAsPow (ρ := C.autHom) hBY hNY hcyc hirr hNB fun n hn => ?_
    obtain ⟨γ, hγ⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn3 hq
      (C.autHom ⟨n, hNY hn⟩)
    have hγf := smul_hypFlag_eq_of_map_projFlag h hr hε hIr γ
      (by rw [hγ]; exact C.map_projFlag ⟨n, hNY hn⟩ (hNP hn))
    obtain ⟨k, -, hk⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two
      (by have := h.one_le; omega) h.card (γ : SemiGL (HypIndex (t + s) ε) K).right
    refine ⟨((2 ^ k : ℕ) : ℤ), actsAsPow_of_two_pow hp hp2 hBY hBp
      (fun b hb => (Subgroup.mem_normalizer_iff.1 (hNB hn) b).1 hb) _ fun b hb => ?_⟩
    have hNF := C.normFix_autHom hε hI hPY ⟨b, hBY hb⟩ (hBP hb) (hW b hb)
    obtain ⟨m, hm⟩ := hBp ⟨b, hb⟩
    have hbm : ((⟨b, hBY hb⟩ : ↥(Subgroup.normalizer (Y : Set A))) : A) ^ p ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    obtain ⟨γb, hγb, hσb, -, hfb, hbb, hrb⟩ := exists_block_scalar hr hε hI ⟨j₀, hj₀⟩
      (C.odd_orderOf_autHom ⟨b, hBY hb⟩ hp_odd hbm) hNF
    obtain ⟨j, hj⟩ := exists_pow_two_eq_one_conj_pow hε hI γ γb hγf hk hσb hfb hbb hrb
    refine ⟨j, ?_⟩
    have hΦ : C.autHom ⟨n, hNY hn⟩ * C.autHom ⟨b, hBY hb⟩ * (C.autHom ⟨n, hNY hn⟩)⁻¹ *
        (C.autHom ⟨b, hBY hb⟩ ^ ((2 ^ k : ℕ) : ℤ))⁻¹ =
        semilinearAutHom h hr hε (γ * γb * γ⁻¹ * (γb ^ 2 ^ k)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hγ, hγb, zpow_natCast]
    rw [hΦ, ← map_pow, hj, map_one]
  exact Or.inl fun b hb y hy => C.centralizes_of_autHom_eq_one ⟨b, hBY hb⟩ (hzero b hb) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
