module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGResCls
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniN
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniQ2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniS
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.Assembly
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.StandardType
open CFSG.HardMathSupport.Solomon.Coordinator (PerfectInLayer)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (perfectInLayer_of_congr perfectInLayer_primeFormP)

private theorem false_of_recipeUnitary {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    (hB : Nat.card B = 3 ^ 4) {n d : ℕ} (hn : 1 ≤ n)
    (hd : (3 ∣ 2 ^ n + 1 ∧ 4 ≤ d ∧ d ≤ 5) ∨ (3 ∣ 2 ^ n - 1 ∧ 6 ≤ d))
    (hraw : LargeEvenRecipeUnitary d (2 ^ n) fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ Φ : PSimple 3 S ≃* R, ∀ (b : Ω)
        (hbN : b ∈ Subgroup.normalizer (S : Set Ω)), b ∈ B →
          MulAut.congr Φ (chevAut 3 S ⟨b, hbN⟩) ∈ I) : False := by
  obtain ⟨F, _, _, hF, -, -, Φ, hΦ⟩ := hraw
  have hFd : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn, by rw [hF, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  have hc := h.cfg
  obtain ⟨hDB, -⟩ := hc.std
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 hc.normal) ▸ Subgroup.mem_top g
  obtain ⟨d₀, hdD, hdx⟩ := SG.exists_mem_D_not_zpowers h
  obtain ⟨hXe, hXc⟩ := SG.card_map_chevAut h hB
  have hdX : chevAut 3 S ⟨d₀, hSN d₀⟩ ∈
      (B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hDB hdD))
  have hd3 : chevAut 3 S ⟨d₀, hSN d₀⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨d₀, hSN d₀⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ 3 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hc.elem.2 d₀ (hDB hdD)), map_one]
  have hXD : ∀ β ∈ (B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S),
      MulAut.congr (InndiagSU.projEquiv hFd hd1) (MulAut.congr Φ β) ∈
        primeFormD hFd ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    rintro _ ⟨⟨b, hbN⟩, hb, rfl⟩
    exact InndiagSU.congr_mem_primeFormD hFd hd1 hF (hΦ b hbN (Subgroup.mem_subgroupOf.1 hb))
  have hpl : PerfectInLayer (MulAut.congr (Φ.trans (InndiagSU.projEquiv hFd hd1))
      (chevAut 3 S ⟨d₀, hSN d₀⟩)) :=
    perfectInLayer_primeFormP hFd (by omega) (fun e => absurd e.1 (by omega)) Nat.prime_three
      (by norm_num) (by norm_num) _ (by rw [← map_pow, hd3, map_one])
  rcases hd with ⟨h3, hd4, hd5⟩ | ⟨h3, hd6⟩
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · exact SG.false_of_uni_two h hcat (by omega) hF hd4 hd5 Φ
    obtain ⟨A, hA, hnc, h3A, hAd, Y, hY, hYA⟩ := SG.uniS_core hFd hn2 h3 hd4 hd5
      (X := ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)).map
        (MulAut.congr Φ).toMonoidHom) (hXe.map _) (by rintro _ ⟨β, hβ, rfl⟩; exact hXD β hβ)
      (by rw [Subgroup.card_map_of_injective (MulAut.congr Φ).injective]; exact hXc)
      (Subgroup.mem_map_of_mem _ hdX)
    haveI := hA
    exact SG.false_of_simple_fix_congr h hcat hB Φ hdD hdx (hSN d₀)
      (perfectInLayer_of_congr (InndiagSU.projEquiv hFd hd1) _ hpl) hnc h3A hAd hY hYA
  · obtain ⟨A, hA, hnc, h3A, hAd, Y, hY, hYA⟩ := SG.uniN_core hFd h3 hd6
      (X := ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)).map
        (MulAut.congr (Φ.trans (InndiagSU.projEquiv hFd hd1))).toMonoidHom) (hXe.map _)
      (by rintro _ ⟨β, hβ, rfl⟩; exact hXD β hβ) (Subgroup.mem_map_of_mem _ hdX)
    haveI := hA
    exact SG.false_of_simple_fix_congr h hcat hB _ hdD hdx (hSN d₀) hpl hnc h3A hAd hY hYA

theorem qsF3ResUni_holds : QSF3ResUni := by
  intro Ω _ _ S B T x D K lab h hcat hB hlab hlab2 h3 hc
  have hraw := SG.exists_rawDatum_chevAut h hlab
  have hcase := SG.resUni_rank h3 hc
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab2.1
  dsimp only at hcase
  rcases hcase with ⟨rfl, hp, hr3, hr4⟩ | ⟨rfl, hm, hr5⟩ | ⟨rfl, hp, rfl⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
    exact false_of_recipeUnitary h hcat hB hn (.inl ⟨hp, by omega, by omega⟩) hraw
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
    exact false_of_recipeUnitary h hcat hB hn (.inr ⟨hm, by omega⟩) hraw
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
    rw [if_neg (by decide), if_pos (by decide)] at hraw
    exact false_of_recipeUnitary h hcat hB hn (.inl ⟨hp, le_rfl, by norm_num⟩) hraw

end CFSG.LocalAnalysis.GLTheoremA.S265

end
