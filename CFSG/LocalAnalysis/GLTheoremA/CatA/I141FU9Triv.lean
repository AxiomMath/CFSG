module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Pre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporL3DownBM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018U38Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFBU38Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LemRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.YS08 (SporL3Down IsL3Kind)
open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top I2018U38NotAlt I2018U38Cover)

theorem i141U9Fam_cyc : I141U9Fam u9FamCyc := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  exfalso
  obtain ⟨-, c, d, hcd⟩ := u9_simple_nonabelian hI1
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic p hp =>
    apply hcd
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

private theorem u9_alt_absurd {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {α : MulAut S} (hα3 : α ^ 3 = 1) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup α) I) (hU : catalogIs (PSimple 3 I) S9.isU3eight)
    (hNA : I2018U38NotAlt) {n : ℕ} (hn : 5 ≤ n) (eS : S ≃* alternatingGroup (Fin n)) : False := by
  by_cases hα1 : α = 1
  · rw [hα1, fixSubgroup_one_eq_top] at hI
    haveI := hs
    obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
    exact hNA (PSimple 3 I) hU n hn ⟨eT.trans eS⟩
  · have hβ : (MulAut.congr eS) α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hβ1 : (MulAut.congr eS) α ≠ 1 := fun h =>
      hα1 ((MulAut.congr eS).injective (h.trans (map_one _).symm))
    obtain ⟨hLe, ⟨eLe⟩⟩ := chevQ_transport Nat.prime_three eS hI
    obtain ⟨m, hm, -, ⟨f⟩⟩ := kdAltDown_holds n 3 hn Nat.prime_three (by norm_num) _ hβ hβ1 _ hLe
    have hm5 : 5 ≤ m := (le_max_left 5 3).trans hm
    exact hNA (PSimple 3 I) hU m hm5 ⟨eLe.trans f⟩

private theorem u9_spor_absurd {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {α : MulAut S} (hα3 : α ^ 3 = 1) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup α) I) (hU : catalogIs (PSimple 3 I) S9.isU3eight)
    (hCover : I2018U38Cover) {s : TauCeti.SporadicName} (hSpor : SporL3Down s)
    (eS : S ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 I) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hI
  have hL3 : IsL3Kind 2 (PQuot 3 I) := hCover _ hq hU
  exact hSpor S hs hna ⟨eS⟩ _ hα3 _ hI 2 hL3

section Alt


theorem i141U9Fam_alt : I141U9Fam u9FamAlt := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  exfalso
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨α, hα3, hJ', ⟨eJ⟩⟩ := u9_transfer hx hI1 hJ
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | alternating n hn =>
    exact u9_alt_absurd hs hna hα3 hJ' (catalogIs_congr' eJ hJU) CFSG.LocalAnalysis.GLTheoremA.I2018.I2018U38NotAlt_holds hn e
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

end Alt

section Spor


theorem i141U9Fam_spor
    : I141U9Fam u9FamSpor := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  exfalso
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨α, hα3, hJ', ⟨eJ⟩⟩ := u9_transfer hx hI1 hJ
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | sporadic s =>
    exact u9_spor_absurd hs hna hα3 hJ' (catalogIs_congr' eJ hJU)
      CFSG.LocalAnalysis.GLTheoremA.I2018.i2018U38Cover_holds
      (CFSG.LocalAnalysis.GLTheoremA.I2018.sporL3Down_all_of_BM
        CFSG.LocalAnalysis.GLTheoremA.sporL3Down_B_holds
        CFSG.LocalAnalysis.GLTheoremA.sporL3Down_M_holds s) e
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | lie _ => exact hi.elim

end Spor

end CFSG.LocalAnalysis.GLTheoremA.I141F
