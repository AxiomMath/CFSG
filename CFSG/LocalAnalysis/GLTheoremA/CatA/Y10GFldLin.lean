module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLinMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLinLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.HardMathSupport.Foote.ModuleExclusions (Ai)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinMark (fieldKind_linear_data)
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinTw (sigma_pow_eq_one normProd_scalar Ai_eq_smul_one_of_normProd)
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinLang (fixed_component_iso no_pComponent_two_two)

theorem innDiagLin_of_labelDict (hD : CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.LinLabelDict) : InnDiagLin :=
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiagLin_of_labelDict hD

theorem fldLin_of_labelDict (hD : CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.LinLabelDict) : FldLin := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
  haveI := Fact.mk hp
  obtain ⟨K, hK, hKf, d, hd2, hcardK, hTag, hRank, A, σ, u, e, hαu, hβ, hσ1⟩ :=
    fieldKind_linear_data hcen hFam hfld
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, m, hqp, hqcard⟩ := FiniteField.card' K
    have hcard' : Nat.card K = 2 ^ (canonLabel labK).n := hcardK
    rw [Nat.card_eq_fintype_card, hqcard] at hcard'
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hcard']
      exact dvd_pow_self q (PNat.ne_zero m)
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hσp : σ ^ p = 1 := sigma_pow_eq_one hd2 h2 A σ p u hβ hpow
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hJ' : GLAPComponent p (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq, ← fixSubgroup_map_congr]
    exact (glaPComponent_map_iff hp e.injective).mpr hJ
  have hlabJ' : HasLabel ↥(J.map e.toMonoidHom) (fun l : GLALabel => l = labJ) :=
    hasLabel_transport e hlabJ
  obtain ⟨cN, hNc⟩ := normProd_scalar hd2 h2 A σ p u hβ hpow hσp
  have hsc : ∃ c : K, Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) =
      c • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hord]
    exact Ai_eq_smul_one_of_normProd A σ p ⟨cN, hNc⟩
  have hn1 : 1 ≤ (canonLabel labK).n := by
    rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
    · exfalso
      have hcard' : Nat.card K = 2 ^ (canonLabel labK).n := hcardK
      rw [h0, pow_zero] at hcard'
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h0
  have hFcard : Nat.card (fixField σ) = 2 ^ ((canonLabel labK).n / p) := by
    have h := card_fixField Nat.prime_two hn1 hcardK σ
    rw [hord] at h
    exact h
  have hpn : p ∣ (canonLabel labK).n := by
    have h := orderOf_dvd_of_card Nat.prime_two hn1 hcardK σ
    rwa [hord] at h
  have hmul : p * ((canonLabel labK).n / p) = (canonLabel labK).n := Nat.mul_div_cancel' hpn
  have hm1 : 1 ≤ (canonLabel labK).n / p :=
    Nat.div_pos (Nat.le_of_dvd hn1 hpn) hp.pos
  have hcardF : Nat.card (fixField σ) = 2 ∨ 4 ≤ Nat.card (fixField σ) := by
    rw [hFcard]
    rcases Nat.lt_or_ge ((canonLabel labK).n / p) 2 with h | h
    · left
      rw [show (canonLabel labK).n / p = 1 by omega]
      norm_num
    · right
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ ((canonLabel labK).n / p) := Nat.pow_le_pow_right (by norm_num) h
  have hquot : Nonempty (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom) ≃*
      StatedProj (StatedSL d ↥(fixField σ))) := by
    rcases (show 3 ≤ d ∨ d = 2 by omega) with h3 | h2d
    · exact fixed_component_iso hd2 h2 A σ p hord u hβ hsc _ hJ' (Or.inl h3)
    · subst h2d
      rcases hcardF with hF2 | hF4
      · exact (no_pComponent_two_two h2 A σ p hord u hβ hsc hF2 _ hJ').elim
      · exact fixed_component_iso hd2 h2 A σ p hord u hβ hsc _ hJ' (Or.inr hF4)
  have hD' := hD ↥(J.map e.toMonoidHom) labJ d ((canonLabel labK).n / p) (fixField σ) hd2 hFcard hlabJ' hquot
  have hJn : (canonLabel labJ).n = (canonLabel labK).n / p := by rw [hD']
  have hJtag : (canonLabel labJ).tag = .A := by rw [hD']
  have hJrank : (canonLabel labJ).rank = d - 1 := by rw [hD']
  refine ⟨?_, ?_, ?_⟩
  · rw [hJn, hmul]
  · rw [hJtag, hTag]
  · rw [hJrank]
    omega

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
