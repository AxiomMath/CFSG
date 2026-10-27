module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Char
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr')


section Certs


theorem i141U9Fam_lin : I141U9Fam u9FamLin := by
  intro Γ _ _ K J x a hQ hx ha hxa hxna hI1 hI2 hJ hJU hZ hF
  exfalso
  have hxN : x ∈ Subgroup.normalizer (K : Set Γ) := hI1.1 (Subgroup.mem_zpowers x)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx
  have hα3 : chevAut 3 K ⟨x, hxN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  have hcardJ : Nat.card (PSimple 3 (chevTransfer 3 K J)) = 5515776 :=
    CatSingle.card_isU3eight lieOrderBridge_holds hU'
  have hdvd : 5515776 ∣ Nat.card (PSimple 3 K) := u9_dvd_card lieOrderBridge_holds hU'
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | lie d' =>
    obtain ⟨d, hv⟩ := d'
    cases d with
    | A r q =>
      have hq2 : q.p = 2 := by
        rcases u9_char_two hI1 e with h | h
        · simpa using h
        · exact absurd (Nat.le_of_dvd Nat.card_pos hdvd) (by omega)
      have hM : CFSG.Models.LieModel (PSimple 3 K) .PSL (r + 1) q.p q.exponent :=
        CFSG.Models.lieModel_A r q hv e
      rw [hq2] at hM
      obtain ⟨hadm, K₀, hK₀f, hK₀fin, hK₀card, ⟨eK⟩⟩ :=
        hM.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
      have hlabAll : Y10F.HasLabel (PQuot 3 K) (fun _ => True) :=
        CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hI1.2
      have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := Y10F.hasLabel_isQuasisimple hlabAll
      obtain ⟨labK, hlab, hin⟩ := innDiagKind_chevAut hxN hq hI1
      have hdict := Y10GInnLin.linLabelDict_holds (PQuot 3 K) labK (r + 1) q.exponent K₀
        hadm.2.2.1 hK₀card hlab ⟨eK⟩
      have hFam : Y10GField.FamLin labK := u9_famLin_of_canonLabel hdict
      have hcen : Subgroup.center (PSimple 3 K) = ⊥ := Y10F.center_centerQuot_eq_bot hq
      obtain ⟨a', m', E', hE'f, hE'fin, ha', hE'card, ⟨eJ'⟩⟩ := u9_lin_pSimple hcen hFam hin hα3 hJ'
      exact u9_card_psl_ne_u38 ha' hE'card (by rw [← Nat.card_congr eJ'.toEquiv]; exact hcardJ)
    | _ => exact hi.elim
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
