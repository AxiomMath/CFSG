module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag


theorem exists_concl166S_twE6_of_center_ne_bot
    {X : Type} [Group X] [Finite X] {lab : GLALabel} {p : ℕ}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ lab.n - 1)
    (hr : GLATwoLocalRank p X + 1 = evenRank X) (hZ : Subgroup.center X ≠ ⊥) :
    ∃ (q : ℕ) (B' : Subgroup X) (x' : X) (J : Subgroup X), Concl166S X p q B' x' J := by
  classical
  obtain ⟨F, hField, hFin, hCharF, σ, hcard, hσ, ⟨eC⟩⟩ :=
    exists_mulEquiv_twE6C_quot_of_isLabel hX ht hn
  letI : Field F := hField
  letI : Finite F := hFin
  letI : CharP F 2 := hCharF
  obtain ⟨hZcard, -, hoddn, hn3⟩ := twE6_caseB_arith hX ht hn hZ
  obtain ⟨z, hzcenter, hz3, hzZ⟩ := exists_center_eq_zpowers_of_card_three hZcard
  let C : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
    twE6C (iterateFrobenius (AlgebraicClosure F) 2 lab.n)
  let π : X →* ↥C := eC.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π :=
    eC.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hkerπ : π.ker = Subgroup.center X := by
    change (eC.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ eC.injective, QuotientGroup.ker_mk']
  obtain ⟨B, E, S, hzB, hBelem, hBcard, hEB, hEelem, hEcard, hzE, he3, hS2, hBS, hBC⟩ :=
    exists_caseB_witness_of_cover (F := F) (σ := σ) hn3 hoddn hcard hσ π hπ hzcenter hz3
      (hkerπ.trans hzZ)
  exact exists_concl166S_twE6_of_caseB_data hX ht hn hp hp2 hpdvd hr hZ hzZ hz3 hzB hBelem
    hBcard hEB hEelem hEcard hzE he3 hS2 hBS hBC

theorem i166On_famTwE6_holds : I166On i166FamTwE6 := by
  intro K _ _ lab p hK hfam hp hp2 _ _ hr
  obtain ⟨ht, hn, hpdvd⟩ := hfam
  by_cases hz : Subgroup.center K = ⊥
  · exact exists_concl166S_twE6_of_center_eq_bot hK ht hn hp hp2 hpdvd hz
  · exact exists_concl166S_twE6_of_center_ne_bot hK ht hn hp hp2 hpdvd hr hz

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
