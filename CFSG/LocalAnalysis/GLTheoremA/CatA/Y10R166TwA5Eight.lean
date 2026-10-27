module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerSymplecticOrth
public import CFSG.Open.StatedSUFieldChange
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallTwo
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open TwA5Eight

theorem exists_mulEquiv_unitaryPSU_six_of_isLabel_twA5_eight
    {K : Type} [Group K] [Finite K]
    (hK : HasLabel K (· = ⟨.twA, 5, 3⟩)) (hz : Subgroup.center K = ⊥) :
    Nonempty (K ≃* unitaryPSU
      (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
        (f := 3) (by norm_num)) 6) := by
  obtain ⟨-, -, hM⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 3 := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨e0⟩⟩ :=
    hM'.statedClassicalModel (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  have hFcard' : Fintype.card F = 64 := by
    rw [← Nat.card_eq_fintype_card]
    calc Nat.card F = (2 ^ 3) ^ 2 := hFcard
      _ = 64 := by norm_num
  haveI : Fintype (GaloisField 2 6) := Fintype.ofFinite _
  let θ : F ≃+* GaloisField 2 6 := FiniteField.ringEquivOfCardEq (by
    rw [hFcard', ← Nat.card_eq_fintype_card]
    exact (GaloisField.card 2 6 (by norm_num)).symm)
  let hGF : UnitaryFieldData 2 3 (GaloisField 2 6) :=
    CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
      (f := 3) (by norm_num)
  let e1 : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let eSU : StatedProj (StatedSU 6 (2 ^ 3) F) ≃*
      StatedProj (StatedSU 6 (2 ^ 3) (GaloisField 2 6)) :=
    CFSG.Open.StatedSUFieldChange.statedProjSUEquiv θ 6 (2 ^ 3)
  let ePSU : StatedProj (StatedSU 6 (2 ^ 3) (GaloisField 2 6)) ≃* unitaryPSU hGF 6 :=
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hGF (n := 6) (by norm_num)).symm
  exact ⟨e1.symm.trans (e0.trans (eSU.trans ePSU))⟩

section Certs


theorem concl166S_twA5Eight_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hK : HasLabel K (fun l : GLALabel => l = lab))
    (hfam : i166FamTwA5 lab p (Subgroup.center K = ⊥))
    (hp : p.Prime) (hz : Subgroup.center K = ⊥) (hn : lab.n = 3) :
    ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J := by
  obtain ⟨ht, hr, -, hpd⟩ := hfam
  have hlab : lab = ⟨.twA, 5, 3⟩ := by
    rcases lab with ⟨t, r, n⟩
    simp only at ht hr hn hpd ⊢
    subst ht
    subst hr
    subst hn
    rfl
  subst hlab
  have hp7 : p = 7 := by
    have hpd' : p ∣ 7 := by simpa using hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 hpd'
  subst hp7
  let hGF : UnitaryFieldData 2 3 (GaloisField 2 6) :=
    CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
      (f := 3) (by norm_num)
  obtain ⟨e⟩ := exists_mulEquiv_unitaryPSU_six_of_isLabel_twA5_eight (K := K) hK hz
  exact htr e (p := 7) (concl166S_twA5Eight_model hGF)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
