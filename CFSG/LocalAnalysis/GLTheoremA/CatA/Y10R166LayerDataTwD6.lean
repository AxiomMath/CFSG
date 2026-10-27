module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD2
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.Open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)

open QuadraticMap Subgroup ClassicalGroups.Orthogonal

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem card_leviFixBar_cPair (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0) :
    Nat.card (leviFixBar (K := F) (cPair F b c 0) (cPair F b c 1)) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus 5 F b c (by norm_num) hirr
  rw [card_leviFixBar (cPair_orth F b c 0 1 (by decide)) hQ hT hQ']
  exact CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two F

theorem dvd_card_matrixProjectiveDerived (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0) {r : ℕ}
    (hr : r ∣ Nat.card F * (Nat.card F ^ 2 - 1)) :
    r ∣ Nat.card (matrixProjectiveDerived (Qc F b c)) := by
  have h1 : r ∣ Nat.card (leviFixBar (K := F)
      (cPair F b c 0) (cPair F b c 1)) := by
    rwa [card_leviFixBar_cPair hirr hQ']
  exact h1.trans (Subgroup.card_subgroup_dvd_card
    (leviFixBar (K := F) (cPair F b c 0) (cPair F b c 1)))

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)


section Certs


theorem dvd_card_of_hasLabel_twD_five {J : Type} [Group J] [Finite J] {n r : ℕ}
    (hn : 2 ≤ n) (hJ : HasLabel J (fun l : GLALabel => l = ⟨.twD, 5, n⟩))
    (hZ : Subgroup.center J = ⊥) (hrdvd : r ∣ 2 ^ (2 * n) - 1) :
    r ∣ Nat.card J := by
  obtain ⟨F, hfield, hfinite, hchar, hF, b, c, hirr, ⟨e⟩⟩ :=
    exists_mulEquiv_matrixProjectiveDerived_of_isLabel_twD hn hJ hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  have hF' : Nat.card F = 2 ^ n := hF
  have hQ' : ∃ v, OmegaMinusLD.Qc F b c v ≠ 0 :=
    (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) (b := b) (c := c)
      (0 : Fin 4)).exists_ne_zero
  have hdvd : r ∣ Nat.card (matrixProjectiveDerived (OmegaMinusLD.Qc F b c)) := by
    refine OmegaMinusLD.dvd_card_matrixProjectiveDerived hirr hQ' ?_
    have hpow : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [mul_comm 2 n, pow_mul]
    have hd : r ∣ (2 ^ n) ^ 2 - 1 := by rwa [hpow] at hrdvd
    rw [hF']
    exact dvd_mul_of_dvd_right hd (2 ^ n)
  have hcard : Nat.card J = Nat.card (matrixProjectiveDerived (OmegaMinusLD.Qc F b c)) :=
    Nat.card_congr e.toEquiv
  rwa [hcard]

end Certs


end CFSG.LocalAnalysis.GLTheoremA.Y10F
