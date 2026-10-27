module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataD5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)

open CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair

theorem layerData166_coordinatePlus {F : Type} [Field F] [Finite F] [CharP F 2] {m n q : ℕ}
    (hm : 4 ≤ m) (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqF : q ∣ Nat.card F - 1) :
    LayerData166 (matrixProjectiveDerived (coordinateQuadPlus m F)) q m := by
  obtain ⟨E, hEB, hEcard, hElayer⟩ := exists_qLayer_le_qTorus hm hn hF hq hq2 hqF
  exact ⟨qTorus (K := F) m q, rootGroupPoint (K := F) m hm, E,
    isElemAbelian_qTorus (K := F) m q hqF,
    card_qTorus (K := F) m q hq hqF,
    isPGroup_two_rootGroupPoint (K := F) m hm,
    qTorus_le_normalizer_rootGroupPoint (K := F) m q hm,
    qTorus_inf_centralizer_rootGroupPoint_eq_bot (K := F) m q hm,
    hEB, hEcard, hElayer⟩

section Label


theorem layerData166At_D {m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n) :
    LayerData166At (⟨.D, m, n⟩ : GLALabel) := by
  intro J _ _ q hlab hZ hq hq2 hqn
  obtain ⟨F, hfield, hfinite, hchar, hF, ⟨e⟩⟩ :=
    exists_mulEquiv_matrixProjectiveDerived_of_isLabel (K := J) hm hn hlab hZ
  letI : Field F := hfield
  letI : Finite F := hfinite
  letI : CharP F 2 := hchar
  have hqF : q ∣ Nat.card F - 1 := by rw [hF]; exact hqn
  show LayerData166 J q m
  exact LayerData166.of_mulEquiv e
    (layerData166_coordinatePlus hm hn hF hq hq2 hqF) hq

theorem layerData166At_D_six :
    ∀ n : ℕ, 2 ≤ n → LayerData166At (⟨.D, 6, n⟩ : GLALabel) :=
  fun n hn => layerData166At_D (by norm_num) hn

theorem layerData166At_D_seven :
    ∀ n : ℕ, 2 ≤ n → LayerData166At (⟨.D, 7, n⟩ : GLALabel) :=
  fun n hn => layerData166At_D (by norm_num) hn

end Label

section Certs


theorem i166On_famDFive_holds
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On (fun lab p z => i166FamD lab p z ∧ 5 ≤ lab.rank) :=
  i166On_famDFive_of_transport htr (fun m n hm hn => layerData166At_D hm hn)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
