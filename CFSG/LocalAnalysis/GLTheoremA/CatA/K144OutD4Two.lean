module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144TriFixCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriOuter
import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model
public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeIso
import CFSG.ClassicalInvolution.Asc77.AscT8X4
import CFSG.ClassicalInvolution.Asc77.AscT8YA3
import CFSG.ClassicalInvolution.AschTight.S19BCSW
import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
import CFSG.ClassicalInvolution.Q3.Q3T8B10
import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
import CFSG.ClassicalInvolution.Q3.Q3TIMain
import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
import CFSG.ClassicalInvolution.Q3.Q3TKMem
import CFSG.ClassicalInvolution.Q3.TL3GlueOdd
import CFSG.ClassicalInvolution.Q3.TL3S8Gold
import CFSG.ClassicalInvolution.Q3.TL3S8Sd
import CFSG.ClassicalInvolution.SmallCases.NobqFinal
import CFSG.Goldschmidt.Steps.G310Core2
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.Goldschmidt75.TheoremB
import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)
open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.Y10GTri

section OutD4Two


theorem card_fix_le_D4two {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    (hlab : HasLabel S (fun l : GLALabel => l = (⟨.D, 4, 1⟩ : GLALabel))) {β : MulAut S}
    (hβ3 : β ^ 3 = 1) (hnin : ¬ InnDiagKind S (⟨.D, 4, 1⟩ : GLALabel) β)
    (hnfld : ¬ FieldKind S (⟨.D, 4, 1⟩ : GLALabel) β) :
    Nat.card ↥(fixSubgroup β) ≤ 12096 := by
  obtain ⟨hperf, lab', hlam', hraw⟩ := hlab
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hEq⟩ := hQ0
  subst hEq
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (by norm_num)] at hraw
  obtain ⟨K, hKF, hKfin, hK, hsR, hnaR, θ, -⟩ := hraw
  have hring2 : ringChar K = 2 := by
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
    exact ringChar.eq K 2
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eA := e.trans (isoAdj K)
  have hind : LargeEvenInduces θ (fun s s' => s' = β s) (MulAut.congr e β) := by
    rintro l _ rfl
    show MulAut.congr e β (e l) = e (β l)
    simp [MulAut.congr_apply]
  have huniq : ∀ u' : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
      LargeEvenInduces θ (fun s s' => s' = β s) u' → u' = MulAut.congr e β := by
    intro u' hu'
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    exact (hu' s (β s) rfl).trans (hind s (β s) rfl).symm
  set α' := MulAut.congr eA β with hα'def
  have hα3 : α' ^ 3 = 1 := by rw [hα'def, ← map_pow, hβ3, map_one]
  have hcongr : α' = MulAut.congr (isoAdj K) (MulAut.congr e β) := MulEquiv.ext fun x => rfl
  obtain ⟨g, a, σ, ε, hε3, hσ3, hα'eq⟩ := exists_cube_normal_form_sigma α' hα3
  have hfix : (fixSubgroup β).map eA.toMonoidHom = fixSubgroup α' :=
    Y10F.fixSubgroup_map_congr eA β
  let eC : ↥(fixSubgroup β) ≃* ↥(fixSubgroup α') :=
    (Subgroup.equivMapOfInjective _ eA.toMonoidHom eA.injective).trans (MulEquiv.subgroupCongr hfix)
  rcases (by omega : ε = 0 ∨ ε = 1 ∨ ε = 2) with hε0 | hε12
  ·
    exfalso
    subst hε0
    obtain ⟨d, hd⟩ :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
        hring2 a
    have hα1 : α' = MulAut.conj (g * d) * entrywiseAdjointAut Tag.D4 σ := by
      rw [hα'eq, tri_d4Graph_zero, mul_one,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.exactNormalAut_D4_eq_mul, hd,
        map_mul, mul_assoc]
    have hu : MulAut.congr e β = MulAut.conj ((isoAdj K).symm (g * d)) *
        MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ) := by
      have h1 : MulAut.congr e β = MulAut.congr (isoAdj K).symm α' := by
        rw [hcongr]
        ext x
        simp [MulAut.congr_apply]
      rw [h1, hα1, map_mul, tri_congr_conj]
    by_cases hI : MulAut.congr e β ∈
        LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    · exact hnin (tri_innDiagKind_of_recipe hperf hlam' hK hsR hnaR θ hI hind)
    · refine hnfld (tri_fieldKind_of_recipe hperf hlam' hK hsR hnaR θ
        (i := MulAut.conj ((isoAdj K).symm (g * d)))
        (f := MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ)) ⟨_, rfl⟩
        (tri_field_mem σ) (hu ▸ hind) ?_)
      rintro ⟨u', hu', hind'⟩
      exact hI (huniq u' hind' ▸ hu')
  ·
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hσ1 : σ = 1 := CFSG.ClassicalInvolution.Q3.TL4.Vtx.ringEquiv_eq_one_of_card_two hK2 σ
    subst hσ1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨eD⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
        (ℓ := 2) (f := 1) (le_refl 1) K hK α' hα3 g a hε12 hα'eq
    calc Nat.card ↥(fixSubgroup β) = Nat.card ↥(fixSubgroup α') := Nat.card_congr eC.toEquiv
      _ = Nat.card ↥(fixSubgroup φ) := Nat.card_congr eD.toEquiv
      _ ≤ 12096 := card_fix_le_triFix hK₃ Fr hFr φ hφ3 hφout

end OutD4Two

end CFSG.LocalAnalysis.GLTheoremA.K144
