module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriOuter
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate18000

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10GTri

set_option linter.unusedSectionVars false


theorem d4_kind_of_eps_zero {S : Type} [Group S] {n : ℕ} (hperf : commutator S = ⊤)
    (hlam : LargeEvenInLambda2 (⟨.D, 4, n⟩ : GLALabel)) (hcen : Subgroup.center S = ⊥)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)), a * b ≠ b * a)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
    {α : MulAut S} (g : adjointGroup Tag.D4 K) (σ : K ≃+* K)
    (hα : MulAut.congr ((((QuotientGroup.quotientMulEquivOfEq hcen).trans
        QuotientGroup.quotientBot).symm.trans θ).trans (isoAdj K)) α =
      MulAut.conj g * entrywiseAdjointAut Tag.D4 σ) :
    InnDiagKind S ⟨.D, 4, n⟩ α ∨ FieldKind S ⟨.D, 4, n⟩ α := by
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  have hind : LargeEvenInduces θ (fun s s' => s' = α s) (MulAut.congr e α) := by
    rintro l _ rfl
    show MulAut.congr e α (e l) = e (α l)
    simp [MulAut.congr_apply]
  have huniq : ∀ u' : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
      LargeEvenInduces θ (fun s s' => s' = α s) u' → u' = MulAut.congr e α := by
    intro u' hu'
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    exact (hu' s (α s) rfl).trans (hind s (α s) rfl).symm
  have hu : MulAut.congr e α = MulAut.conj ((isoAdj K).symm g) *
      MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ) := by
    have h1 : MulAut.congr e α =
        MulAut.congr (isoAdj K).symm (MulAut.congr (e.trans (isoAdj K)) α) := by
      ext x
      simp [MulAut.congr_apply]
    rw [h1, hα, map_mul, tri_congr_conj]
  by_cases hI : MulAut.congr e α ∈
      LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
  · exact Or.inl (tri_innDiagKind_of_recipe hperf hlam hK hs hna θ hI hind)
  · refine Or.inr (tri_fieldKind_of_recipe hperf hlam hK hs hna θ
      (i := MulAut.conj ((isoAdj K).symm g))
      (f := MulAut.congr (isoAdj K).symm (entrywiseAdjointAut Tag.D4 σ)) ⟨_, rfl⟩
      (tri_field_mem σ) (hu ▸ hind) ?_)
    rintro ⟨u', hu', hind'⟩
    exact hI (huniq u' hind' ▸ hu')

theorem d4_normal_form {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥) {n : ℕ}
    (hlab : HasLabel S (fun l : GLALabel => l = ⟨.D, 4, n⟩)) {α : MulAut S} (hα : α ^ 3 = 1)
    (hin : ¬ InnDiagKind S ⟨.D, 4, n⟩ α) (hfld : ¬ FieldKind S ⟨.D, 4, n⟩ α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 2 ^ n) (g : adjointGroup Tag.D4 K)
      (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (α' : MulAut ↥(adjointGroup Tag.D4 K)),
      (ε = 1 ∨ ε = 2) ∧ σ ^ 3 = 1 ∧ α' ^ 3 = 1 ∧
      α' = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∧
      Nonempty (↥(fixSubgroup α) ≃* ↥(fixSubgroup α')) := by
  obtain ⟨hperf, lab', hlam', hraw⟩ := hlab
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hEq⟩ := hQ0
  subst hEq
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (by norm_num)] at hraw
  obtain ⟨K, hKF, hKfin, hK, hsR, hnaR, θ, -⟩ := hraw
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eA := e.trans (isoAdj K)
  let α' := MulAut.congr eA α
  have hα3 : α' ^ 3 = 1 := by
    change (MulAut.congr eA α) ^ 3 = 1
    rw [← map_pow, hα, map_one]
  obtain ⟨g, a, σ, ε, hε3, hσ3, hα'eq⟩ := exists_cube_normal_form_sigma α' hα3
  have hfix : (fixSubgroup α).map eA.toMonoidHom = fixSubgroup α' :=
    Y10F.fixSubgroup_map_congr eA α
  let eC : ↥(fixSubgroup α) ≃* ↥(fixSubgroup α') :=
    (Subgroup.equivMapOfInjective _ eA.toMonoidHom eA.injective).trans (MulEquiv.subgroupCongr hfix)
  rcases (by omega : ε = 0 ∨ ε = 1 ∨ ε = 2) with hε0 | hε12
  · exfalso
    subst hε0
    have hring2 : ringChar K = 2 := ringChar.eq_iff.mpr (CFSG.StandardType.charP_two_of_card hK)
    obtain ⟨d, hd⟩ :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exactNormalAut_eq_conj_of_charTwo
        hring2 a
    have hα1 : α' = MulAut.conj (g * d) * entrywiseAdjointAut Tag.D4 σ := by
      rw [hα'eq, tri_d4Graph_zero, mul_one,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.exactNormalAut_D4_eq_mul, hd,
        map_mul, mul_assoc]
    rcases d4_kind_of_eps_zero hperf hlam' hcen hK hsR hnaR θ (g * d) σ hα1 with h | h
    · exact hin h
    · exact hfld h
  · exact ⟨K, hKF, hKfin, hK, g, a, σ, ε, α', hε12, hσ3, hα3, hα'eq, ⟨eC⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
