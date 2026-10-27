module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriLabPGL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriLabD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriLabTD4
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


theorem triOuter_canon_label (hRig : GGLabelRigidInput) {f : ℕ} (hf : 2 ≤ f) {K₃ : Type} [Field K₃]
    [Finite K₃] (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range)
    {X : Type} [Group X] [Finite X] {C J : Subgroup X} (e : ↥C ≃* ↥(fixSubgroup φ))
    (hJ : GLAPComponent 3 C J) {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : TriJLabel (canonLabel labJ) := by
  rcases triFixModel (by omega) hK₃ Fr hFr φ hφ3 hφ with
    ⟨F₀, _, _, hF₀, ⟨e'⟩⟩ | ⟨F, _, π, hF, ⟨e'⟩⟩
  · have := triCanon_G2 hRig hf hF₀ (e.trans e') hJ hlabJ
    refine Or.inl ?_
    rw [this]
  · cases π
    · refine Or.inr (Or.inl ?_)
      rw [triCanon_PGL_false_label hRig hf hF (e.trans e') hJ hlabJ]
      exact ⟨Or.inr rfl, rfl⟩
    · refine Or.inr (Or.inl ?_)
      rw [triCanon_PGL_true_label hRig hf hF (e.trans e') hJ hlabJ]
      exact ⟨Or.inl rfl, rfl⟩

theorem triD4_graph_label (hRig : GGLabelRigidInput) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) {g : adjointGroup Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {α' : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α' ^ 3 = 1)
    (hα' : α' = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))
    {X : Type} [Group X] [Finite X] {C J : Subgroup X} (e : ↥C ≃* ↥(fixSubgroup α'))
    (hJ : GLAPComponent 3 C J) {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : TriJLabel (canonLabel labJ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨eD⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv (ℓ := 2)
      (f := n) (by omega) K hK α' hα3 g a hε hα'
  exact triOuter_canon_label hRig hn hK₃ Fr hFr φ hφ3 hφout (e.trans eD) hJ hlabJ

theorem triOuterD4_label (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) {n : ℕ} (hn2 : 2 ≤ n)
    (hlab : HasLabel S (fun l : GLALabel => l = ⟨.D, 4, n⟩)) {α : MulAut S} (hα : α ^ 3 = 1)
    (hin : ¬ InnDiagKind S ⟨.D, 4, n⟩ α) (hfld : ¬ FieldKind S ⟨.D, 4, n⟩ α)
    {J : Subgroup S} {labJ : GLALabel} (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : GLAPComponent 3 (fixSubgroup α) J) : TriJLabel (canonLabel labJ) := by
  obtain ⟨K, _, _, hK, g, a, σ, ε, α', hε, hσ3, hα3, hα'eq, ⟨eC⟩⟩ :=
    d4_normal_form hcen hlab hα hin hfld
  by_cases hσ1 : σ = 1
  · subst hσ1
    exact triD4_graph_label hRig hn2 hK hε hα3 hα'eq eC hJ hlabJ
  · obtain ⟨m, hm, hnm, hcJ⟩ := triD4_graphField hRig hK hσ3 hσ1 hε hα3 hα'eq eC hJ hlabJ
    refine Or.inr (Or.inr ?_)
    rw [hcJ]

theorem triFieldTD4_label (hRig : GGLabelRigidInput) {S : Type} [Group S] [Finite S]
    (hcen : Subgroup.center S = ⊥) {labK : GLALabel} (hT : labK.tag = .triD4) (hn : 2 ≤ labK.n)
    {α : MulAut S} (hfld : FieldKind S labK α) (hα : α ^ 3 = 1) {J : Subgroup S} {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    TriJLabel (canonLabel labJ) := by
  obtain ⟨K, _, _, hK, Fr, hFr, φ, hφ3, hφout, ⟨eC⟩⟩ := td4_outer_data hcen hT hfld hα
  exact triOuter_canon_label hRig hn hK Fr hFr φ hφ3 hφout eC hJ hlabJ

end CFSG.LocalAnalysis.GLTheoremA.I167

end
