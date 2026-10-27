module

public import CFSG.HardMathSupport.Dickson.Bal207.D4GraphBridgeField
public import CFSG.HardMathSupport.Dickson.Bal207.D4Semilin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.HardMathSupport.Dickson.Bal207.Restate

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem mulAut_congr_conj {G H : Type} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext t
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem mulAut_congr_symm_congr {G H : Type} [Group G] [Group H] (e : G ≃* H) (φ : MulAut G) :
    MulAut.congr e.symm (MulAut.congr e φ) = φ := by
  ext t
  simp [MulAut.congr_apply]

section Glue

variable {F : Type} [Field F] [Finite F]


theorem semilinD4EightAut_conj (hF : Nat.card F = 8) (g : ↥(adjointGroup Tag.D4 F)) :
    SemilinD4EightAut ↥(adjointGroup Tag.D4 F) (MulAut.conj g) := by
  refine ⟨F, inferInstance, inferInstance, (isoAdj F).symm, hF, ?_⟩
  have h := mulAut_congr_conj (coordinatePlusWitnessEquiv F (isoAdj F).symm) g
  rw [h]
  exact CFSG.HardMathSupport.Timmesfeld.DefChar.Orth.inner_mem_matrixProjectiveImage _ _

theorem semilinD4EightAut_of_conj_entrywise (hF : Nat.card F = 8) (σ : F ≃+* F)
    {α ψ : MulAut ↥(adjointGroup Tag.D4 F)} (h : ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 σ) :
    SemilinD4EightAut ↥(adjointGroup Tag.D4 F) α := by
  have h1 : SemilinD4EightAut ↥(adjointGroup Tag.D4 F) (entrywiseAdjointAut Tag.D4 σ) :=
    ⟨F, inferInstance, inferInstance, (isoAdj F).symm, hF, congr_entrywiseAdjointAut_mem σ⟩
  have h2 := h1.of_mulEquiv ψ⁻¹
  have h3 : MulAut.congr ψ⁻¹ (entrywiseAdjointAut Tag.D4 σ) = α := by
    rw [← h]
    ext x
    simp [MulAut.congr_apply]
  rwa [h3] at h2

theorem exists_graph_of_not_semilin_adjoint (hF : Nat.card F = 2 ^ 3)
    (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hns : ¬ SemilinD4EightAut ↥(adjointGroup Tag.D4 F) α) :
    ∃ (g : ↥(adjointGroup Tag.D4 F)) (a : Fin Tag.D4.rank → Fˣ) (σ : F ≃+* F) (ε : ℕ),
      (ε = 1 ∨ ε = 2) ∧ α = MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε) := by
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  rcases d4_cube_trichotomy_model hF α hα with ⟨g, hg⟩ | ⟨σ, ψ, -, hψ⟩ | h
  · exact absurd (by rw [← hg]; exact semilinD4EightAut_conj hF8 g) hns
  · exact absurd (semilinD4EightAut_of_conj_entrywise hF8 σ hψ) hns
  · exact h

theorem graphAutD4_of_not_semilin_model {S : Type} [Group S] (hF : Nat.card F = 2 ^ 3)
    (e : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F))) (φ : MulAut S) (h3 : φ ^ 3 = 1)
    (hns : ¬ SemilinD4EightAut S φ) : GraphAutD4 S φ := by
  have hβ3 : MulAut.congr (e.trans (isoAdj F)) φ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hns' : ¬ SemilinD4EightAut ↥(adjointGroup Tag.D4 F)
      (MulAut.congr (e.trans (isoAdj F)) φ) := by
    intro h
    apply hns
    have h' := h.of_mulEquiv (e.trans (isoAdj F)).symm
    rwa [mulAut_congr_symm_congr] at h'
  obtain ⟨g, a, σ, ε, hε, hαeq⟩ := exists_graph_of_not_semilin_adjoint hF _ hβ3 hns'
  refine ⟨F, inferInstance, inferInstance, e.trans (isoAdj F), g, a, σ, ε, hF, hε, fun h => ?_⟩
  refine ⟨MulAut.congr (e.trans (isoAdj F)) φ h, ?_, rfl⟩
  rw [hαeq]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, coe_d4Graph]
  rfl

theorem graphAutD4_of_not_semilin {S : Type} [Group S]
    (hS : StatedClassicalModel S .POmegaPlus 4 2 3) (φ : MulAut S) (h3 : φ ^ 3 = 1)
    (hns : ¬ SemilinD4EightAut S φ) : GraphAutD4 S φ := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hS
  exact graphAutD4_of_not_semilin_model hF e φ h3 hns

theorem graphAutD4_of_not_semilin_idx {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsD4EightIdx d.1) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) (φ : MulAut S)
    (h3 : φ ^ 3 = 1) (hns : ¬ SemilinD4EightAut S φ) : GraphAutD4 S φ := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | D r q =>
    obtain ⟨rfl, hp, hexp⟩ := hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even 4 q hv hp e
    rw [hp, hexp] at hm
    exact graphAutD4_of_not_semilin hm φ h3 hns
  | _ => simp [IsD4EightIdx] at hd

end Glue

end CFSG.HardMathSupport.Dickson.Bal207

end
