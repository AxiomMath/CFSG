module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Triality
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClass
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem card_le_nine_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    (hQv : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (t : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) (ht3 : t ^ 3 = 1)
    (htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 K))
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : CFSG.Open.IsElemAbelian 3 A) (hfix : ∀ a ∈ A, t a = a) : Nat.card A ≤ 9 := by
  set Φ := CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv (coordinateQuadPlus 4 K) hQv with hΦ
  set α : MulAut (matrixDerived (coordinateQuadPlus 4 K)) := MulAut.congr Φ.symm t with hαdef
  have hαapp : ∀ y, α y = Φ.symm (t (Φ y)) := fun y => by
    simp [hαdef, MulAut.congr_apply]
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, ht3, map_one]
  have hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K),
      CFSG.RankThree.PartOne.AUTSL.conjAct (coordinateQuadPlus 4 K) g ≠ α := by
    intro g hg
    apply htE
    refine (mem_matrixProjectiveImage_iff _ t).mpr ⟨g, MulEquiv.ext fun x => ?_⟩
    obtain ⟨y, rfl⟩ := Φ.surjective x
    have h1 : α y = CFSG.RankThree.PartOne.AUTSL.conjAct _ g y := by rw [hg]
    have h2 : t (Φ y) = Φ (α y) := by rw [hαapp, MulEquiv.apply_symm_apply]
    rw [h2, h1, CFSG.RankThree.PartOne.AUTSL.conjAct_apply]
    exact matrixProjectiveConjugation_mk _ g y
  set E' : Subgroup (matrixDerived (coordinateQuadPlus 4 K)) := A.comap Φ.toMonoidHom with hE'def
  have hcard : Nat.card E' = Nat.card A :=
    Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => Iff.rfl)
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE' : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Φ.injective ?_)⟩⟩, fun y hy => Φ.injective ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommA _ a.2 _ b.2
    · rw [map_pow, map_one]
      exact hA.2 _ hy
  have hfix' : ∀ e ∈ E', α e = e := fun e he => by
    have h := hfix _ he
    change t (Φ e) = Φ e at h
    rw [hαapp, h, MulEquiv.symm_apply_apply]
  have h9 := CFSG.StandardType.D4Rank.card_le_nine_of_classInput
    CFSG.StandardType.D4Rank.ggD4TrialityClassInput_holds α hα3 hns E' hE' hfix'
  rw [← hcard]
  exact h9

theorem center_eq_bot_of_mulEquiv {T H : Type} [Group T] [Group H] (φ : T ≃* H)
    (hcen : Subgroup.center T = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : φ.symm z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hz (φ y)
  rw [hcen, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg φ hz'

theorem pRank_mulAut_le_of_charTwo {T : Type} [Group T] [Finite T] {f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus 4 2 f) (hcen : Subgroup.center T = ⊥) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut T)) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) + 1 := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  have : CharP K 2 := ringChar.of_eq (coordinate_model_witness_plus hm K hK e).1
  set φ := coordinatePlusWitnessEquiv K e with hφ
  have hcen' := center_eq_bot_of_mulEquiv φ hcen
  have h3 : 3 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
    have h := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := K)
      (n := 4) le_rfl
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ] at h
  have hQv :=
    CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value
      _ hQ
  have key := pRank_mulAut_le_of_trialityBound _ hQ hab hidx hcen'
    (fun t ht3 htE A hA hfix => card_le_nine_of_charTwo hQv t ht3 htE A hA hfix) h3
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr φ),
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]

end CFSG.HardMathSupport.Timmesfeld.DFour
