module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TwE6UniqAbs

variable {L : Type} [Field L]

theorem iform_eq_sum_mul_iform_single {τ : Tag} (β γ : Fin τ.rank → ℤ) :
    ∑ j, iform β (Pi.single j 1) * γ j = iform β γ := by
  have h : ∀ j, iform β (Pi.single j 1) = ∑ i, β i * τ.symmetrizedCartan i j := by
    intro j
    unfold iform
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_apply, hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [h, Finset.sum_mul]
  unfold iform
  exact Finset.sum_comm

theorem rootDiag_apply_coord (a : Fin Tag.E6.rank → Lˣ) (w : RootModule Tag.E6 L)
    (b : Label Tag.E6) :
    rootDiag a w b = ((rootChar a (labelWt Tag.E6 b) : Lˣ) : L) * w b := by
  classical
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
  | single c r =>
    rw [← Finsupp.smul_single_one, map_smul, rootDiag_single]
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · ring

theorem iform_R6_abs_le_two : ∀ x ∈ R6, ∀ y ∈ R6, |iform x y| ≤ 2 := by
  decide +kernel

theorem abs_iform_le_two {a b : Fin Tag.E6.rank → ℤ}
    (ha : IsRoot Tag.E6 a) (hb : IsRoot Tag.E6 b) : |iform a b| ≤ 2 :=
  iform_R6_abs_le_two a (mem_R6_of_isRoot ha) b (mem_R6_of_isRoot hb)

theorem rootDiagUnit_rootVec (a : Fin Tag.E6.rank → Lˣ) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) :
    (rootDiagUnit Tag.E6 a : Module.End L (RootModule Tag.E6 L)) (rootVec Tag.E6 L β) =
      ((rootChar a β : Lˣ) : L) • rootVec Tag.E6 L β := by
  rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootVec_eq_single hβ]
  change rootDiag a (Finsupp.single (Sum.inr ⟨β, hβ⟩) 1) = _
  rw [rootDiag_single]
  rfl

theorem eigenvalue_rootDiagUnit (a : Fin Tag.E6.rank → Lˣ) {w : RootModule Tag.E6 L} {c : L}
    (hw : w ≠ 0)
    (h : (rootDiagUnit Tag.E6 a : Module.End L (RootModule Tag.E6 L)) w = c • w) :
    ∃ γ : Fin Tag.E6.rank → ℤ, (IsRoot Tag.E6 γ ∨ γ = 0) ∧ c = ((rootChar a γ : Lˣ) : L) := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hw (Finsupp.ext fun b => by simpa using hcon b)
  have hcoef : rootDiag a w b = c * w b := by
    change (rootDiagUnit Tag.E6 a : Module.End L (RootModule Tag.E6 L)) w b = c * w b
    rw [h, Finsupp.smul_apply, smul_eq_mul]
  have hc : ((rootChar a (labelWt Tag.E6 b) : Lˣ) : L) = c :=
    mul_right_cancel₀ hb ((rootDiag_apply_coord a w b).symm.trans hcoef)
  refine ⟨labelWt Tag.E6 b, ?_, hc.symm⟩
  rcases b with i | ⟨β, hβ⟩
  · exact Or.inr rfl
  · exact Or.inl hβ

theorem units_map_entrywiseHom_rootDiagUnit (σ : L ≃+* L) (a : Fin Tag.E6.rank → Lˣ) :
    Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E6 a) =
      rootDiagUnit Tag.E6 (fun j => Units.map (σ : L →+* L).toMonoidHom (a j)) :=
  Units.ext (CFSG.LieType.Chevalley.entrywise_rootDiag σ.toRingHom a)

theorem rootChar_hsl (u : Lˣ) (β γ : Fin Tag.E6.rank → ℤ) :
    rootChar (fun j => u ^ iform β (Pi.single j 1)) γ = u ^ iform β γ := by
  rw [← iform_eq_sum_mul_iform_single β γ]
  unfold rootChar
  simp only [← zpow_mul]
  exact CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum _ _ _

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
