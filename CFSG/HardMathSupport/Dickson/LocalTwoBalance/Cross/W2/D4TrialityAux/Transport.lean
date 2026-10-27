module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.RankThree.PartOne.K133C.InnerPlane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.RankThree.Classical.SteinbergBY CFSG.RankThree.PartOne
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.LieType.Universal.Spin

@[expose] def D4TrialityCoreFree : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ x : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), x ^ 3 = 1 →
      x ∉ matrixProjectiveImage (coordinateQuadPlus 4 K) → CoreFreeAt 3 x

theorem d4TrialityPlaneThreeBalance_of_coreFree (h : D4TrialityCoreFree) :
    D4TrialityPlaneThreeBalance := by
  intro K _ _ hK3 D hD _ ⟨t, htD, htE⟩ _ H hH _
  have hx3 : t ^ 3 = 1 := hD.2 t htD
  have ht1 : t ≠ 1 := fun h1 => htE (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hinj := K133C.conj_injective_of_center_bot
    (KCOrthogonalSubfield.center_matrix_eq_bot (by norm_num) hnd hT)
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := inferInstance
  exact localDeltaIn_eq_bot_of_coreFree Nat.prime_three hinj hH htD ht1 (h K hK3 t hx3 htE)

theorem innerAut_le_matrixProjectiveImage (K : Type) [Field K] [Finite K] :
    innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hmodel : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K)))
      .POmegaPlus 4 (ringChar K) n :=
    ⟨⟨hℓ, n.pos, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 (ringChar K) n hmodel K hK (MulEquiv.refl _)
  obtain ⟨-, -, -, -, -, hEA, -⟩ := hgates
  rw [← hEA]
  exact projective_inner_le_pointFamilyAut _

section Chevalley


@[expose] def D4OuterCoreFree : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ x : MulAut (adjointGroup Tag.D4 K), x ^ 3 = 1 → x ∉ innerAut (adjointGroup Tag.D4 K) →
      CoreFreeAt 3 x

theorem nonempty_matrixProjective_equiv_adjointGroup (K : Type) [Field K] [Finite K] :
    Nonempty (matrixProjectiveDerived (coordinateQuadPlus 4 K) ≃* adjointGroup Tag.D4 K) := by
  obtain ⟨e⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  exact ⟨(statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm.trans e⟩

theorem d4TrialityCoreFree_of_outerCoreFree (h : D4OuterCoreFree) : D4TrialityCoreFree := by
  intro K _ _ hK3 x hx3 hxE
  obtain ⟨e⟩ := nonempty_matrixProjective_equiv_adjointGroup K
  have hx' : (MulAut.congr e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hout : MulAut.congr e x ∉ innerAut (adjointGroup Tag.D4 K) := by
    rintro ⟨c, hc⟩
    apply hxE
    apply innerAut_le_matrixProjectiveImage K
    refine ⟨e.symm c, MulEquiv.ext fun y => ?_⟩
    have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.D4 K) => e.symm (φ (e y))) hc
    simp only [MulAut.conj_apply, congr_apply', MulEquiv.symm_apply_apply] at h1
    simpa [MulAut.conj_apply] using h1
  have := coreFreeAt_congr e.symm (h K hK3 _ hx' hout)
  rwa [congr_symm_congr] at this

end Chevalley

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
