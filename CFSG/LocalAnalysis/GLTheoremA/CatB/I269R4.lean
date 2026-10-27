module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TOuter
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I269R

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three

theorem units_zmod2_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  apply Units.ext
  have := u.ne_zero
  generalize (u : ZMod 2) = x at this ⊢
  revert x
  decide

section PartA


theorem d4Graph_zero : d4Graph (ZMod 2) 0 = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_d4Graph]
  simp

theorem d4Graph_add (a b : ℕ) :
    d4Graph (ZMod 2) (a + b) = d4Graph (ZMod 2) a * d4Graph (ZMod 2) b := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_d4Graph, coe_d4Graph, coe_d4Graph, pow_add]
  group

theorem d4Graph_three : d4Graph (ZMod 2) 3 = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have h3 : d4P (ZMod 2) ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 (ZMod 2)
  rw [coe_d4Graph, h3]
  simp

theorem exactNormalAut_one_zero : exactNormalAut Tag.D4 (ZMod 2) 1 1 0 = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_exactNormalAut_zero, CFSG.StandardType.MpStdE6.rootDiagUnit_one, one_mul, inv_one, mul_one]
  have : Units.map (entrywiseHom (1 : ZMod 2 ≃+* ZMod 2).toRingHom) (h : ModGL Tag.D4 (ZMod 2)) = h :=
    Units.ext (entrywise_id _)
  rw [this]
  rfl

theorem exists_inner_mul_graph (γ : MulAut (adjointGroup Tag.D4 (ZMod 2))) (hγ : γ ^ 3 = 1) :
    ∃ (g : adjointGroup Tag.D4 (ZMod 2)) (ε : ℕ), ε < 3 ∧ γ = MulAut.conj g * d4Graph (ZMod 2) ε := by
  obtain ⟨g, a, σ, ε, hε, -, h⟩ := exists_cube_normal_form_sigma γ hγ
  have hz2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hσ : σ = 1 := RingEquiv.ext fun x => by
    rcases hz2 x with rfl | rfl <;> simp
  have ha : a = 1 := funext fun i => units_zmod2_eq_one _
  subst hσ ha
  rw [exactNormalAut_one_zero, one_mul] at h
  exact ⟨g, ε, hε, h⟩

theorem innerPair_adjoint : InnerPair (adjointGroup Tag.D4 (ZMod 2)) := by
  intro α β hα hβ
  obtain ⟨g, ε, hε, hαe⟩ := exists_inner_mul_graph α hα
  obtain ⟨h, δ, hδ, hβe⟩ := exists_inner_mul_graph β hβ
  have h12 : d4Graph (ZMod 2) 1 * d4Graph (ZMod 2) 2 = 1 := by
    rw [← d4Graph_add]; exact d4Graph_three
  have h21 : d4Graph (ZMod 2) 2 * d4Graph (ZMod 2) 1 = 1 := by
    rw [← d4Graph_add]; exact d4Graph_three
  interval_cases ε <;> interval_cases δ
  · exact Or.inl ⟨g, by rw [hαe, d4Graph_zero, mul_one]⟩
  · exact Or.inl ⟨g, by rw [hαe, d4Graph_zero, mul_one]⟩
  · exact Or.inl ⟨g, by rw [hαe, d4Graph_zero, mul_one]⟩
  · exact Or.inr (Or.inl ⟨h, by rw [hβe, d4Graph_zero, mul_one]⟩)
  · refine Or.inr (Or.inr (Or.inr ⟨g * h⁻¹, ?_⟩))
    rw [hαe, hβe, map_mul, map_inv]
    group
  · refine Or.inr (Or.inr (Or.inl ⟨g * d4Graph (ZMod 2) 1 h, ?_⟩))
    rw [hαe, hβe, map_mul]
    calc MulAut.conj g * MulAut.conj (d4Graph (ZMod 2) 1 h) =
        MulAut.conj g * MulAut.conj (d4Graph (ZMod 2) 1 h) * (d4Graph (ZMod 2) 1 * d4Graph (ZMod 2) 2) := by
          rw [h12, mul_one]
      _ = MulAut.conj g * (MulAut.conj (d4Graph (ZMod 2) 1 h) * d4Graph (ZMod 2) 1) * d4Graph (ZMod 2) 2 := by
          group
      _ = _ := by rw [← mul_conj_eq]; group
  · exact Or.inr (Or.inl ⟨h, by rw [hβe, d4Graph_zero, mul_one]⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨g * d4Graph (ZMod 2) 2 h, ?_⟩))
    rw [hαe, hβe, map_mul]
    calc MulAut.conj g * MulAut.conj (d4Graph (ZMod 2) 2 h) =
        MulAut.conj g * MulAut.conj (d4Graph (ZMod 2) 2 h) * (d4Graph (ZMod 2) 2 * d4Graph (ZMod 2) 1) := by
          rw [h21, mul_one]
      _ = MulAut.conj g * (MulAut.conj (d4Graph (ZMod 2) 2 h) * d4Graph (ZMod 2) 2) * d4Graph (ZMod 2) 1 := by
          group
      _ = _ := by rw [← mul_conj_eq]; group
  · refine Or.inr (Or.inr (Or.inr ⟨g * h⁻¹, ?_⟩))
    rw [hαe, hβe, map_mul, map_inv]
    group

end PartA

section PartC


theorem outerNoFive_adjoint : OuterNoFive (adjointGroup Tag.D4 (ZMod 2)) := by
  intro α hα hout y hy5 hfix
  have hdvd := D4T.outer_card_dvd (F := ZMod 2) (by simp) α hα hout
  have hy : y ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α :=
    CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.2 hfix
  have h5 : 5 ∣ Nat.card (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) := by
    have := Subgroup.orderOf_dvd_natCard _ hy
    rwa [hy5] at this
  have h5' := h5.trans hdvd
  revert h5'
  unfold CFSG.Open.ordTrialityD4
  decide +kernel

end PartC

end I269R

end CFSG.LocalAnalysis.GLTheoremA

end
