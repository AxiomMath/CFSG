module

public import CFSG.LieType.Universal.SpinOmega.Products
public import CFSG.LieType.Universal.SpinOmega.Reflections
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_polar_eq_zero_map_ne_zero [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ Module.finrank K V) (u w : V) :
    ∃ a, polar Q u a = 0 ∧ polar Q w a = 0 ∧ Q a ≠ 0 := by
  classical
  set S : Submodule K V := Submodule.span K ((({u, w} : Finset V)) : Set V) with hSdef
  set T := LinearMap.BilinForm.orthogonal (polarBilin Q) S with hTdef
  have hS : Module.finrank K S ≤ 2 :=
    (finrank_span_finset_le_card ({u, w} : Finset V)).trans Finset.card_le_two
  have hT : Module.finrank K T = Module.finrank K V - Module.finrank K S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  have huS : u ∈ S := Submodule.subset_span (by simp)
  have hwS : w ∈ S := Submodule.subset_span (by simp)
  by_contra hcon
  push Not at hcon
  have hTQ : ∀ a ∈ T, Q a = 0 := fun a ha => by
    have h1 : polar Q u a = 0 := by
      simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp ha) u huS
    have h2 : polar Q w a = 0 := by
      simpa using (LinearMap.BilinForm.mem_orthogonal_iff.mp ha) w hwS
    exact hcon a h1 h2
  have hTT : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    rw [polarBilin_apply_apply, polar, hTQ _ (T.add_mem hb ha), hTQ b hb, hTQ a ha, sub_zero,
      sub_zero]
  have h1 := Submodule.finrank_mono hTT
  rw [LinearMap.BilinForm.finrank_orthogonal hQ T] at h1
  have h2 := Submodule.finrank_le T
  omega

theorem eichler_mem_range_spinAction [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ Module.finrank K V) {u w : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) : eichler Q u w ∈ (spinAction Q).range := by
  obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ hV u w
  have hmem : 1 + ι Q w * ι Q u ∈ spinGroup Q := by
    have := one_add_smul_ι_mul_ι_mem_spinGroup Q hu huw hua hwa (isUnit_iff_ne_zero.mpr ha) 1
    rwa [one_smul] at this
  refine ⟨⟨_, hmem⟩, LinearEquiv.ext fun v => ?_⟩
  rw [spinAction_apply_of_coe_eq Q hu huw rfl, eichler_apply hu huw]
  module

theorem elementaryGroup_le_range_spinAction [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ Module.finrank K V) :
    elementaryGroup Q ≤ (spinAction Q).range :=
  elementaryGroup_le_of_eichler_mem fun _ _ hu huw => eichler_mem_range_spinAction hQ hV hu huw

theorem range_spinAction_le_elementaryGroup (hQ : (polarBilin Q).Nondegenerate)
    {P P' : HypPair Q} (h : P.Orth P') : (spinAction Q).range ≤ elementaryGroup Q := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨l, hl, hev, hprod, hx⟩ := exists_list_of_spinGroup x
  rw [hx]
  exact prod_map_reflect_mem_elementaryGroup hQ h hl hev (by rw [hprod]; exact IsSquare.one)

theorem range_spinAction_eq_elementaryGroup [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ Module.finrank K V) {P P' : HypPair Q}
    (h : P.Orth P') : (spinAction Q).range = elementaryGroup Q :=
  le_antisymm (range_spinAction_le_elementaryGroup hQ h) (elementaryGroup_le_range_spinAction hQ hV)

end General

section Matrix

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]

theorem toLinEquiv_spinMatrix (Q : QuadraticForm K (σ → K)) (x : spinGroup Q) :
    toLinEquiv σ K (spinMatrix Q x) = spinAction Q x :=
  LinearEquiv.ext fun v => by rw [toLinEquiv_apply, spinMatrix_mulVec]

theorem spinMatrix_eq_comp (Q : QuadraticForm K (σ → K)) :
    spinMatrix Q = (toLinEquiv σ K).symm.toMonoidHom.comp (spinAction Q) :=
  MonoidHom.ext fun x => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.eq_symm_apply,
      toLinEquiv_spinMatrix]

theorem range_spinMatrix (Q : QuadraticForm K (σ → K)) :
    (spinMatrix Q).range = (spinAction Q).range.map (toLinEquiv σ K).symm.toMonoidHom := by
  rw [spinMatrix_eq_comp, MonoidHom.range_comp]

theorem range_spinMatrix_eq_statedOmega {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K}
    (hQ₀ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hR : (spinAction Q).range = elementaryGroup Q) :
    (spinMatrix Q).range = StatedOmega Q₀ := by
  rw [range_spinMatrix, hR, statedOmega_eq_map_elementaryGroup hQ₀ hE]

end Matrix

section Forms

variable {n : ℕ} {K : Type} [Field K]

theorem range_spinAction_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (spinAction (quadOdd n K)).range = elementaryGroup (quadOdd n K) :=
  range_spinAction_eq_elementaryGroup (nondegenerate_polarBilin_quadOdd n K h2)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_unit]
      omega)
    (oddPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))

theorem range_spinAction_quadOdd_eq_commutator (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (spinAction (quadOdd n K)).range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K),
        TauCeti.QuadraticMap.orthogonalGroup (quadOdd n K)⁆ := by
  rw [range_spinAction_quadOdd h2 hn, commutator_orthogonalGroup_quadOdd h2 hn]

theorem range_spinMatrix_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (spinMatrix (quadOdd n K)).range = StatedOmega (StatedQuadOdd n K) :=
  range_spinMatrix_eq_statedOmega (coe_quadOdd n K) (commutator_orthogonalGroup_quadOdd h2 hn)
    (range_spinAction_quadOdd h2 hn)

theorem range_spinAction_quadPlus (hn : 3 ≤ n) :
    (spinAction (quadPlus n K)).range = elementaryGroup (quadPlus n K) :=
  range_spinAction_eq_elementaryGroup (nondegenerate_polarBilin_quadPlus n K)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega)
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))

theorem range_spinAction_quadPlus_eq_commutator (hn : 3 ≤ n) :
    (spinAction (quadPlus n K)).range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)⁆ := by
  rw [range_spinAction_quadPlus hn, commutator_orthogonalGroup_quadPlus hn]

theorem range_spinMatrix_quadPlus (hn : 3 ≤ n) :
    (spinMatrix (quadPlus n K)).range = StatedOmega (StatedQuadPlus n K) :=
  range_spinMatrix_eq_statedOmega (coe_quadPlus n K) (commutator_orthogonalGroup_quadPlus hn)
    (range_spinAction_quadPlus hn)

variable {b c : K}

theorem range_spinAction_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinAction (quadMinus n K b c)).range = elementaryGroup (quadMinus n K b c) :=
  range_spinAction_eq_elementaryGroup (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega)
    (minusPair_orth (K := K) (b := b) (c := c) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]))

theorem range_spinAction_quadMinus_eq_commutator [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinAction (quadMinus n K b c)).range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ := by
  rw [range_spinAction_quadMinus hn hirr, commutator_orthogonalGroup_quadMinus hn hirr]

theorem range_spinMatrix_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinMatrix (quadMinus n K b c)).range = StatedOmega (StatedQuadMinus n K b c) :=
  range_spinMatrix_eq_statedOmega (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus hn hirr) (range_spinAction_quadMinus hn hirr)

end Forms

end CFSG.LieType.Universal.Spin
