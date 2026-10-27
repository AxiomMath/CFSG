module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace

public noncomputable section

open scoped TensorProduct

namespace CFSG.LinearAlgebra.ExteriorIncidence

universe u v w

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {I : Type w} [Fintype I] [LinearOrder I]

def incidence (b : Module.Basis I k V) :
    ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V →ₗ[k]
      ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V :=
  ∑ i, TensorProduct.map
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i))
    (LinearMap.mulLeft k (ExteriorAlgebra.ι k (b i)))

omit [LinearOrder I] in
theorem incidence_tmul (b : Module.Basis I k V) (p q : ExteriorAlgebra k V) :
    incidence b (p ⊗ₜ[k] q) =
      ∑ i, CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i) p
        ⊗ₜ[k] (ExteriorAlgebra.ι k (b i) * q) := by
  simp [incidence, LinearMap.sum_apply]

def coordinateContract (b : Module.Basis I k V) (s : Finset I) :
    ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V →ₗ[k] ExteriorAlgebra k V :=
  (TensorProduct.lid k (ExteriorAlgebra k V)).toLinearMap.comp
    (TensorProduct.map (b.ExteriorAlgebra.coord s) LinearMap.id)

omit [Fintype I] in
theorem coordinateContract_tmul (b : Module.Basis I k V) (s : Finset I)
    (p q : ExteriorAlgebra k V) :
    coordinateContract b s (p ⊗ₜ[k] q) = b.ExteriorAlgebra.coord s p • q := by
  simp [coordinateContract]

omit [Fintype I] in
private theorem erase_ne_erase (s : Finset I) {i j : I} (hi : i ∈ s)
    (hji : j ≠ i) : s.erase j ≠ s.erase i := by
  intro h
  have hmem : i ∈ s.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩
  rw [h] at hmem
  simp at hmem

theorem coordinateContract_incidence_basis (b : Module.Basis I k V) (s : Finset I)
    {i : I} (hi : i ∈ s) (q : ExteriorAlgebra k V) :
    coordinateContract b (s.erase i) (incidence b (b.ExteriorAlgebra s ⊗ₜ[k] q)) =
      TauCeti.ExteriorAlgebra.basisEraseSign i s • (ExteriorAlgebra.ι k (b i) * q) := by
  rw [incidence_tmul, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis, if_pos hi]
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign i s) with h | h <;>
      simp [h, coordinateContract_tmul, Module.Basis.coord_apply]
  · intro j _ hji
    rw [TauCeti.ExteriorAlgebra.contractLeft_coord_basis]
    by_cases hj : j ∈ s
    · rw [if_pos hj]
      have hne := erase_ne_erase s hi hji
      rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign j s) with h | h <;>
        simp [h, coordinateContract_tmul, Module.Basis.coord_apply, hne.symm]
    · simp [hj]
  · simp

theorem incidence_basis_tmul_eq_zero_iff (b : Module.Basis I k V) (s : Finset I)
    (q : ExteriorAlgebra k V) :
    incidence b (b.ExteriorAlgebra s ⊗ₜ[k] q) = 0 ↔
      ∀ i ∈ s, ExteriorAlgebra.ι k (b i) * q = 0 := by
  constructor
  · intro h i hi
    have heq := coordinateContract_incidence_basis b s hi q
    rw [h, map_zero] at heq
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign i s) with hs | hs <;>
      simpa [hs] using heq.symm
  · intro h
    rw [incidence_tmul]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · simp [h i hi]
    · simp [hi]

omit [Fintype I] in
theorem coord_creation_contraction (b : Module.Basis I k V) (i : I) (s : Finset I)
    (q : ExteriorAlgebra k V) :
    b.ExteriorAlgebra.coord s
      (ExteriorAlgebra.ι k (b i) *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i) q) =
      if i ∈ s then b.ExteriorAlgebra.coord s q else 0 := by
  classical
  let L : ExteriorAlgebra k V →ₗ[k] k :=
    (b.ExteriorAlgebra.coord s).comp
      ((LinearMap.mulLeft k (ExteriorAlgebra.ι k (b i))).comp
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i)))
  have hL : L = if i ∈ s then b.ExteriorAlgebra.coord s else 0 := by
    apply b.ExteriorAlgebra.ext
    intro t
    simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis]
    by_cases ht : i ∈ t <;> by_cases hs : i ∈ s <;>
      simp [ht, hs, Module.Basis.coord_apply]
    all_goals
      have hne : t ≠ s := by intro h; subst t; contradiction
      simp [hne.symm]
  by_cases hs : i ∈ s <;>
    simpa [L, hs] using congrArg (fun f : ExteriorAlgebra k V →ₗ[k] k => f q) hL

theorem coord_eq_zero_of_incidence_basis (b : Module.Basis I k V) (s t : Finset I)
    (q : ExteriorAlgebra k V) (h : incidence b (b.ExteriorAlgebra s ⊗ₜ[k] q) = 0)
    (hst : ¬ s ⊆ t) : b.ExteriorAlgebra.coord t q = 0 := by
  classical
  obtain ⟨i, hi, hit⟩ := Finset.not_subset.mp hst
  have hw := (incidence_basis_tmul_eq_zero_iff b s q).mp h i hi
  have hc := congrArg
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i)) hw
  rw [CliffordAlgebra.contractLeft_ι_mul] at hc
  have hc' : q - ExteriorAlgebra.ι k (b i) *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i) q = 0 := by
    simpa [Module.Basis.coord_apply] using hc
  have he : q = ExteriorAlgebra.ι k (b i) *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i) q :=
    sub_eq_zero.mp hc'
  have hcoord := coord_creation_contraction b i t q
  rw [← he, if_neg hit] at hcoord
  exact hcoord

omit [Fintype I] in
theorem coord_eq_zero_of_degree (b : Module.Basis I k V) {r : ℕ}
    (q : ⋀[k]^r V) (t : Finset I) (ht : t.card ≠ r) :
    b.ExteriorAlgebra.coord t (q : ExteriorAlgebra k V) = 0 := by
  let L : (⋀[k]^r V) →ₗ[k] k :=
    (b.ExteriorAlgebra.coord t).comp (⋀[k]^r V).subtype
  have hL : L = 0 := by
    apply (b.exteriorPower r).ext
    intro s
    have hne : (s : Finset I) ≠ t := by
      intro h
      apply ht
      rw [← h]
      exact s.property
    rw [LinearMap.zero_apply]
    change b.ExteriorAlgebra.coord t ((b.exteriorPower r s : ⋀[k]^r V) :
      ExteriorAlgebra k V) = 0
    rw [← ExteriorAlgebra.basis_eq_coe_basis]
    simp [Module.Basis.coord_apply, hne]
  exact congrArg (fun f : (⋀[k]^r V) →ₗ[k] k => f q) hL

theorem exists_eq_ι_mul_basis_of_incidence (b : Module.Basis I k V) (s : Finset I)
    (q : ⋀[k]^(s.card + 1) V)
    (h : incidence b (b.ExteriorAlgebra s ⊗ₜ[k] (q : ExteriorAlgebra k V)) = 0) :
    ∃ v : V, (q : ExteriorAlgebra k V) = ExteriorAlgebra.ι k v * b.ExteriorAlgebra s := by
  classical
  let L : V →ₗ[k] ExteriorAlgebra k V :=
    (LinearMap.mulRight k (b.ExteriorAlgebra s)).comp (ExteriorAlgebra.ι k)
  have hspan : Submodule.span k
      (b.ExteriorAlgebra '' {t : Finset I | s ⊆ t ∧ t.card = s.card + 1}) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, ⟨hst, ht⟩, rfl⟩
    have hnot : ¬ t ⊆ s := by
      intro hts
      have := Finset.card_le_card hts
      omega
    obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hnot
    have heq : insert j s = t :=
      Finset.eq_of_subset_of_card_le (Finset.insert_subset_iff.mpr ⟨hjt, hst⟩) (by
        rw [Finset.card_insert_of_notMem hjs, ht])
    have hL : L (b j) =
        TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s) • b.ExteriorAlgebra t := by
      simp [L, hjs, heq]
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign j (insert j s)) with
        hsign | hsign
    · exact ⟨b j, by simpa [hsign] using hL⟩
    · refine ⟨-b j, ?_⟩
      rw [map_neg, hL]
      simp [hsign]
  have hq : (q : ExteriorAlgebra k V) ∈ Submodule.span k
      (b.ExteriorAlgebra '' {t : Finset I | s ⊆ t ∧ t.card = s.card + 1}) := by
    apply (b.ExteriorAlgebra.mem_span_image).mpr
    intro t ht
    constructor
    · by_contra hst
      exact Finsupp.mem_support_iff.mp ht (coord_eq_zero_of_incidence_basis b s t q h hst)
    · by_contra hdeg
      exact Finsupp.mem_support_iff.mp ht (coord_eq_zero_of_degree b q t hdeg)
  obtain ⟨v, hv⟩ := hspan hq
  exact ⟨v, hv.symm⟩

def incidenceFromTensor : Module.Dual k V ⊗[k] V →ₗ[k]
    Module.End k (ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V) :=
  TensorProduct.lift
    { toFun := fun f =>
        { toFun := fun v => TensorProduct.map
            (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) f)
            (LinearMap.mulLeft k (ExteriorAlgebra.ι k v))
          map_add' := by
            intro x y
            ext p q
            simp [add_mul, TensorProduct.tmul_add]
          map_smul' := by
            intro c x
            ext p q
            simp }
      map_add' := by
        intro f g
        ext v p q
        simp [TensorProduct.add_tmul]
      map_smul' := by
        intro c f
        ext v p q
        simp [TensorProduct.smul_tmul'] }

theorem incidenceFromTensor_tmul (f : Module.Dual k V) (v : V) :
    incidenceFromTensor (f ⊗ₜ[k] v) = TensorProduct.map
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) f)
      (LinearMap.mulLeft k (ExteriorAlgebra.ι k v)) := by
  simp [incidenceFromTensor]

omit [LinearOrder I] in
theorem incidence_eq_fromTensor (b : Module.Basis I k V) :
    incidence b = incidenceFromTensor (∑ i, b.coord i ⊗ₜ[k] b i) := by
  simp [incidence, incidenceFromTensor_tmul, map_sum]

omit [LinearOrder I] in
theorem sum_dual_basis_tmul_eq {J : Type*} [Fintype J]
    (b : Module.Basis I k V) (c : Module.Basis J k V) :
    (∑ i, b.coord i ⊗ₜ[k] b i) = ∑ j, c.coord j ⊗ₜ[k] c j := by
  let := Module.Finite.of_basis b
  apply (dualTensorHomEquiv k V V).injective
  ext v
  simp only [map_sum, LinearMap.sum_apply, dualTensorHomEquiv_tmul]
  simpa only [Module.Basis.coord_apply, Module.Basis.equivFun_apply] using
    (b.sum_equivFun v).trans (c.sum_equivFun v).symm

omit [LinearOrder I] in
theorem incidence_eq {J : Type*} [Fintype J]
    (b : Module.Basis I k V) (c : Module.Basis J k V) : incidence b = incidence c := by
  rw [incidence_eq_fromTensor, incidence_eq_fromTensor, sum_dual_basis_tmul_eq b c]

omit [Fintype I] in
theorem contract_map_basis (b : Module.Basis I k V) (e : V ≃ₗ[k] V) (i : I)
    (p : ExteriorAlgebra k V) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) ((b.map e).coord i)
        (ExteriorAlgebra.map e.toLinearMap p) =
      ExteriorAlgebra.map e.toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i) p) := by
  have h : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V))
        ((b.map e).coord i)).comp (ExteriorAlgebra.map e.toLinearMap).toLinearMap =
      (ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k V)) (b.coord i)) := by
    apply b.ExteriorAlgebra.ext
    intro s
    by_cases hi : i ∈ s
    · rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign i s) with hs | hs <;>
        simp [Module.Basis.map_exteriorAlgebra, hi, hs]
    · simp [Module.Basis.map_exteriorAlgebra, hi]
  exact congrArg (fun f : ExteriorAlgebra k V →ₗ[k] ExteriorAlgebra k V => f p) h

theorem incidence_map (b : Module.Basis I k V) (e : V ≃ₗ[k] V)
    (z : ExteriorAlgebra k V ⊗[k] ExteriorAlgebra k V) :
    incidence (b.map e)
        (TensorProduct.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap
          (ExteriorAlgebra.map e.toLinearMap).toLinearMap z) =
      TensorProduct.map (ExteriorAlgebra.map e.toLinearMap).toLinearMap
        (ExteriorAlgebra.map e.toLinearMap).toLinearMap (incidence b z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p q =>
    rw [TensorProduct.map_tmul, incidence_tmul, incidence_tmul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul]
    simp only [AlgHom.toLinearMap_apply]
    rw [contract_map_basis]
    simp
  | add z z' hz hz' =>
    simp only [map_add, hz, hz']

end CFSG.LinearAlgebra.ExteriorIncidence
