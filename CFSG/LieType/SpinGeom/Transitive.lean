module

public import CFSG.LieType.SpinGeom.Mem
public import CFSG.LieType.SpinGeom.Count

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Realized

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev Realized (f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)) : Prop :=
  ∃ h ∈ spinSeven K, ∀ v,
    ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = f v

private theorem Realized.comp {f g : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)}
    (hf : Realized f) (hg : Realized g) : Realized (fun v => f (g v)) := by
  obtain ⟨h₁, hm₁, e₁⟩ := hf
  obtain ⟨h₂, hm₂, e₂⟩ := hg
  refine ⟨h₁ * h₂, mul_mem hm₁ hm₂, fun v => ?_⟩
  have h : (((h₁ * h₂ : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      ((h₁ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        ((h₂ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := rfl
  rw [h, ← Matrix.mulVec_mulVec, e₂, e₁]

private theorem Realized.inv {f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K)}
    (hf : Realized f) :
    ∃ f' : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f' ∧ ∀ v, f' (f v) = v := by
  obtain ⟨h, hm, e⟩ := hf
  let f' : (Fin (2 * 4) → K) → (Fin (2 * 4) → K) := fun v =>
    (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v
  refine ⟨f', ⟨h⁻¹, inv_mem hm, fun v => rfl⟩, fun v => ?_⟩
  have h1 : ((((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) *
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 := by
    have h2 : ((h⁻¹ * h : Om8 K) : GL (Fin (2 * 4)) K) = 1 := by
      rw [inv_mul_cancel]
      rfl
    exact congrArg (fun u : GL (Fin (2 * 4)) K =>
      (u : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) h2
  calc f' (f v)
      = (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ f v := rfl
    _ = (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          ((((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) *ᵥ v) := by
        rw [← e v]
    _ = (((((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) *
          (((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K))) *ᵥ v := by
        rw [Matrix.mulVec_mulVec]
    _ = v := by rw [h1, Matrix.one_mulVec]

private theorem realized_elemMap (a b : Fin 4) (hab : a ≠ b) (c : K) :
    Realized (elemMap K a b c) :=
  exists_mem_spinSeven_elemMap a b hab c

private theorem realized_longMap {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (m : K) :
    Realized (longMap K a b c d m) :=
  exists_mem_spinSeven_longMap hab hcd hac had hbc hbd m

private theorem realized_spinElt (c m : Fin 3 → K) :
    Realized (spinElt K c m 1) :=
  exists_mem_spinSeven_spinElt c m 1 (by simp)

end Realized

section Coordinates

variable {K : Type} [Field K]

private noncomputable def n1 (v : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  longMap K 0 1 2 3 1 (longMap K 2 3 0 1 1 (longMap K 0 1 2 3 1 v))

private noncomputable def n2 (v : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  elemMap K 0 1 1 (elemMap K 1 0 1 (elemMap K 0 1 1 v))

end Coordinates

section RealizeMaps

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem realized_n1 : Realized (K := K) n1 := by
  have hL : Realized (K := K) (longMap K 0 1 2 3 1) :=
    realized_longMap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1
  have hM : Realized (K := K) (longMap K 2 3 0 1 1) :=
    realized_longMap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 1
  simpa [n1] using hL.comp (hM.comp hL)

private theorem realized_n2 : Realized (K := K) n2 := by
  have hE : Realized (K := K) (elemMap K 0 1 1) :=
    realized_elemMap 0 1 (by decide) 1
  have hM : Realized (K := K) (elemMap K 1 0 1) :=
    realized_elemMap 1 0 (by decide) 1
  simpa [n2] using hE.comp (hM.comp hE)

omit [Finite K] in
private theorem n1_frameE_zero : n1 (K := K) (frameE K 0) = frameF K 1 := by
  apply vec_ext
  · intro k
    fin_cases k <;>
      simp [n1, coordX_longMap, coordY_longMap, coordX_frameE, coordY_frameE, coordX_frameF,
        CharTwo.add_self_eq_zero]
  · intro k
    fin_cases k <;>
      simp [n1, coordX_longMap, coordY_longMap, coordX_frameE, coordY_frameE, coordY_frameF,
        CharTwo.add_self_eq_zero]

omit [Finite K] in
private theorem n2_frameF_one : n2 (K := K) (frameF K 1) = frameF K 0 := by
  apply vec_ext
  · intro k
    fin_cases k <;>
      simp [n2, coordX_elemMap, coordX_frameF, CharTwo.add_self_eq_zero]
  · intro k
    fin_cases k <;>
      simp [n2, coordY_elemMap, coordY_frameF, CharTwo.add_self_eq_zero]

end RealizeMaps

section StabilizerOrbit

variable {K : Type} [Field K] [CharP K 2]

private theorem spinElt_frameF_zero_eq (w : Fin (2 * 4) → K)
    (hQ : coordinateQuadPlus 4 K w = 0) (hy0 : coordY K w 0 = 1) :
    spinElt K (fun j => coordY K w j.succ) (fun j => coordX K w j.succ) 1 (frameF K 0) = w := by
  have hx0 : coordX K w 0 =
      (fun j : Fin 3 => coordY K w j.succ) ⬝ᵥ (fun j : Fin 3 => coordX K w j.succ) := by
    have hsum : coordX K w 0 + ∑ j : Fin 3, coordX K w j.succ * coordY K w j.succ = 0 := by
      have h := hQ
      rw [quad_eq_sum, Fin.sum_univ_succ, hy0] at h
      simpa using h
    rw [CharTwo.add_eq_zero] at hsum
    rw [hsum]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [coordX_spinElt_zero]
      simp only [xvec_frameF, yvec_frameF_zero, coordX_frameF, Matrix.adjugate_one,
        Matrix.transpose_one, Matrix.mulVec_zero, dotProduct_zero, coordY_frameF, if_true,
        add_zero, zero_add, one_mul]
      exact hx0.symm
    · rw [coordX_spinElt_succ]
      simp [xvec_frameF, coordY_frameF]
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [coordY_spinElt_zero]
      simp [coordY_frameF, hy0]
    · rw [coordY_spinElt_succ]
      simp [yvec_frameF_zero, xvec_frameF, Matrix.adjugate_one, coordY_frameF]

end StabilizerOrbit

section IntoStab

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_realized_coordY_zero_eq_one_of_ne (v : Fin (2 * 4) → K)
    {k : Fin 4} (hk : k ≠ 0) (hyk : coordY K v k ≠ 0) :
    ∃ f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f ∧ coordY K (f v) 0 = 1 := by
  classical
  let c : K := (1 - coordY K v 0) / coordY K v k
  refine ⟨elemMap K k 0 c, realized_elemMap k 0 hk c, ?_⟩
  rw [coordY_elemMap]
  simp only [if_true]
  have hc : c * coordY K v k = 1 - coordY K v 0 := by
    dsimp [c]
    rw [div_mul_cancel₀ _ hyk]
  rw [hc]
  ring

private theorem exists_realized_coordY_zero_eq_one_of_y0 (v : Fin (2 * 4) → K)
    (hy0 : coordY K v 0 ≠ 0) (hy : ∀ k : Fin 4, k ≠ 0 → coordY K v k = 0) :
    ∃ f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f ∧ coordY K (f v) 0 = 1 := by
  have h1 : coordY K (elemMap K 0 1 1 v) 1 ≠ 0 := by
    rw [coordY_elemMap]
    simp [hy 1 (by decide), hy0]
  obtain ⟨f, hf, hf0⟩ :=
    exists_realized_coordY_zero_eq_one_of_ne (elemMap K 0 1 1 v) (k := 1) (by decide) h1
  exact ⟨fun v => f (elemMap K 0 1 1 v),
    hf.comp (realized_elemMap 0 1 (by decide) 1), hf0⟩

private theorem exists_realized_coordY_zero_eq_one_of_y_ne_zero (v : Fin (2 * 4) → K)
    (hy : ∃ k : Fin 4, coordY K v k ≠ 0) :
    ∃ f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f ∧ coordY K (f v) 0 = 1 := by
  classical
  by_cases h0 : coordY K v 0 = 0
  · obtain ⟨k, hk⟩ := hy
    have hk0 : k ≠ 0 := by
      intro h
      subst h
      exact hk h0
    exact exists_realized_coordY_zero_eq_one_of_ne v hk0 hk
  · by_cases hex : ∃ k : Fin 4, k ≠ 0 ∧ coordY K v k ≠ 0
    · obtain ⟨k, hk0, hk⟩ := hex
      exact exists_realized_coordY_zero_eq_one_of_ne v hk0 hk
    · exact exists_realized_coordY_zero_eq_one_of_y0 v h0 fun k hk0 => by
        by_contra hk
        exact hex ⟨k, hk0, hk⟩

private theorem exists_realized_y_ne_of_y_zero (v : Fin (2 * 4) → K)
    (hy : ∀ k : Fin 4, coordY K v k = 0) (hx : ∃ k : Fin 4, coordX K v k ≠ 0) :
    ∃ f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f ∧ ∃ k : Fin 4, coordY K (f v) k ≠ 0 := by
  obtain ⟨d, hd⟩ := hx
  classical
  fin_cases d
  · refine ⟨longMap K 2 3 1 0 1, realized_longMap (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) 1, ⟨1, ?_⟩⟩
    rw [coordY_longMap]
    simp [hy]
    exact hd
  · refine ⟨longMap K 2 3 0 1 1, realized_longMap (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) 1, ⟨0, ?_⟩⟩
    rw [coordY_longMap]
    simp [hy]
    exact hd
  · refine ⟨longMap K 1 3 0 2 1, realized_longMap (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) 1, ⟨0, ?_⟩⟩
    rw [coordY_longMap]
    simp [hy]
    exact hd
  · refine ⟨longMap K 1 2 0 3 1, realized_longMap (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) 1, ⟨0, ?_⟩⟩
    rw [coordY_longMap]
    simp [hy]
    exact hd

private theorem exists_realized_coordY_zero_eq_one (b : Fin (2 * 4) → K) (hb : b ≠ 0) :
    ∃ f : (Fin (2 * 4) → K) → (Fin (2 * 4) → K),
      Realized f ∧ coordY K (f b) 0 = 1 := by
  classical
  by_cases hy : ∃ k : Fin 4, coordY K b k ≠ 0
  · exact exists_realized_coordY_zero_eq_one_of_y_ne_zero b hy
  · have hy' : ∀ k : Fin 4, coordY K b k = 0 := fun k => by
      by_contra hk
      exact hy ⟨k, hk⟩
    have hx : ∃ k : Fin 4, coordX K b k ≠ 0 := by
      by_contra hx
      apply hb
      apply vec_ext
      · intro k
        rw [coordX_zero]
        by_contra hk
        exact hx ⟨k, hk⟩
      · intro k
        rw [coordY_zero]
        exact hy' k
    obtain ⟨f, hf, k, hk⟩ := exists_realized_y_ne_of_y_zero b hy' hx
    obtain ⟨g, hg, hg0⟩ := exists_realized_coordY_zero_eq_one_of_y_ne_zero (f b) ⟨k, hk⟩
    exact ⟨fun v => g (f v), hg.comp hf, hg0⟩

end IntoStab

theorem spinSeven_transitive (K : Type) [Field K] [Finite K] [CharP K 2]
    (b : Fin (2 * 4) → K) (hb : b ≠ 0) (hQ : coordinateQuadPlus 4 K b = 0) :
    ∃ h ∈ spinSeven K,
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = b := by
  obtain ⟨g, hg_real, hg_y⟩ := exists_realized_coordY_zero_eq_one (K := K) b hb
  have hgQ : coordinateQuadPlus 4 K (g b) = 0 := by
    obtain ⟨h, _, hact⟩ := hg_real
    calc coordinateQuadPlus 4 K (g b)
        = coordinateQuadPlus 4 K
            (((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b) := by
          rw [← hact b]
      _ = coordinateQuadPlus 4 K b := coordinateQuadPlus_mulVec_om8 h b
      _ = 0 := hQ
  let c : Fin 3 → K := fun j => coordY K (g b) j.succ
  let m : Fin 3 → K := fun j => coordX K (g b) j.succ
  have hu_real : Realized (K := K) (spinElt K c m 1) := realized_spinElt c m
  have huF0 : spinElt K c m 1 (frameF K 0) = g b := by
    dsimp [c, m]
    exact spinElt_frameF_zero_eq (g b) hgQ hg_y
  have hn1 : Realized (K := K) n1 := realized_n1
  have hn2 : Realized (K := K) n2 := realized_n2
  obtain ⟨ginv, hginv_real, hginv_g⟩ := hg_real.inv
  have hF_real : Realized (K := K)
      (fun v => ginv (spinElt K c m 1 (n2 (K := K) (n1 (K := K) v)))) :=
    hginv_real.comp (hu_real.comp (hn2.comp hn1))
  obtain ⟨h, hh, hact⟩ := hF_real
  refine ⟨h, hh, ?_⟩
  have hFE0 : (fun v => ginv (spinElt K c m 1 (n2 (K := K) (n1 (K := K) v))))
      (frameE K 0) = b := by
    calc
      (fun v => ginv (spinElt K c m 1 (n2 (K := K) (n1 (K := K) v))))
          (frameE K 0)
          = ginv (spinElt K c m 1 (n2 (K := K) (n1 (K := K) (frameE K 0)))) := rfl
      _ = ginv (spinElt K c m 1 (n2 (K := K) (frameF K 1))) := by rw [n1_frameE_zero]
      _ = ginv (spinElt K c m 1 (frameF K 0)) := by rw [n2_frameF_one]
      _ = ginv (g b) := by rw [huF0]
      _ = b := hginv_g b
  rw [← hFE0]
  exact hact (frameE K 0)

end CFSG.LieType.SpinGeom
