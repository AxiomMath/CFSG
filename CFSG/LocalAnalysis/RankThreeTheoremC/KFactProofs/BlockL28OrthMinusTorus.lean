module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusFives

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail Matrix

variable {K : Type} [Field K]

@[expose] def minusTorusVec {n : ℕ} (k : ℕ) (t : Fin k → Kˣ) (i : Fin n) : Kˣ :=
  if h : (i : ℕ) < k then t ⟨i, h⟩ else if (i : ℕ) = k then (∏ j, t j)⁻¹ else 1

theorem minusTorusVec_one {n : ℕ} (k : ℕ) : minusTorusVec (n := n) k (1 : Fin k → Kˣ) = 1 := by
  funext i
  simp only [minusTorusVec, Pi.one_apply, Finset.prod_const_one, inv_one]
  split_ifs <;> rfl

theorem minusTorusVec_mul {n : ℕ} (k : ℕ) (t s : Fin k → Kˣ) :
    minusTorusVec (n := n) k (t * s) = minusTorusVec k t * minusTorusVec k s := by
  funext i
  simp only [minusTorusVec, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
  split_ifs <;> simp

theorem prod_minusTorusVec {n k : ℕ} (hn : k + 1 ≤ n) (t : Fin k → Kˣ) :
    ∏ i, minusTorusVec (n := n) k t i = 1 := by
  let g : ℕ → Kˣ := fun m => if h : m < k then t ⟨m, h⟩ else if m = k then (∏ j, t j)⁻¹ else 1
  have e : ∏ i, minusTorusVec (n := n) k t i = ∏ i : Fin n, g i := rfl
  have h1 : ∏ i ∈ Finset.range k, g i = ∏ j, t j := by
    rw [← Fin.prod_univ_eq_prod_range g k]
    exact Finset.prod_congr rfl fun j _ => by simp [g, j.isLt]
  rw [e, Fin.prod_univ_eq_prod_range g n, ← Finset.prod_range_mul_prod_Ico g hn,
    Finset.prod_eq_one (s := Finset.Ico (k + 1) n) fun m hm => ?_, mul_one,
    Finset.prod_range_succ, h1]
  · simp [g]
  · rw [Finset.mem_Ico] at hm
    have h1 : ¬ m < k := by omega
    have h2 : m ≠ k := by omega
    simp only [g, h1, h2, ↓reduceDIte, ↓reduceIte]

variable (K) in
@[expose] noncomputable def minusTorusSL (k : ℕ) {n : ℕ} (hn : k + 1 ≤ n) :
    (Fin k → Kˣ) →* SpecialLinearGroup (Fin n) K where
  toFun t := ⟨diagonal fun i => (minusTorusVec k t i : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_minusTorusVec hn, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [minusTorusVec_one]
  map_mul' t s := by
    apply Subtype.ext
    change diagonal (fun i => (minusTorusVec k (t * s) i : K)) =
      diagonal (fun i => (minusTorusVec k t i : K)) * diagonal (fun i => (minusTorusVec k s i : K))
    rw [diagonal_mul_diagonal, minusTorusVec_mul]
    rfl

theorem coe_minusTorusSL {k n : ℕ} (hn : k + 1 ≤ n) (t : Fin k → Kˣ) :
    ((minusTorusSL K k hn t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (minusTorusVec k t i : K) :=
  rfl

variable [Finite K] [CharP K 2] {r s : ℕ} {d : Fin (s + 1) → ℕ}

variable (b c : K) in
@[expose] noncomputable def minusParabTorus (k : ℕ) (hk : k + 1 ≤ r) (hr : 3 ≤ r) :
    (Fin k → Kˣ) →* ↥(orthParab r (minusTailForm K b c) d) :=
  (((orthDMapOneHom K r).comp ((SpecialLinearGroup.toGL).comp (minusTorusSL K k hk))).codRestrict
      (orthElementaryGroup (quadTail r (minusTailForm K b c))) fun t =>
        NonsplitOrthogonalCover.dMap_one_mem_orthElementaryGroup hr
          (minusTorusSL K k hk t).2).codRestrict _ fun t =>
    mem_orthParab.2 fun i => map_tailFlag_dMap (blockTriangular_diagonal _) _ _

omit [Finite K] in
theorem minusParabTorus_injective (b c : K) (k : ℕ) (hk : k + 1 ≤ r) (hr : 3 ≤ r) :
    Function.Injective (minusParabTorus b c k hk hr (K := K) (d := d)) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1 : dMap (SpecialLinearGroup.toGL (minusTorusSL K k hk t))
      (1 : (Fin 2 → K) ≃ₗ[K] _) = 1 := congrArg (fun x : ↥(orthParab r (minusTailForm K b c) d) =>
        ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))) ht
  have h2 := congrArg orthCoefMat h1
  rw [orthCoefMat_dMap, orthCoefMat_one] at h2
  funext j
  have hj := congrFun (congrFun h2 ⟨j, by omega⟩) ⟨j, by omega⟩
  have hj' : ((minusTorusVec (n := r) k t ⟨j, by omega⟩ : Kˣ) : K) = 1 := by
    simpa [coe_minusTorusSL] using hj
  simp only [minusTorusVec, j.isLt, ↓reduceDIte, Fin.eta] at hj'
  exact Units.ext (by simpa using hj')

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
