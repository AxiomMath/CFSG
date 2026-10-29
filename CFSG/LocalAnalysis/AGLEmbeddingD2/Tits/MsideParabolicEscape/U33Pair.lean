module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Isotropic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Regular

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

open Matrix

variable {F : Type} [Field F]

theorem form_adj (σ : F →+* F) (A : Matrix (Fin 3) (Fin 3) F) (p q : Fin 3 → F) :
    (σ ∘ A.mulVec p) ⬝ᵥ q = (σ ∘ p) ⬝ᵥ (adj σ A).mulVec q := by
  simp only [dotProduct, Function.comp_apply, Matrix.mulVec, map_sum, map_mul, adj,
    Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem exists_vec_ne_zero (ν : Matrix (Fin 3) (Fin 3) F) (h : ν ≠ 0) :
    ∃ a : Fin 3 → F, ν.mulVec a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  ext i j
  have := congrFun (hcon (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem image_mem_line (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (ν B : Matrix (Fin 3) (Fin 3) F)
    (hνB : ν * B = 0) (hBB : B * B = 0) (hadjν : adj σ ν = -ν) (hadjB : adj σ B = -B)
    (hν2 : ν * ν = 0) (a : Fin 3 → F) (hu : ν.mulVec a ≠ 0) (v : Fin 3 → F) :
    ∃ c : F, B.mulVec v = c • ν.mulVec a := by
  by_contra hcon
  push Not at hcon
  have hli : LinearIndependent F ![ν.mulVec a, B.mulVec v] := by
    rw [LinearIndependent.pair_iff' hu]
    intro c hc
    exact hcon c hc.symm
  refine no_two_isotropic σ hσσ (ν.mulVec a) (B.mulVec v) ?_ ?_ ?_ hli
  · rw [form_adj, hadjν]
    simp [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hν2]
  · rw [form_adj, hadjν]
    simp [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hνB]
  · rw [form_adj, hadjB]
    simp [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hBB]

theorem pair_proportional (σ : F →+* F) (hσσ : ∀ x, σ (σ x) = x) (ν μ : Matrix (Fin 3) (Fin 3) F)
    (hν2 : ν * ν = 0) (hμ2 : μ * μ = 0) (hνμ : ν * μ = 0)
    (hadjν : adj σ ν = -ν) (hadjμ : adj σ μ = -μ) (hν0 : ν ≠ 0) :
    ∃ c : F, μ = c • ν := by
  obtain ⟨a, ha⟩ := exists_vec_ne_zero ν hν0
  set u : Fin 3 → F := ν.mulVec a with hu
  have colν : ∀ j, ∃ k : F, ν.mulVec (Pi.single j 1) = k • u := fun j =>
    image_mem_line σ hσσ ν ν hν2 hν2 hadjν hadjν hν2 a ha _
  have colμ : ∀ j, ∃ k : F, μ.mulVec (Pi.single j 1) = k • u := fun j =>
    image_mem_line σ hσσ ν μ hνμ hμ2 hadjν hadjμ hν2 a ha _
  choose κ hκ using colν
  choose l hl using colμ
  have eν : ∀ i j, ν i j = κ j * u i := fun i j => by
    have := congrFun (hκ j) i
    simpa [Matrix.mulVec_single_one] using this
  have eμ : ∀ i j, μ i j = l j * u i := fun i j => by
    have := congrFun (hl j) i
    simpa [Matrix.mulVec_single_one] using this
  have r1 : ∀ i j, σ (κ i) * σ (u j) = -(κ j * u i) := fun i j => by
    have := congrFun (congrFun hadjν i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at this
    rw [eν j i, map_mul] at this
    rw [this, eν i j]
  have r2 : ∀ i j, σ (l i) * σ (u j) = -(l j * u i) := fun i j => by
    have := congrFun (congrFun hadjμ i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at this
    rw [eμ j i, map_mul] at this
    rw [this, eμ i j]
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  set p : F := -σ (κ i0) / u i0 with hp
  set q : F := -σ (l i0) / u i0 with hq
  have hκp : ∀ j, κ j = p * σ (u j) := fun j => by
    have := r1 i0 j
    rw [hp]
    field_simp
    linear_combination this
  have hlq : ∀ j, l j = q * σ (u j) := fun j => by
    have := r2 i0 j
    rw [hq]
    field_simp
    linear_combination this
  have hp0 : p ≠ 0 := by
    intro hp0
    apply hν0
    ext i j
    rw [eν, hκp, hp0]
    simp
  refine ⟨q / p, ?_⟩
  ext i j
  rw [eμ, Matrix.smul_apply, eν, hlq, hκp]
  simp only [smul_eq_mul]
  field_simp

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
