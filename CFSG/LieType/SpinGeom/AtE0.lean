module

public import CFSG.LieType.SpinGeom.Classify
public import CFSG.LieType.SpinGeom.Inv
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Card

variable {K : Type} [Field K] [Finite K] {C : Type} [AddCommGroup C]

omit [Finite K] in
theorem card_W_line {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (h3 : ∀ t : K, (t • frameE K 0, (0 : C)) ∈ W)
    (hline : ∀ w ∈ W, w.2 = 0 ∧ ∃ t : K, w.1 = t • frameE K 0) : Nat.card W = Nat.card K := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : K => (⟨(t • frameE K 0, 0), h3 t⟩ : W)) ⟨?_, ?_⟩)
  · intro t t' h
    exact smul_left_injective K (frameE_ne_zero (K := K)) (congrArg (fun w : W => w.1.1) h)
  · rintro ⟨w, hw⟩
    obtain ⟨h2, t, ht⟩ := hline w hw
    exact ⟨t, Subtype.ext (Prod.ext ht.symm h2.symm)⟩

omit [Finite K] in
theorem card_W_four {W : AddSubgroup ((Fin (2 * 4) → K) × C)}
    (hfour1 : ∀ w ∈ W, w.2 = 0 ∧ coordY K w.1 0 = 0 ∧ ∀ j : Fin 3, coordX K w.1 j.succ = 0)
    (hfour2 : ∀ (x₀ : K) (y : Fin 3 → K), (frameVec K x₀ 0 y 0, (0 : C)) ∈ W) :
    Nat.card W = Nat.card K ^ 4 := by
  have e : K × (Fin 3 → K) ≃ W := Equiv.ofBijective
    (fun p => (⟨(frameVec K p.1 0 p.2 0, 0), hfour2 p.1 p.2⟩ : W)) ⟨?_, ?_⟩
  · rw [← Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fin]
    ring
  · intro p p' h
    obtain ⟨h1, -, h3, -⟩ := frameVec_inj (congrArg (fun w : W => w.1.1) h)
    exact Prod.ext h1 h3
  · rintro ⟨w, hw⟩
    obtain ⟨h2, h3, h4⟩ := hfour1 w hw
    refine ⟨(coordX K w.1 0, yvec K w.1), Subtype.ext (Prod.ext ?_ h2.symm)⟩
    have h5 := frameVec_coords (K := K) w.1
    have h6 : (fun j : Fin 3 => coordX K w.1 j.succ) = 0 := funext h4
    rw [h6, h3] at h5
    exact h5

end Card

section AtE0

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spinGeom_atE0 (hq : 4 ≤ Nat.card K)
    (hTrans : ∀ b : Fin (2 * 4) → K, b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
      ∃ h ∈ spinSeven K,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = b)
    (s : ℕ) (QC : QuadraticForm K (Fin (2 * s) → K))
    (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
    (A : Subgroup (GL (Fin (2 * 4)) K))
    (hA : A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype)
    (hAfix : ∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = frameE K 0)
    (h3 : ∀ t : K, (t • frameE K 0, (0 : Fin (2 * s) → K)) ∈ W)
    (h4 : ∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0)
    (h5 : ∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 (frameE K 0) = 0)
    (h6 : ∀ M ∈ spinSeven K, Odd (orderOf M) →
      ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        frameE K 0 →
      (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
        w.2) ∈ W) ∧
      ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A)
    (h7 : ∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x (frameE K 0) = 0 →
      ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W)
    (h8 : ∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
      (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • frameE K 0)
    (h9 : ∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
      ∃ t : K, w = (t • frameE K 0, 0))
    (hcount : Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s)) : False := by
  have hq1 : 1 < Nat.card K := by omega
  have hnf := spinStabNormalForm_of_count (fun c m g hg => exists_mem_spinSeven_spinElt c m g hg)
    hTrans
  have hAnf : ∀ a ∈ A, ∃ (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K), g.det = 1 ∧ ∀ v,
      (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m g v := by
    intro a ha
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.1 (hA ha)
    exact hnf M hM (hAfix _ ha)
  obtain ⟨hζ, hX, hconj⟩ := inv_root_elements hq h6
  have hQ0 : ∀ u : Fin (2 * 4) → K, (u, (0 : Fin (2 * s) → K)) ∈ W →
      coordinateQuadPlus 4 K u = 0 := by
    intro u hu
    simpa using h4 (u, 0) hu
  have hinj : ∀ w ∈ W, w.1 = 0 → w.2 = 0 := by
    intro w hw h0
    obtain ⟨t, ht⟩ := h9 w hw fun a _ => by rw [h0, Matrix.mulVec_zero]
    exact (Prod.ext_iff.1 ht).2
  rcases classify_W h3 h5 hQ0 hinj hζ hX with hline | ⟨hfour1, hfour2⟩
  · have hα : ∀ a ∈ A, ∃ c : Fin 3 → K,
        ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c 0 1 v := by
      intro a ha
      obtain ⟨c, m, g, hg, hv⟩ := hAnf a ha
      have h7' : ∀ x : Fin (2 * 4) → K, coordY K x 0 = 0 → ∃ t : K,
          spinElt K c m g x - x = t • frameE K 0 := by
        intro x hx
        obtain ⟨-, t, ht⟩ := hline _ (h7 a ha x hx)
        exact ⟨t, by rw [← hv x]; exact ht⟩
      obtain ⟨rfl, rfl⟩ := eq_alpha_of_line h7'
      exact ⟨c, hv⟩
    have hle := card_le_of_alpha hα
    rw [card_W_line h3 hline] at hcount
    have h1 : Nat.card K ^ 4 < Nat.card K ^ (2 * 4 - 1 + 2 * s) :=
      Nat.pow_lt_pow_right hq1 (by omega)
    have h2 : Nat.card A * Nat.card K ≤ Nat.card K ^ 4 := by
      calc Nat.card A * Nat.card K ≤ Nat.card K ^ 3 * Nat.card K := Nat.mul_le_mul_right _ hle
        _ = Nat.card K ^ 4 := by ring
    omega
  · have hα : ∀ a ∈ A, ∃ c m : Fin 3 → K,
        ∀ v, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K c m 1 v := by
      intro a ha
      obtain ⟨c, m, g, hg, hv⟩ := hAnf a ha
      have h8' : ∀ y : Fin 3 → K, ∃ t : K,
          spinElt K c m g (frameVec K 0 0 y 0) - frameVec K 0 0 y 0 = t • frameE K 0 := by
        intro y
        obtain ⟨t, ht⟩ := h8 a ha (frameVec K 0 0 y 0, 0) (hfour2 0 y)
        exact ⟨t, by rw [← hv]; exact ht⟩
      obtain rfl := eq_one_of_four hg h8'
      exact ⟨c, m, hv⟩
    have h9' : ∀ y : Fin 3 → K, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        frameVec K 0 0 y 0 = frameVec K 0 0 y 0) → y = 0 := by
      intro y hy
      obtain ⟨t, ht⟩ := h9 (frameVec K 0 0 y 0, 0) (hfour2 0 y) hy
      have h0 : frameVec K 0 0 y 0 = t • frameE K 0 := (Prod.ext_iff.1 ht).1
      have h1 : frameVec K 0 0 y 0 = frameVec K t 0 0 0 := by
        rw [h0, frameE_zero_eq, frameVec_smul]
        simp
      exact (frameVec_inj h1).2.2.1
    exact case_four_false hα hconj h9' (by rw [← card_W_four hfour1 hfour2]; exact hcount)

end AtE0

end CFSG.LieType.SpinGeom
