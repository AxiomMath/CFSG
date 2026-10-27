module

public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K]

theorem exists_primitiveRoot_three (h : UnitaryFieldData 2 1 K) : ∃ ω : K, IsPrimitiveRoot ω 3 := by
  classical
  have hfin := h.finite
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      ← Nat.card_eq_fintype_card, h.card]
    norm_num
  exact ⟨g, IsPrimitiveRoot.coe_units_iff.mpr (hord ▸ IsPrimitiveRoot.orderOf g)⟩

theorem stdHerm_mulVec_mulVec (h : UnitaryFieldData 2 1 K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → K) :
    stdHerm h n (A.mulVec v) (A.mulVec w) =
      stdHerm h n v ((((A.map h.bar).transpose * A)).mulVec w) := by
  have h1 : h.bar ∘ (A.mulVec v) = (A.map h.bar).mulVec (h.bar ∘ v) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  show (h.bar ∘ (A.mulVec v)) ⬝ᵥ (A.mulVec w) =
    (h.bar ∘ v) ⬝ᵥ ((((A.map h.bar).transpose * A)).mulVec w)
  rw [h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (h.bar ∘ v) (A.map h.bar).transpose,
    Matrix.vecMul_transpose]

theorem exists_unitary_diag (h : UnitaryFieldData 2 1 K) {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (hu : (A.map h.bar).transpose * A = 1) (h3 : A ^ 3 = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
      (P.map h.bar).transpose * P = 1 ∧ A * P = P * diagonal d := by
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_three h
  have hfin := h.finite
  obtain ⟨b, μ, hbμ, hon⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hω
    (by norm_num : 3 ∣ 2 ^ 1 + 1) (stdHerm_isSymm h n) (stdHerm_separatingLeft h n)
    (fun _ : Unit => (Matrix.toLinAlgEquiv' A : Module.End K (Fin n → K)))
    (fun _ _ => Commute.refl _) (fun _ => by rw [← map_pow, h3, map_one])
    (fun _ v w => by
      rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply, stdHerm_mulVec_mulVec, hu,
        Matrix.one_mulVec])
  let e : Fin (Module.finrank K (Fin n → K)) ≃ Fin n := finCongr (Module.finrank_fin_fun K)
  let b' : Module.Basis (Fin n) K (Fin n → K) := b.reindex e
  have hb' : ∀ k, b' k = b (e.symm k) := fun k => by simp [b', Module.Basis.reindex_apply]
  refine ⟨Matrix.of fun r k => b' k r, fun k => μ () (e.symm k), ?_, ?_⟩
  · ext k l
    have h1 := hon (e.symm k) (e.symm l)
    rw [← hb', ← hb'] at h1
    have h2 : (if e.symm k = e.symm l then (1 : K) else 0) = if k = l then 1 else 0 := by
      simp [e.symm.injective.eq_iff]
    rw [h2] at h1
    simpa [Matrix.mul_apply, Matrix.one_apply, stdHerm_apply] using h1
  · ext r k
    have h1 := congrFun (hbμ () (e.symm k)) r
    rw [← hb', Matrix.toLinAlgEquiv'_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal]
    have h2 : (A * Matrix.of fun r k => b' k r) r k = A.mulVec (b' k) r := rfl
    rw [h2, h1]
    simp [mul_comm]

end CFSG.EvenSporadicStandard.M24Std.CResH3
