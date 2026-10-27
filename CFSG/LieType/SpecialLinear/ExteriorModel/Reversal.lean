module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Reversal.Basic
public import CFSG.LieType.SpecialLinear.ExteriorModel.Kron
public import CFSG.LieType.SpecialLinear.BorelStd

public section

open Module

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {R : Type*} [CommRing R] {m n : ℕ}

private noncomputable def complSubtypeEquiv (h : n ≤ m) (s : Set.powersetCard (Fin m) n) :
    (complEquiv h s).val ≃ {i : Fin m // ¬ i ∈ s.val} :=
  Equiv.subtypeEquivRight (fun i => by
    simp [complEquiv, Set.powersetCard.coe_compl])

private noncomputable def splitEquiv (h : n ≤ m) (s : Set.powersetCard (Fin m) n) :
    Fin n ⊕ Fin (m - n) ≃ Fin m :=
  ((Set.powersetCard.orderIsoOfFin s).toEquiv.sumCongr
      ((Set.powersetCard.orderIsoOfFin (complEquiv h s)).toEquiv.trans
        (complSubtypeEquiv h s))).trans
    (Equiv.sumCompl (p := fun i : Fin m => i ∈ s.val))

@[simp]
private theorem splitEquiv_inl (h : n ≤ m) (s : Set.powersetCard (Fin m) n) (i : Fin n) :
    splitEquiv h s (Sum.inl i) = s.val.orderEmbOfFin s.prop i := by
  simp [splitEquiv, complSubtypeEquiv, Set.powersetCard.orderIsoOfFin]
  rfl

@[simp]
private theorem splitEquiv_inr (h : n ≤ m) (s : Set.powersetCard (Fin m) n)
    (j : Fin (m - n)) :
    splitEquiv h s (Sum.inr j) =
      (complEquiv h s).val.orderEmbOfFin (complEquiv h s).prop j := by
  simp [splitEquiv, complSubtypeEquiv, Set.powersetCard.orderIsoOfFin]
  rfl

theorem sign_eq_one_of_two_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (h2 : (2 : R) = 0) (σ : Equiv.Perm α) : (Equiv.Perm.sign σ : R) = 1 := by
  have hneg : (-1 : R) = 1 := by
    have h : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; simp
  · rw [h]; simpa using hneg

theorem minor_inv_transpose_compl (h2 : (2 : R) = 0) (g : Matrix (Fin m) (Fin m) R)
    (hdet : g.det = 1) (hn : n ≤ m) (s t : Set.powersetCard (Fin m) n) :
    minor (g⁻¹)ᵀ (complEquiv hn s) (complEquiv hn t) = minor g s t := by
  classical
  have hg : IsUnit g.det := by rw [hdet]; exact isUnit_one
  let e_s := splitEquiv hn s
  let e_t := splitEquiv hn t
  let G : Matrix (Fin n ⊕ Fin (m - n)) (Fin n ⊕ Fin (m - n)) R := g.submatrix e_s e_t
  let h' : Matrix (Fin n ⊕ Fin (m - n)) (Fin n ⊕ Fin (m - n)) R :=
    (g⁻¹).submatrix e_t e_s
  have hG_h' : G * h' = 1 := by
    dsimp [G, h']
    rw [Matrix.submatrix_mul_equiv g (g⁻¹) e_s e_t e_s, Matrix.mul_nonsing_inv g hg]
    simp
  let A : Matrix (Fin n) (Fin n) R := G.toBlocks₁₁
  let B : Matrix (Fin n) (Fin (m - n)) R := G.toBlocks₁₂
  let C : Matrix (Fin (m - n)) (Fin n) R := G.toBlocks₂₁
  let D : Matrix (Fin (m - n)) (Fin (m - n)) R := G.toBlocks₂₂
  let P : Matrix (Fin n) (Fin n) R := h'.toBlocks₁₁
  let Q : Matrix (Fin n) (Fin (m - n)) R := h'.toBlocks₁₂
  let Rr : Matrix (Fin (m - n)) (Fin n) R := h'.toBlocks₂₁
  let H : Matrix (Fin (m - n)) (Fin (m - n)) R := h'.toBlocks₂₂
  have hG : Matrix.fromBlocks A B C D = G := Matrix.fromBlocks_toBlocks G
  have hh : Matrix.fromBlocks P Q Rr H = h' := Matrix.fromBlocks_toBlocks h'
  have hblocks :
      Matrix.fromBlocks (A * P + B * Rr) (A * Q + B * H)
        (C * P + D * Rr) (C * Q + D * H) =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0
        (1 : Matrix (Fin (m - n)) (Fin (m - n)) R) := by
    rw [← Matrix.fromBlocks_multiply, hG, hh, hG_h', Matrix.fromBlocks_one]
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hblocks
  have hGK : G * Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) Q 0 H =
      Matrix.fromBlocks A 0 C (1 : Matrix (Fin (m - n)) (Fin (m - n)) R) := by
    rw [← hG, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, h12, h22]
  have hdetGK : G.det * H.det = A.det := by
    have h := congrArg Matrix.det hGK
    rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_one, Matrix.det_one, one_mul, mul_one] at h
    exact h
  have hGdet : G.det = g.det := by
    have hGG : G = g.reindex e_s.symm e_t.symm := by
      ext i j
      simp [G, Matrix.reindex_apply]
    rw [hGG, Matrix.det_reindex, sign_eq_one_of_two_eq_zero h2, one_mul]
  have hA : A.det = minor g s t := by
    dsimp [A, G, minor]
    congr 1
  have hH : H.det = minor (g⁻¹) (complEquiv hn t) (complEquiv hn s) := by
    dsimp [H, h', minor]
    congr 1
  have hmain : g.det * minor (g⁻¹) (complEquiv hn t) (complEquiv hn s) = minor g s t := by
    rw [← hGdet, ← hH, hdetGK, hA]
  rw [hdet, one_mul] at hmain
  rwa [minor_transpose]

theorem permMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (σ : Equiv.Perm (Fin m)) :
    (σ.permMatrix R).map φ = σ.permMatrix S := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem minor_permMatrix_conj (h2 : (2 : R) = 0) (σ : Equiv.Perm (Fin m))
    (M : Matrix (Fin m) (Fin m) R) (s t : Set.powersetCard (Fin m) n) :
    minor (σ.permMatrix R * M * (σ.permMatrix R)ᵀ) s t =
      minor M (permImage σ s) (permImage σ t) := by
  classical
  have hP : ∀ (r u : Set.powersetCard (Fin m) n),
      minor (σ.permMatrix R) r u = if u = permImage σ r then 1 else 0 := by
    intro r u
    rw [minor_permMatrix h2 σ r u]
    by_cases h : ((r : Finset (Fin m))).map σ.toEmbedding = (u : Finset (Fin m))
    · have hu : u = permImage σ r := by
        apply Subtype.ext
        simpa only [coe_permImage, Finset.map_eq_image, Equiv.coe_toEmbedding] using h.symm
      rw [if_pos h, if_pos hu]
    · have hu : u ≠ permImage σ r := by
        intro hh
        exact h (by
          simp only [hh, coe_permImage, Finset.map_eq_image, Equiv.coe_toEmbedding])
      rw [if_neg h, if_neg hu]
  have hPt : ∀ v : Set.powersetCard (Fin m) n,
      minor (σ.permMatrix R)ᵀ v t = if v = permImage σ t then 1 else 0 := by
    intro v
    rw [minor_transpose]
    exact hP t v
  calc
    minor (σ.permMatrix R * M * (σ.permMatrix R)ᵀ) s t
        = ∑ u, minor (σ.permMatrix R) s u *
            minor (M * (σ.permMatrix R)ᵀ) u t := by
          rw [Matrix.mul_assoc, minor_mul]
    _ = ∑ u, (if u = permImage σ s then 1 else 0) *
          (∑ v, minor M u v * minor (σ.permMatrix R)ᵀ v t) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hP s u, minor_mul]
    _ = ∑ u, (if u = permImage σ s then 1 else 0) *
          (∑ v, minor M u v * (if v = permImage σ t then 1 else 0)) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          congr 1
          exact Finset.sum_congr rfl fun v _ => by rw [hPt v]
    _ = minor M (permImage σ s) (permImage σ t) := by
          simp [Finset.sum_ite_eq', mul_comm]

@[expose] noncomputable def revMap (h : n ≤ m) :
    (Set.powersetCard (Fin m) n → R) ≃ₗ[R]
      (Set.powersetCard (Fin m) (m - n) → R) where
  toFun x := fun s => x (((complEquiv h).trans revEquiv).symm s)
  invFun x := fun s => x (((complEquiv h).trans revEquiv) s)
  left_inv x := by
    ext s
    simp
  right_inv x := by
    ext s
    simp
  map_add' x y := by
    ext s
    simp
  map_smul' c x := by
    ext s
    simp

theorem revMap_apply (h : n ≤ m) (x : Set.powersetCard (Fin m) n → R)
    (s : Set.powersetCard (Fin m) n) :
    revMap (R := R) h x (revEquiv (complEquiv h s)) = x s := by
  change x ((complEquiv h).symm
    (revEquiv.symm (revEquiv (complEquiv h s)))) = x s
  simp [revEquiv_symm]

theorem linearFlag_permMatrix_eq {F : Type} [Field F] (π : Equiv.Perm (Fin m)) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.permMatrix m F π =
      Equiv.Perm.permMatrix (R := F) (σ := π.symm) := by
  simpa only [Equiv.Perm.inv_def] using
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.permMatrix_eq (n := m) (K := F) π)

theorem revMap_minor {F : Type} [Field F] (h2 : (2 : F) = 0)
    (g : SpecialLinearGroup (Fin m) F) (φ : F →+* R) (hn : n ≤ m)
    (x : Set.powersetCard (Fin m) n → R) :
    revMap hn (minor (g.map φ) *ᵥ x) =
      minor ((borelGraph m F g : Matrix (Fin m) (Fin m) F).map φ) *ᵥ revMap hn x := by
  classical
  let gmat : Matrix (Fin m) (Fin m) F := g
  let P : Matrix (Fin m) (Fin m) R := (Fin.revPerm : Equiv.Perm (Fin m)).permMatrix R
  let N : Matrix (Fin m) (Fin m) R := ((gmat⁻¹).map φ)ᵀ
  let B : Matrix (Fin m) (Fin m) R :=
    (borelGraph m F g : Matrix (Fin m) (Fin m) F).map φ
  let F' : Set.powersetCard (Fin m) n ≃ Set.powersetCard (Fin m) (m - n) :=
    (complEquiv hn).trans revEquiv
  have h2R : (2 : R) = 0 := by
    rw [show (2 : R) = φ (2 : F) from (map_natCast φ 2).symm, h2, map_zero]
  have hgdet : gmat.det = 1 := by
    change (g : Matrix (Fin m) (Fin m) F).det = 1
    exact g.2
  have hmatmul : gmat * (((g⁻¹ : SpecialLinearGroup (Fin m) F) :
      Matrix (Fin m) (Fin m) F)) = 1 := by
    change (((g * g⁻¹ : SpecialLinearGroup (Fin m) F) :
      Matrix (Fin m) (Fin m) F)) = 1
    rw [mul_inv_cancel]
    rfl
  have hginv : gmat⁻¹ = ((g⁻¹ : SpecialLinearGroup (Fin m) F) :
      Matrix (Fin m) (Fin m) F) :=
    Matrix.inv_eq_right_inv hmatmul
  have hPP : (Fin.revPerm : Equiv.Perm (Fin m)).permMatrix F *
      (Fin.revPerm : Equiv.Perm (Fin m)).permMatrix F = 1 := by
    rw [← Matrix.permMatrix_mul,
      show (Fin.revPerm : Equiv.Perm (Fin m)) * Fin.revPerm = 1 by ext i; simp,
      Matrix.permMatrix_one]
  have hPinv : (((revGL m F)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (Fin.revPerm : Equiv.Perm (Fin m)).permMatrix F := by
    rw [Matrix.GeneralLinearGroup.coe_inv, coe_revGL, linearFlag_permMatrix_eq,
      Fin.revPerm_symm]
    exact Matrix.inv_eq_right_inv hPP
  have hPmap : ((Fin.revPerm : Equiv.Perm (Fin m)).permMatrix F).map φ = P :=
    permMatrix_map (R := F) φ Fin.revPerm
  have hPsym : Pᵀ = P := by
    dsimp [P]
    rw [Matrix.transpose_permMatrix, Equiv.Perm.inv_def, Fin.revPerm_symm]
  have hB : B = P * N * Pᵀ := by
    dsimp [B, N, P]
    rw [coe_borelGraph, hPinv, linearFlag_permMatrix_eq, Fin.revPerm_symm]
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
    rw [← hginv]
    simp only [hPmap]
    rw [hPsym]
  have hminor : ∀ s t : Set.powersetCard (Fin m) n,
      minor B (F' s) (F' t) = minor (g.map φ) s t := by
    intro s t
    have hFs : F' s = permImage (Fin.revPerm : Equiv.Perm (Fin m)) (complEquiv hn s) := rfl
    have hFt : F' t = permImage (Fin.revPerm : Equiv.Perm (Fin m)) (complEquiv hn t) := rfl
    calc
      minor B (F' s) (F' t)
          = minor N
              (permImage (Fin.revPerm : Equiv.Perm (Fin m)) (F' s))
              (permImage (Fin.revPerm : Equiv.Perm (Fin m)) (F' t)) := by
            rw [hB]
            exact minor_permMatrix_conj h2R (Fin.revPerm : Equiv.Perm (Fin m)) N
              (F' s) (F' t)
      _ = minor N (complEquiv hn s) (complEquiv hn t) := by
            rw [hFs, hFt]
            simp only [permImage_permImage, permImage_revPerm_mul_self]
      _ = φ (minor gmat s t) := by
            dsimp [N]
            rw [minor_transpose, minor_map, ← minor_transpose,
              minor_inv_transpose_compl h2 gmat hgdet hn s t]
      _ = minor (gmat.map φ) s t := (minor_map φ gmat s t).symm
      _ = minor (g.map φ) s t := rfl
  ext u
  let s := F'.symm u
  have hu : F' s = u := by simp [s]
  have hFs : F' s = revEquiv (complEquiv hn s) := rfl
  rw [← hu]
  change revMap hn (minor (g.map φ) *ᵥ x) (revEquiv (complEquiv hn s)) =
    (minor B *ᵥ revMap hn x) (F' s)
  rw [revMap_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp F']
  refine Finset.sum_congr rfl fun t _ => ?_
  have hFt : F' t = revEquiv (complEquiv hn t) := rfl
  have hrev : revMap hn x (F' t) = x t := by
    rw [hFt, revMap_apply]
  rw [hrev, hminor s t]

end CFSG.LieType.SpecialLinear.ExteriorModel
