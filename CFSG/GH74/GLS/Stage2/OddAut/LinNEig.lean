module

public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Eig

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Polynomial Lagrange Matrix

section Joint

variable {K : Type*} [Field K] {r n : ℕ} {ω : K}

theorem exists_joint_eigenbasis_n (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    (a b : Matrix (Fin n) (Fin n) K) (ha : a ^ r = 1) (hb : b ^ r = 1) (hab : a * b = b * a) :
    ∃ (B : Matrix (Fin n) (Fin n) K) (da db : Fin n → K), IsUnit B.det ∧
      a * B = B * Matrix.diagonal da ∧ b * B = B * Matrix.diagonal db := by
  classical
  set s : Finset K := nthRootsFinset r (1 : K) with hs
  have hsne : s.Nonempty := ⟨1, by rw [hs, mem_nthRootsFinset hr]; exact one_pow r⟩
  have hxa := aeval_nodal_of_pow_eq_one hr hω ha
  have hxb := aeval_nodal_of_pow_eq_one hr hω hb
  let P : K → K → Matrix (Fin n) (Fin n) K := fun ζ ξ => eigProj s a ζ * eigProj s b ξ
  have hP1 : ∑ ζ ∈ s, ∑ ξ ∈ s, P ζ ξ = 1 := by
    simp only [P, ← Finset.mul_sum, ← Finset.sum_mul, sum_eigProj hsne, one_mul]
  have hPa : ∀ ζ ∈ s, ∀ ξ, a * P ζ ξ = ζ • P ζ ξ := by
    intro ζ hζ ξ
    simp only [P]
    rw [← Matrix.mul_assoc, eigProj_eigen hxa hζ, Matrix.smul_mul]
  have hPb : ∀ ζ, ∀ ξ ∈ s, b * P ζ ξ = ξ • P ζ ξ := by
    intro ζ ξ hξ
    simp only [P]
    have hc : eigProj s a ζ * b = b * eigProj s a ζ := (eigProj_commute hab ζ).eq
    rw [← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, eigProj_eigen hxb hξ, Matrix.mul_smul]
  let vec : (↥s × ↥s × Fin n) → (Fin n → K) := fun i => (P i.1 i.2.1) *ᵥ Pi.single i.2.2 1
  have hspan : ⊤ ≤ Submodule.span K (Set.range vec) := by
    intro w _
    have hw : w = ∑ m, w m • (Pi.single m (1 : K) : Fin n → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
    have h1 : (Pi.single m (1 : K) : Fin n → K) =
        ∑ ζ : ↥s, ∑ ξ : ↥s, (P ζ ξ) *ᵥ Pi.single m 1 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ (Pi.single m (1 : K) : Fin n → K))
        hP1
      simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at h
      exact h.symm.trans (sum_coe_sort_sum s _)
    rw [h1]
    exact Submodule.sum_mem _ fun ζ _ => Submodule.sum_mem _ fun ξ _ =>
      Submodule.subset_span ⟨(ζ, ξ, m), rfl⟩
  obtain ⟨κ, f, hfinj, hspan', hli⟩ := exists_linearIndependent' K vec
  have hfin : Finite κ := Finite.of_injective f hfinj
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range (vec ∘ f)) := by rw [hspan']; exact hspan
  let bs : Module.Basis κ K (Fin n → K) := Module.Basis.mk hli htop
  have hcard : Fintype.card κ = n := by
    have := Module.finrank_eq_card_basis bs
    simpa using this.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bs' : Module.Basis (Fin n) K (Fin n → K) := bs.reindex e
  have hcol : ∀ j : Fin n, ∃ ζ ξ : K, a *ᵥ (bs' j) = ζ • bs' j ∧ b *ᵥ (bs' j) = ξ • bs' j := by
    intro j
    have hj : bs' j = vec (f (e.symm j)) := by
      simp only [bs', Module.Basis.reindex_apply, bs, Module.Basis.mk_apply, Function.comp]
    generalize f (e.symm j) = i' at hj
    obtain ⟨⟨ζ, hζ⟩, ⟨ξ, hξ⟩, m⟩ := i'
    refine ⟨ζ, ξ, ?_, ?_⟩
    · rw [hj]
      simp only [vec]
      rw [Matrix.mulVec_mulVec, hPa ζ hζ ξ, Matrix.smul_mulVec]
    · rw [hj]
      simp only [vec]
      rw [Matrix.mulVec_mulVec, hPb ζ ξ hξ, Matrix.smul_mulVec]
  choose da db hda hdb using hcol
  refine ⟨(Pi.basisFun K (Fin n)).toMatrix bs', da, db, ?_, ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact Module.Basis.isUnit_det _ _
  · ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (hda j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.mul_apply]
    rw [h]
    ring
  · ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (hdb j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.mul_apply]
    rw [h]
    ring

end Joint

end CFSG.GH74.GLS.Stage2.OddAut
