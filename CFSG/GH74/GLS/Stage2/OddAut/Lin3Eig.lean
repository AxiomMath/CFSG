module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Polynomial Lagrange Matrix

section EigProj

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

theorem commute_aeval {x y : A} (h : Commute x y) (p : K[X]) : Commute (aeval x p) y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c y).mul_left (h.pow_left n)

variable [DecidableEq K]

noncomputable def eigProj (s : Finset K) (x : A) (ζ : K) : A :=
  aeval x (Lagrange.basis s id ζ)

theorem eigProj_commute {s : Finset K} {x y : A} (h : Commute x y) (ζ : K) :
    Commute (eigProj s x ζ) y := commute_aeval h _

theorem eigProj_eigen {s : Finset K} {x : A} (hx : aeval x (Lagrange.nodal s id) = 0) {ζ : K}
    (hζ : ζ ∈ s) : x * eigProj s x ζ = ζ • eigProj s x ζ := by
  have h1 : (X - C ζ) * Lagrange.basis s id ζ = C (nodalWeight s id ζ) * Lagrange.nodal s id := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hζ, ← Lagrange.nodal_erase_eq_nodal_div hζ,
      Lagrange.nodal_eq_mul_nodal_erase hζ]
    simp only [id]
    ring
  have h2 := congrArg (aeval x) h1
  simp only [map_mul, map_sub, aeval_X, aeval_C, hx, mul_zero] at h2
  have h3 : (x - algebraMap K A ζ) * eigProj s x ζ = 0 := h2
  rw [sub_mul, sub_eq_zero] at h3
  rw [h3, Algebra.smul_def]

theorem sum_eigProj {s : Finset K} (hs : s.Nonempty) (x : A) :
    ∑ ζ ∈ s, eigProj s x ζ = 1 := by
  unfold eigProj
  rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) hs, map_one]

omit [DecidableEq K] in
theorem aeval_nodal_of_pow_eq_one {r : ℕ} {ω : K} (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    {x : A} (hx : x ^ r = 1) :
    aeval x (Lagrange.nodal (nthRootsFinset r (1 : K)) id) = 0 := by
  have : Lagrange.nodal (nthRootsFinset r (1 : K)) id = X ^ r - 1 := by
    rw [Polynomial.X_pow_sub_one_eq_prod hr hω]
    rfl
  rw [this]
  simp [hx]

end EigProj

section Joint

variable {K : Type*} [Field K] {r : ℕ} {ω : K}

omit [Field K] in
theorem sum_coe_sort_sum {M : Type*} [AddCommMonoid M] (s : Finset K) (f : K → K → M) :
    ∑ ζ ∈ s, ∑ ξ ∈ s, f ζ ξ = ∑ ζ : ↥s, ∑ ξ : ↥s, f ζ ξ := by
  rw [← Finset.sum_coe_sort s (fun ζ => ∑ ξ ∈ s, f ζ ξ)]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [← Finset.sum_coe_sort s (fun ξ => f ζ ξ)]

theorem exists_joint_eigenbasis (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    (a b : Matrix (Fin 3) (Fin 3) K) (ha : a ^ r = 1) (hb : b ^ r = 1) (hab : a * b = b * a) :
    ∃ (B : Matrix (Fin 3) (Fin 3) K) (da db : Fin 3 → K), IsUnit B.det ∧
      a * B = B * Matrix.diagonal da ∧ b * B = B * Matrix.diagonal db := by
  classical
  set s : Finset K := nthRootsFinset r (1 : K) with hs
  have hsne : s.Nonempty := ⟨1, by rw [hs, mem_nthRootsFinset hr]; exact one_pow r⟩
  have hxa := aeval_nodal_of_pow_eq_one hr hω ha
  have hxb := aeval_nodal_of_pow_eq_one hr hω hb
  let P : K → K → Matrix (Fin 3) (Fin 3) K := fun ζ ξ => eigProj s a ζ * eigProj s b ξ
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
  let vec : (↥s × ↥s × Fin 3) → (Fin 3 → K) := fun i => (P i.1 i.2.1) *ᵥ Pi.single i.2.2 1
  have hspan : ⊤ ≤ Submodule.span K (Set.range vec) := by
    intro w _
    have hw : w = ∑ m, w m • (Pi.single m (1 : K) : Fin 3 → K) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
    have h1 : (Pi.single m (1 : K) : Fin 3 → K) =
        ∑ ζ : ↥s, ∑ ξ : ↥s, (P ζ ξ) *ᵥ Pi.single m 1 := by
      have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ (Pi.single m (1 : K) : Fin 3 → K))
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
  let bs : Module.Basis κ K (Fin 3 → K) := Module.Basis.mk hli htop
  have hcard : Fintype.card κ = 3 := by
    have := Module.finrank_eq_card_basis bs
    simpa using this.symm
  let e : κ ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let bs' : Module.Basis (Fin 3) K (Fin 3 → K) := bs.reindex e
  have hcol : ∀ j : Fin 3, ∃ ζ ξ : K, a *ᵥ (bs' j) = ζ • bs' j ∧ b *ᵥ (bs' j) = ξ • bs' j := by
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
  refine ⟨(Pi.basisFun K (Fin 3)).toMatrix bs', da, db, ?_, ?_, ?_⟩
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

section Line

variable {K : Type*} [Field K] {r : ℕ} {ω : K}

@[expose] def eigSp (x : Matrix (Fin 3) (Fin 3) K) (ζ : K) : Submodule K (Fin 3 → K) :=
  LinearMap.ker (Matrix.mulVecLin (x - ζ • (1 : Matrix (Fin 3) (Fin 3) K)))

theorem mem_eigSp {x : Matrix (Fin 3) (Fin 3) K} {ζ : K} {v : Fin 3 → K} :
    v ∈ eigSp x ζ ↔ x *ᵥ v = ζ • v := by
  simp only [eigSp, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem exists_line_eigenvector (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    (x : Matrix (Fin 3) (Fin 3) K) (hx : x ^ r = 1)
    (hns : ∀ c : K, x ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧
      ∀ y : Matrix (Fin 3) (Fin 3) K, x * y = y * x → ∃ κ : K, y *ᵥ v = κ • v := by
  classical
  set s : Finset K := nthRootsFinset r (1 : K) with hs
  have hsne : s.Nonempty := ⟨1, by rw [hs, mem_nthRootsFinset hr]; exact one_pow r⟩
  have hxa := aeval_nodal_of_pow_eq_one hr hω hx
  have hmem : ∀ ζ ∈ s, ∀ w, eigProj s x ζ *ᵥ w ∈ eigSp x ζ := by
    intro ζ hζ w
    rw [mem_eigSp, Matrix.mulVec_mulVec, eigProj_eigen hxa hζ, Matrix.smul_mulVec]
  have hsum : ∀ w : Fin 3 → K, w = ∑ ζ ∈ s, eigProj s x ζ *ᵥ w := by
    intro w
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M *ᵥ w) (sum_eigProj hsne x)
    simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at h
    exact h.symm
  have hpair : ∃ ζ₁ ∈ s, ∃ ζ₂ ∈ s, ζ₁ ≠ ζ₂ ∧ eigSp x ζ₁ ≠ ⊥ ∧ eigSp x ζ₂ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    by_cases hex : ∃ ζ₀ ∈ s, eigSp x ζ₀ ≠ ⊥
    · obtain ⟨ζ₀, hζ₀, hne⟩ := hex
      have hall : ∀ w, w ∈ eigSp x ζ₀ := by
        intro w
        rw [hsum w]
        refine Submodule.sum_mem _ fun ζ hζ => ?_
        by_cases hζe : ζ = ζ₀
        · rw [hζe]
          exact hmem ζ₀ hζ₀ w
        · have hb := hcon ζ₀ hζ₀ ζ hζ (Ne.symm hζe) hne
          have h2 := hmem ζ hζ w
          rw [hb, Submodule.mem_bot] at h2
          rw [h2]
          exact Submodule.zero_mem _
      apply hns ζ₀
      ext i j
      have h := mem_eigSp.mp (hall (Pi.single j 1))
      have h2 := congrFun h i
      simpa [Matrix.mulVec_single_one, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using h2
    · push Not at hex
      have h0 : ∀ w : Fin 3 → K, w = 0 := by
        intro w
        rw [hsum w]
        refine Finset.sum_eq_zero fun ζ hζ => ?_
        have h2 := hmem ζ hζ w
        rw [hex ζ hζ, Submodule.mem_bot] at h2
        exact h2
      have := congrFun (h0 (Pi.single 0 1)) 0
      simp at this
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hne, hb₁, hb₂⟩ := hpair
  have hdisj : Disjoint (eigSp x ζ₁) (eigSp x ζ₂) := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have e1 := mem_eigSp.mp h1
    have e2 := mem_eigSp.mp h2
    have : (ζ₁ - ζ₂) • v = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  rw [Module.finrank_fin_fun] at hle
  have h1 : 1 ≤ Module.finrank K (eigSp x ζ₁) := Submodule.one_le_finrank_iff.mpr hb₁
  have h2 : 1 ≤ Module.finrank K (eigSp x ζ₂) := Submodule.one_le_finrank_iff.mpr hb₂
  have key : ∃ ζ : K, Module.finrank K (eigSp x ζ) = 1 := by
    by_cases h : Module.finrank K (eigSp x ζ₁) = 1
    · exact ⟨ζ₁, h⟩
    · exact ⟨ζ₂, by omega⟩
  obtain ⟨ζ, hζ⟩ := key
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hζ
  refine ⟨(v : Fin 3 → K), fun h => hv0 (Subtype.ext h), fun y hy => ?_⟩
  have hyv : y *ᵥ (v : Fin 3 → K) ∈ eigSp x ζ := by
    rw [mem_eigSp, Matrix.mulVec_mulVec, hy, ← Matrix.mulVec_mulVec, mem_eigSp.mp v.2,
      Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := hv ⟨_, hyv⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

end Line

end CFSG.GH74.GLS.Stage2.OddAut
