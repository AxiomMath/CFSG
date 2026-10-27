module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianBasic

public section

namespace CFSG.ComponentClassification.CatalogueBHermitian

noncomputable section

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

theorem complement_finrank [FiniteDimensional K V] {e : V} (he : h e e = 1) :
    Module.finrank K (LinearMap.ker (h e)) + 1 = Module.finrank K V := by
  have hsurj : Function.Surjective (h e) := by
    intro c
    refine ⟨c • e, ?_⟩
    rw [map_smul, smul_eq_mul, he, mul_one]
  have hd := LinearMap.finrank_range_add_finrank_ker (h e)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self] at hd
  omega

theorem exists_orthonormal_basis [Finite K] [FiniteDimensional K V]
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  classical
  suffices ∀ d, Module.finrank K V = d →
      ∃ b : Module.Basis (Fin d) K V,
        ∀ i j, h (b i) (b j) = if i = j then 1 else 0 by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero =>
      refine ⟨basisOfFinrankZero hd, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ d ih =>
      let : Nontrivial V := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank K V)
      obtain ⟨e, he⟩ := exists_unit_vector h hsym hnd hsigma hne
      let W := LinearMap.ker (h e)
      let hW := h.domRestrict₁₂ W W
      have hdim : Module.finrank K W = d := by
        have hc := complement_finrank h he
        change Module.finrank K W + 1 = Module.finrank K V at hc
        omega
      obtain ⟨bW, hbW⟩ := ih hW (complement_isSymm h hsym e)
        (complement_nondegenerate h hsym hnd he) hdim
      change ∀ i j, h (bW i : V) (bW j : V) = if i = j then 1 else 0 at hbW
      have hli : ∀ (c : K), ∀ x ∈ W, c • e + x = 0 → c = 0 :=
        coefficient_zero h he
      have hsp : ∀ x : V, ∃ c : K, x + c • e ∈ W := by
        intro x
        refine ⟨-h e x, ?_⟩
        simpa only [orthogonalProjection_apply, neg_smul, sub_eq_add_neg] using
          orthogonalProjection_mem_ker h he x
      let b := Module.Basis.mkFinCons e bW hli hsp
      refine ⟨b, ?_⟩
      have hb : (b : Fin (d + 1) → V) = Fin.cons e (fun i => (bW i : V)) :=
        Module.Basis.coe_mkFinCons e bW hli hsp
      intro i j
      rw [hb]
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j
      · simpa using he
      · simp [eq_comm]
      · have hx : h (bW i : V) e = 0 := hsym.isRefl e (bW i) (bW i).property
        simpa using hx
      · simpa only [Fin.cons_succ, Fin.succ_inj] using hbW i j

end

end CFSG.ComponentClassification.CatalogueBHermitian
