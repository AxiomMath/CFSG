module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3UAlg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LAlg
public import CFSG.LinearAlgebra.LinearGroups.UnitaryTransitivity

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3L Polynomial

variable {K : Type} [Field K]

theorem finrank_ker_comp_le {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ ψ : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker (φ ∘ₗ ψ)) ≤
      Module.finrank K (LinearMap.ker φ) + Module.finrank K (LinearMap.ker ψ) := by
  set g : LinearMap.ker (φ ∘ₗ ψ) →ₗ[K] LinearMap.ker φ :=
    (ψ.domRestrict (LinearMap.ker (φ ∘ₗ ψ))).codRestrict (LinearMap.ker φ)
      (fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
        exact hx) with hg
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have h1 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K (LinearMap.ker φ) :=
    Submodule.finrank_le _
  have h2 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K (LinearMap.ker ψ) := by
    let e : LinearMap.ker g →ₗ[K] LinearMap.ker ψ :=
      { toFun := fun x => ⟨((x : LinearMap.ker (φ ∘ₗ ψ)) : V), by
          rw [LinearMap.mem_ker]
          exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2)⟩
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := e) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h4 := congrArg (fun z : LinearMap.ker ψ => (z : V)) hxy
    exact h4
  omega

variable {n : ℕ}

theorem aeval_quad_mulVec (A : Matrix (Fin n) (Fin n) K) (a : Fin 3 → K) (v : Fin n → K) :
    Polynomial.aeval A (C (a 0) + C (a 1) * X + C (a 2) * X ^ 2) *ᵥ v =
      ∑ j : Fin 3, a j • ((A ^ (j : ℕ)) *ᵥ v) := by
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
    Algebra.algebraMap_eq_smul_one, Matrix.add_mulVec, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Fin.sum_univ_three, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one]

theorem linearIndependent_orbit {A : Matrix (Fin n) (Fin n) K} {c : K}
    (hA : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) K)) (hroot : ∀ μ : K, μ ^ 3 ≠ c)
    {v : Fin n → K} (hv : v ≠ 0) :
    LinearIndependent K (fun j : Fin 3 => (A ^ (j : ℕ)) *ᵥ v) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  set g : K[X] := C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 with hgdef
  set q : K[X] := X ^ 3 - C c with hqdef
  have hqm : q.Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  have hqd : q.natDegree = 3 := Polynomial.natDegree_X_pow_sub_C
  have hirr : Irreducible q := by
    rw [hqm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun μ hμ => ?_
    rw [Polynomial.mem_roots hqm.ne_zero, Polynomial.IsRoot.def, hqdef, eval_sub, eval_pow,
      eval_X, eval_C, sub_eq_zero] at hμ
    exact hroot μ hμ
  have hg0 : g ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := hne
    have hc0 : g.coeff 0 = a 0 := by simp [hgdef]
    have hc1 : g.coeff 1 = a 1 := by simp [hgdef]
    have hc2 : g.coeff 2 = a 2 := by simp [hgdef]
    rw [h0, coeff_zero] at hc0 hc1 hc2
    fin_cases j
    · exact hj hc0.symm
    · exact hj hc1.symm
    · exact hj hc2.symm
  have hgdeg : g.natDegree ≤ 2 := by
    rw [hgdef]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · rw [natDegree_C]; omega
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_C, natDegree_X]
      omega
    · exact (natDegree_C_mul_X_pow_le _ _).trans le_rfl
  have hcop : IsCoprime q g := by
    rw [Irreducible.coprime_iff_not_dvd hirr]
    intro hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd hg0
    omega
  obtain ⟨s, t, hst⟩ := hcop
  have hgv : Polynomial.aeval A g *ᵥ v = 0 := by
    rw [hgdef, aeval_quad_mulVec]
    exact ha
  have hqA : Polynomial.aeval A q = 0 := by
    rw [hqdef, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hA,
      Algebra.algebraMap_eq_smul_one, sub_self]
  have hone := congrArg (fun r : K[X] => Polynomial.aeval A r *ᵥ v) hst
  simp only [map_add, map_mul, hqA, mul_zero, zero_add, map_one, Matrix.one_mulVec] at hone
  rw [← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_zero] at hone
  exact hv hone.symm

theorem exists_cube_root_of_four {A : Matrix (Fin 4) (Fin 4) K} {c : K}
    (hA : A ^ 3 = c • (1 : Matrix (Fin 4) (Fin 4) K)) : ∃ μ : K, μ ^ 3 = c := by
  by_contra hroot
  push Not at hroot
  have hdim : ∀ v : Fin 4 → K, v ≠ 0 → Module.finrank K (orbitSpan A v) = 3 := fun v hv => by
    rw [orbitSpan, finrank_span_eq_card (linearIndependent_orbit hA hroot hv), Fintype.card_fin]
  set e : Fin 4 → K := Pi.single 0 1 with he
  have he0 : e ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [he] at this
  set W := orbitSpan A e with hW
  have hWt : W ≠ ⊤ := by
    intro h
    have h1 := hdim e he0
    rw [← hW, h, finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨v', hv'⟩ : ∃ v', v' ∉ W := by
    by_contra hall
    push Not at hall
    exact hWt (eq_top_iff.mpr fun x _ => hall x)
  have hv'0 : v' ≠ 0 := by
    rintro rfl
    exact hv' W.zero_mem
  set W' := orbitSpan A v' with hW'
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W W'
  have hsup : Module.finrank K ↥(W ⊔ W') ≤ 4 := by
    have := Submodule.finrank_le (W ⊔ W')
    rwa [Module.finrank_fin_fun] at this
  rw [hdim e he0, hdim v' hv'0] at hsum
  have hinf : W ⊓ W' ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have hinv : ∀ (U : Submodule K (Fin 4 → K)), (∀ y ∈ U, A *ᵥ y ∈ U) →
      ∀ y ∈ U, orbitSpan A y ≤ U := by
    intro U hU y hy
    rw [orbitSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · simpa using hy
    · simpa using hU y hy
    · change (A ^ 2) *ᵥ y ∈ U
      rw [pow_two, ← Matrix.mulVec_mulVec]
      exact hU _ (hU y hy)
  have hxW : orbitSpan A x ≤ W ⊓ W' := by
    refine hinv _ (fun y hy => ?_) x hx
    exact ⟨mulVec_mem_orbitSpan hA e hy.1, mulVec_mem_orbitSpan hA v' hy.2⟩
  have h3 : Module.finrank K ↥(W ⊓ W') = 3 := by
    have h4 := Submodule.finrank_mono hxW
    have h5 := Submodule.finrank_mono (inf_le_left : W ⊓ W' ≤ W)
    rw [hdim x hx0] at h4
    rw [hdim e he0] at h5
    omega
  have hWW : W ⊓ W' = W := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h3, hdim e he0])
  have hle : W ≤ W' := hWW ▸ inf_le_right
  have hWW' : W = W' := Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim e he0, hdim v' hv'0])
  apply hv'
  rw [hWW']
  simpa using mem_orbitSpan_pow A v' 0

variable {p f : ℕ}

theorem exists_cube_root_unity (h : UnitaryFieldData p f K) (hp3 : p ≠ 3) :
    ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h3 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).mp h3).symm
    omega
  have hp2 : p ^ 2 % 3 = 1 := by
    rcases hp' with h1 | h1 <;> (rw [Nat.pow_mod, h1]; try decide)
  have hmod : p ^ (2 * f) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod, hp2, one_pow]
    try decide
  have hcard : 3 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcard
  refine ⟨u, fun h1 => ?_, ?_⟩
  · have hu1 : u = 1 := Units.val_eq_one.mp h1
    rw [hu1, orderOf_one] at hu
    omega
  · have h3 := pow_orderOf_eq_one u
    rw [hu] at h3
    have h4 := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h4

theorem cube_factor {A : Matrix (Fin n) (Fin n) K} {c μ ω : K} (hμ : μ ^ 3 = c) (hω1 : ω ≠ 1)
    (hω : ω ^ 3 = 1) (hA : A ^ 3 = c • (1 : Matrix (Fin n) (Fin n) K)) :
    (A - μ • 1) * (A - (μ * ω) • 1) * (A - (μ * ω ^ 2) • 1) = 0 := by
  have e1 : 1 + ω + ω ^ 2 = 0 := by
    have h2 : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hω1)
  have key : (X - C μ) * (X - C (μ * ω)) * (X - C (μ * ω ^ 2)) = (X ^ 3 - C c : K[X]) := by
    have e2 : (X - C μ) * (X - C (μ * ω)) * (X - C (μ * ω ^ 2)) =
        X ^ 3 - C (μ * (1 + ω + ω ^ 2)) * X ^ 2 + C (μ ^ 2 * ω * (1 + ω + ω ^ 2)) * X -
          C (μ ^ 3 * ω ^ 3) := by
      simp only [map_mul, map_add, map_pow, map_one]
      ring
    rw [e2, e1, hμ, hω]
    simp
  have h1 := congrArg (Polynomial.aeval A) key
  simp only [Polynomial.aeval_mul, Polynomial.aeval_sub, Polynomial.aeval_X_pow,
    Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at h1
  rw [h1, hA, sub_self]

theorem exists_eigen_two (h : UnitaryFieldData p f K) (hp3 : p ≠ 3)
    {A : Matrix (Fin 4) (Fin 4) K} {c : K} (hA : A ^ 3 = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ ν : K, ν ^ 3 = c ∧ 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' (A - ν • 1))) := by
  obtain ⟨μ, hμ⟩ := exists_cube_root_of_four hA
  obtain ⟨ω, hω1, hω⟩ := exists_cube_root_unity h hp3
  have hprod := cube_factor hμ hω1 hω hA
  have hker : LinearMap.ker (Matrix.toLin' (A - μ • 1) ∘ₗ
      (Matrix.toLin' (A - (μ * ω) • 1) ∘ₗ Matrix.toLin' (A - (μ * ω ^ 2) • 1))) = ⊤ := by
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Matrix.mul_assoc, hprod, map_zero,
      LinearMap.ker_zero]
  have h4 := finrank_ker_comp_le (Matrix.toLin' (A - μ • 1))
    (Matrix.toLin' (A - (μ * ω) • 1) ∘ₗ Matrix.toLin' (A - (μ * ω ^ 2) • 1))
  have h5 := finrank_ker_comp_le (Matrix.toLin' (A - (μ * ω) • 1))
    (Matrix.toLin' (A - (μ * ω ^ 2) • 1))
  rw [hker, finrank_top, Module.finrank_fin_fun] at h4
  by_cases h1 : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' (A - μ • 1)))
  · exact ⟨μ, hμ, h1⟩
  by_cases h2 : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' (A - (μ * ω) • 1)))
  · exact ⟨μ * ω, by rw [mul_pow, hμ, hω, mul_one], h2⟩
  refine ⟨μ * ω ^ 2, ?_, by omega⟩
  rw [mul_pow, hμ, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow, mul_one]

theorem exists_isotropic_of_two_le (h : UnitaryFieldData p f K) {E : Submodule K (Fin n → K)}
    (hE : 2 ≤ Module.finrank K E) : ∃ w ∈ E, w ≠ 0 ∧ stdHermForm h n w w = 0 := by
  have := h.finite
  set b := Module.finBasis K E with hb
  set i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  set i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  set v : Fin 2 → (Fin n → K) := ![(b i0 : Fin n → K), (b i1 : Fin n → K)] with hv
  have hli : LinearIndependent K v := by
    have hinj : Function.Injective ![i0, i1] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [i0, i1, Fin.ext_iff]
    have h1 := (b.linearIndependent.comp _ hinj).map' E.subtype (Submodule.ker_subtype E)
    convert h1 using 1
    funext j
    fin_cases j <;> rfl
  set S : Submodule K (Fin n → K) := Submodule.span K (Set.range v) with hS
  have hSE : S ≤ E := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact (b i0).2
    · exact (b i1).2
  have hS2 : Module.finrank K S = 2 := by
    rw [hS, finrank_span_eq_card hli, Fintype.card_fin]
  set B : S →ₛₗ[h.bar] S →ₗ[K] K := ((stdHermForm h n).comp S.subtype).compl₂ S.subtype
    with hBdef
  have hBsymm : B.IsSymm := ⟨fun x y => (stdHermForm_isSymm h n).eq x y⟩
  by_cases hsep : B.SeparatingLeft
  · obtain ⟨a, ha0, ha⟩ := exists_isotropic_of_finrank_two h hBsymm hsep hS2
    exact ⟨a, hSE a.2, fun h0 => ha0 (Subtype.ext h0), ha⟩
  · simp only [LinearMap.SeparatingLeft, not_forall] at hsep
    obtain ⟨x, hx, hx0⟩ := hsep
    exact ⟨x, hSE x.2, fun h0 => hx0 (Subtype.ext h0), hx x⟩

theorem exists_isotropic_invariant_four (h : UnitaryFieldData p f K) (hp3 : p ≠ 3)
    {A : GL (Fin 4) K} (hA : A ∈ uU h 4) {c : K} (hc : c ≠ 0)
    (hA3 : (A : Matrix (Fin 4) (Fin 4) K) ^ 3 = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ W : Submodule K (Fin 4 → K), (∃ w ∈ W, w ≠ 0) ∧
      (∀ x ∈ W, ∀ y ∈ W, stdHermForm h 4 x y = 0) ∧
      (∀ x ∈ W, (A : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ W) ∧
      (∀ x ∈ W, ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x ∈ W) := by
  obtain ⟨ν, hν, hE⟩ := exists_eigen_two h hp3 hA3
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hν
    exact hc hν.symm
  set E := LinearMap.ker (Matrix.toLin' ((A : Matrix (Fin 4) (Fin 4) K) - ν • 1)) with hEdef
  have hmemE : ∀ x, x ∈ E ↔ (A : Matrix (Fin 4) (Fin 4) K) *ᵥ x = ν • x := by
    intro x
    rw [hEdef, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
  have hAinv : ∀ x, (A : Matrix (Fin 4) (Fin 4) K) *ᵥ x = ν • x →
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x = ν⁻¹ • x := by
    intro x hx
    have h1 : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hx, Matrix.mulVec_smul] at h1
    calc ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x =
        ν⁻¹ • (ν • (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x)) := by
          rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
      _ = ν⁻¹ • x := by rw [h1]
  by_cases hN : ν * h.bar ν = 1
  · obtain ⟨w, hwE, hw0, hww⟩ := exists_isotropic_of_two_le h hE
    have hAw := (hmemE w).1 hwE
    refine ⟨Submodule.span K {w}, ⟨w, Submodule.mem_span_singleton_self w, hw0⟩, ?_, ?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [stdHermForm_smul_left, stdHermForm_smul_right, hww, mul_zero, mul_zero]
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [Matrix.mulVec_smul, hAw, smul_smul]
      exact Submodule.mem_span_singleton.mpr ⟨a * ν, rfl⟩
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [Matrix.mulVec_smul, hAinv w hAw, smul_smul]
      exact Submodule.mem_span_singleton.mpr ⟨a * ν⁻¹, rfl⟩
  · have hE0 : E ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hE
      omega
    obtain ⟨w, hwE, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
    refine ⟨E, ⟨w, hwE, hw0⟩, ?_, ?_, ?_⟩
    · intro x hx y hy
      have h1 := stdHermForm_uU h hA x y
      rw [(hmemE x).1 hx, (hmemE y).1 hy, stdHermForm_smul_left, stdHermForm_smul_right] at h1
      have h2 : (1 - ν * h.bar ν) * stdHermForm h 4 x y = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hN))
    · intro x hx
      rw [hmemE, (hmemE x).1 hx, Matrix.mulVec_smul, (hmemE x).1 hx]
    · intro x hx
      rw [hmemE, hAinv x ((hmemE x).1 hx), Matrix.mulVec_smul, (hmemE x).1 hx, smul_comm]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U
