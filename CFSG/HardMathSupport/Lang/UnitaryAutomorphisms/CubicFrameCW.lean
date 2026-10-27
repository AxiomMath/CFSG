module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.Transvection
public import Mathlib.FieldTheory.ChevalleyWarning

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

section Quad

variable {F M N G σ ι : Type*} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N]
  [Module F N] [AddCommGroup G] [Module F G] [Fintype σ] [DecidableEq σ]

theorem exists_quad_poly (Φ : M →ₗ[F] N →ₗ[F] G) (ℓ : G →ₗ[F] F) (u : (σ → F) →ₗ[F] M)
    (w : (σ → F) →ₗ[F] N) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x P = ℓ (Φ (u x) (w x)) := by
  refine ⟨∑ s, ∑ t, MvPolynomial.C (ℓ (Φ (u (Pi.single s 1)) (w (Pi.single t 1)))) *
      MvPolynomial.X s * MvPolynomial.X t, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 : (MvPolynomial.C (ℓ (Φ (u (Pi.single s 1)) (w (Pi.single t 1)))) *
        MvPolynomial.X s : MvPolynomial σ F).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    have h2 : (MvPolynomial.X t : MvPolynomial σ F).totalDegree ≤ 1 := by simp
    omega
  · intro x
    have hx : x = ∑ s, x s • (Pi.single s (1 : F) : σ → F) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

theorem exists_quad_poly_sum [Fintype ι] (Φ : M →ₗ[F] N →ₗ[F] G) (ℓ : G →ₗ[F] F)
    (u : ι → (σ → F) →ₗ[F] M) (w : ι → (σ → F) →ₗ[F] N) :
    ∃ P : MvPolynomial σ F, P.totalDegree ≤ 2 ∧
      ∀ x, MvPolynomial.eval x P = ℓ (∑ i, Φ (u i x) (w i x)) := by
  classical
  choose P hP1 hP2 using fun i => exists_quad_poly Φ ℓ (u i) (w i)
  refine ⟨∑ i, P i, (MvPolynomial.totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun i _ => hP1 i), fun x => ?_⟩
  simp [map_sum, hP2]

end Quad

theorem exists_isotropic_vec (hn : 4 ≤ n) (B : Matrix (Fin n) (Fin n) K) :
    ∃ v : Fin n → K, v ≠ 0 ∧ hpair h v v = 0 ∧ hpair h v (B *ᵥ v) = 0 := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have : Fintype h.fixedField := Fintype.ofFinite _
  have : Module.Finite h.fixedField K := Module.Finite.of_finite
  have hfix : ∀ a : h.fixedField, h.bar (algebraMap h.fixedField K a) = algebraMap h.fixedField K a :=
    fun a => a.2
  have hbs : ∀ (a : h.fixedField) (c : K), h.bar (a • c) = a • h.bar c := by
    intro a c; rw [Algebra.smul_def, Algebra.smul_def, map_mul, hfix]
  let Φ : K →ₗ[h.fixedField] K →ₗ[h.fixedField] K := LinearMap.mk₂ h.fixedField
    (fun c d => h.bar c * d)
    (fun c c' d => by simp [add_mul]) (fun a c d => by simp [hbs])
    (fun c d d' => by simp [mul_add]) (fun a c d => by simp)
  have hd : 2 ≤ Module.finrank h.fixedField K := by
    by_contra hlt
    have hle : Module.finrank h.fixedField K ≤ 1 := by omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hle
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    obtain ⟨a, ha⟩ := hv 1
    obtain ⟨a', ha'⟩ := hv c
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hvv : v = algebraMap h.fixedField K a⁻¹ := by
      have : v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [this, ha, Algebra.smul_def, mul_one]
    have hcc : c = algebraMap h.fixedField K (a' * a⁻¹) := by
      rw [← ha', Algebra.smul_def, hvv, map_mul]
    apply hc
    rw [hcc]
    exact hfix _
  set d := Module.finrank h.fixedField K with hd_def
  let b : Module.Basis (Fin d) h.fixedField K := Module.finBasis h.fixedField K
  let T : (Fin n × Fin d → h.fixedField) →ₗ[h.fixedField] (Fin n → K) :=
    LinearMap.pi fun i => (b.equivFun.symm : (Fin d → h.fixedField) →ₗ[h.fixedField] K) ∘ₗ
      (LinearMap.funLeft h.fixedField h.fixedField (fun k : Fin d => (i, k)))
  have hT : ∀ x i, T x i = b.equivFun.symm (fun k => x (i, k)) := fun x i => rfl
  have hTinj : ∀ x, T x = 0 → x = 0 := by
    intro x hx
    refine funext fun ik => ?_
    obtain ⟨i, k⟩ := ik
    have h1 := congrFun hx i
    rw [hT] at h1
    have h2 : (fun k => x (i, k)) = 0 := (LinearEquiv.map_eq_zero_iff _).mp h1
    exact congrFun h2 k
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_leftInverse_of_injective
    (Algebra.linearMap h.fixedField K)
    (LinearMap.ker_eq_bot.mpr (algebraMap h.fixedField K).injective)
  have hℓ' : ∀ a : h.fixedField, ℓ (algebraMap h.fixedField K a) = a :=
    fun a => LinearMap.congr_fun hℓ a
  let u : Fin n → (Fin n × Fin d → h.fixedField) →ₗ[h.fixedField] K :=
    fun i => LinearMap.proj i ∘ₗ T
  let Bm : (Fin n → K) →ₗ[h.fixedField] (Fin n → K) :=
    (Matrix.mulVecLin B).restrictScalars h.fixedField
  let w : Fin n → (Fin n × Fin d → h.fixedField) →ₗ[h.fixedField] K :=
    fun i => LinearMap.proj i ∘ₗ Bm ∘ₗ T
  obtain ⟨P0, hP0d, hP0⟩ := exists_quad_poly_sum Φ ℓ u u
  have hPex := fun j : Fin d => exists_quad_poly_sum Φ (b.coord j) u w
  choose P hPd hP using hPex
  let g : Option (Fin d) → MvPolynomial (Fin n × Fin d) h.fixedField := fun o => o.elim P0 P
  have hgd : ∀ o, (g o).totalDegree ≤ 2 := by
    rintro (_ | j)
    · exact hP0d
    · exact hPd j
  have hlt : ∑ o ∈ Finset.univ, (g o).totalDegree < Fintype.card (Fin n × Fin d) := by
    calc ∑ o ∈ Finset.univ, (g o).totalDegree ≤ ∑ o : Option (Fin d), 2 :=
          Finset.sum_le_sum fun o _ => hgd o
      _ = 2 * (d + 1) := by simp [mul_comm]
      _ < Fintype.card (Fin n × Fin d) := by simp; nlinarith
  have hdvd := char_dvd_card_solutions_of_sum_lt p hlt
  have hex : ∃ x : Fin n × Fin d → h.fixedField, x ≠ 0 ∧
      ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), MvPolynomial.eval x (g o) = 0 := by
    by_contra hcon0
    have hcon : ∀ x : Fin n × Fin d → h.fixedField,
        (∀ o ∈ (Finset.univ : Finset (Option (Fin d))), MvPolynomial.eval x (g o) = 0) →
          x = 0 := fun x hx => by
      by_contra hx0
      exact hcon0 ⟨x, hx0, hx⟩
    have hdvd' : p ∣ Nat.card { x : Fin n × Fin d → h.fixedField //
        ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), MvPolynomial.eval x (g o) = 0 } := by
      rw [Nat.card_eq_fintype_card]; convert hdvd
    have hcard1 : Nat.card { x : Fin n × Fin d → h.fixedField //
        ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), MvPolynomial.eval x (g o) = 0 } ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      exact Subtype.ext ((hcon x hx).trans (hcon y hy).symm)
    have hpos : 0 < Nat.card { x : Fin n × Fin d → h.fixedField //
        ∀ o ∈ (Finset.univ : Finset (Option (Fin d))), MvPolynomial.eval x (g o) = 0 } := by
      refine Nat.card_pos_iff.mpr ⟨⟨⟨0, ?_⟩⟩, inferInstance⟩
      rintro (_ | j) _
      · show MvPolynomial.eval 0 P0 = 0
        rw [hP0]; simp
      · show MvPolynomial.eval 0 (P j) = 0
        rw [hP]; simp
    have := Nat.le_of_dvd hpos hdvd'
    have := h.prime.two_le
    omega
  obtain ⟨x, hx0, hx⟩ := hex
  refine ⟨T x, fun hTx => hx0 (hTinj x hTx), ?_, ?_⟩
  · have h0 := hx none (Finset.mem_univ _)
    simp only [g, Option.elim] at h0
    rw [hP0] at h0
    have hsum : ∑ i, Φ (u i x) (u i x) = hpair h (T x) (T x) := by
      simp [hpair, Φ, u]
    rw [hsum] at h0
    have hc : h.bar (hpair h (T x) (T x)) = hpair h (T x) (T x) := (hpair_comm (T x) (T x)).symm
    have h3 := hℓ' ⟨_, hc⟩
    have e : algebraMap h.fixedField K ⟨_, hc⟩ = hpair h (T x) (T x) := rfl
    rw [e, h0] at h3
    simpa using congrArg Subtype.val h3.symm
  · have hsum : ∑ i, Φ (u i x) (w i x) = hpair h (T x) (B *ᵥ T x) := by
      simp [hpair, Φ, u, w, Bm]
    rw [← hsum, ← (b.forall_coord_eq_zero_iff)]
    intro j
    have h0 := hx (some j) (Finset.mem_univ _)
    simp only [g, Option.elim] at h0
    rwa [hP] at h0

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
