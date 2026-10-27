module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Polynomial

namespace CFSG.GH74.GLS.Stage4.Hex

structure GalData (F K : Type) [Field F] [Field K] where
  θ : F →+* K
  σ : K →+* K
  q : ℕ
  hq : 3 ≤ q
  hF : Nat.card F = q
  hK : Nat.card K = q ^ 3
  hσ : ∀ x, σ x = x ^ q

namespace GalData

variable {F K : Type} [Field F] [Field K]

theorem finiteK (G : GalData F K) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [G.hK]; have := G.hq; positivity)

theorem finiteF (G : GalData F K) : Finite F :=
  Nat.finite_of_card_ne_zero (by rw [G.hF]; have := G.hq; omega)

theorem pow_card_K (G : GalData F K) (x : K) : x ^ (G.q ^ 3) = x := by
  have := G.finiteK
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, G.hK] at h
  exact h

theorem pow_card_F (G : GalData F K) (c : F) : c ^ G.q = c := by
  have := G.finiteF
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, G.hF] at h
  exact h

theorem σ3 (G : GalData F K) (x : K) : G.σ (G.σ (G.σ x)) = x := by
  rw [G.hσ, G.hσ, G.hσ, ← pow_mul, ← pow_mul]
  have := G.pow_card_K x
  rwa [show G.q * (G.q * G.q) = G.q ^ 3 by ring]

theorem σ_θ (G : GalData F K) (c : F) : G.σ (G.θ c) = G.θ c := by
  rw [G.hσ, ← map_pow, G.pow_card_F]

theorem fixed_card_le (G : GalData F K) (S : Finset K) (hS : ∀ x ∈ S, x ^ G.q = x) :
    S.card ≤ G.q := by
  classical
  have hq := G.hq
  have hc : (X ^ G.q - X : K[X]).coeff G.q = 1 := by
    rw [coeff_sub, coeff_X_pow, coeff_X]
    have : G.q ≠ 1 := by omega
    simp [Ne.symm this]
  have hne : (X ^ G.q - X : K[X]) ≠ 0 := by
    intro h
    rw [h] at hc
    simp at hc
  have hdeg : (X ^ G.q - X : K[X]).natDegree = G.q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
    omega
  calc S.card ≤ (X ^ G.q - X : K[X]).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp [Multiset.mem_toFinset, mem_roots hne, hS x hx]
    _ ≤ Multiset.card (X ^ G.q - X : K[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ G.q - X : K[X]).natDegree := card_roots' _
    _ = G.q := hdeg

theorem fixed_eq (G : GalData F K) {x : K} (hx : G.σ x = x) : ∃ c, G.θ c = x := by
  classical
  have := G.finiteK
  have := G.finiteF
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F
  by_contra hcon
  simp only [not_exists] at hcon
  have hinj : Function.Injective G.θ := G.θ.injective
  let S : Finset K := Finset.univ.image G.θ ∪ {x}
  have hS : ∀ y ∈ S, y ^ G.q = y := by
    intro y hy
    rcases Finset.mem_union.1 hy with h | h
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
      rw [← map_pow, G.pow_card_F]
    · rw [Finset.mem_singleton.1 h, ← G.hσ, hx]
  have hcard := G.fixed_card_le S hS
  have hdisj : Disjoint (Finset.univ.image G.θ) {x} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
    exact hcon c hc
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
    Finset.card_singleton, Finset.card_univ, ← Nat.card_eq_fintype_card, G.hF] at hcard
  omega

theorem tr_exists (G : GalData F K) (s : K) : ∃ c : F, G.θ c = s + G.σ s + G.σ (G.σ s) := by
  apply G.fixed_eq
  rw [map_add, map_add, G.σ3]; ring

noncomputable def trF (G : GalData F K) (s : K) : F := Classical.choose (G.tr_exists s)

theorem θ_trF (G : GalData F K) (s : K) : G.θ (G.trF s) = s + G.σ s + G.σ (G.σ s) :=
  Classical.choose_spec (G.tr_exists s)

theorem trF_add (G : GalData F K) (s s' : K) : G.trF (s + s') = G.trF s + G.trF s' := by
  apply G.θ.injective
  rw [map_add, G.θ_trF, G.θ_trF, G.θ_trF, map_add, map_add]
  ring

theorem trF_smul (G : GalData F K) (c : F) (s : K) : G.trF (G.θ c * s) = c * G.trF s := by
  apply G.θ.injective
  rw [map_mul, G.θ_trF, G.θ_trF]
  simp only [map_mul, G.σ_θ]
  ring

theorem trF_ne_zero (G : GalData F K) : ∃ s, G.trF s ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have := G.finiteK
  have := Fintype.ofFinite K
  have h : ∀ s : K, s + s ^ G.q + s ^ (G.q * G.q) = 0 := by
    intro s
    have := G.θ_trF s
    rw [hcon s, map_zero, G.hσ, G.hσ, ← pow_mul] at this
    exact this.symm
  have hq := G.hq
  let P : K[X] := X + X ^ G.q + X ^ (G.q * G.q)
  have hdeg : P.natDegree = G.q * G.q := by
    have h1 : G.q < G.q * G.q := by nlinarith
    have h2 : (1 : ℕ) < G.q * G.q := by nlinarith
    show (X + X ^ G.q + X ^ (G.q * G.q) : K[X]).natDegree = G.q * G.q
    rw [natDegree_add_eq_right_of_natDegree_lt]
    · simp
    · rw [natDegree_add_eq_right_of_natDegree_lt] <;> simp <;> omega
  have hcard : P.natDegree < Fintype.card K := by
    rw [hdeg, ← Nat.card_eq_fintype_card, G.hK]
    nlinarith
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card P _
    · rw [Cardinal.mk_fintype]; exact_mod_cast hcard
    intro x
    simp [P, h x]
  have hc : P.coeff (G.q * G.q) = 1 := by
    have h1 : G.q * G.q ≠ G.q := by nlinarith
    have h2 : 1 ≠ G.q * G.q := by nlinarith
    simp [P, coeff_X_pow, coeff_X, h1, h2]
  rw [hzero] at hc
  simp at hc

theorem trF_zero (G : GalData F K) : G.trF 0 = 0 := by
  have := G.trF_add 0 0
  rw [add_zero] at this
  exact add_eq_left.1 this.symm

theorem trF_neg (G : GalData F K) (s : K) : G.trF (-s) = - G.trF s := by
  have := G.trF_add s (-s)
  rw [add_neg_cancel, G.trF_zero] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem eq_of_trF_eq (G : GalData F K) {a a' : K}
    (h : ∀ s, G.trF (a * s) = G.trF (a' * s)) : a = a' := by
  by_contra hne
  have hne' : a - a' ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨s₀, hs₀⟩ := G.trF_ne_zero
  have h1 := h ((a - a')⁻¹ * s₀)
  have h2 : a * ((a - a')⁻¹ * s₀) = (a - a') * ((a - a')⁻¹ * s₀) + a' * ((a - a')⁻¹ * s₀) := by
    ring
  rw [h2, G.trF_add, mul_inv_cancel_left₀ hne'] at h1
  exact hs₀ (add_eq_right.1 h1)

theorem dual_rep (G : GalData F K) (f : K → F) (hadd : ∀ s s', f (s + s') = f s + f s')
    (hhom : ∀ (c : F) s, f (G.θ c * s) = c * f s) : ∃ a : K, ∀ s, f s = G.trF (a * s) := by
  classical
  let _ : Module F K := Module.compHom K G.θ
  have := G.finiteK
  have : Module.Finite F K := Module.Finite.of_finite
  have hsmul : ∀ (c : F) (s : K), c • s = G.θ c * s := fun c s => rfl
  let Ψ : K →ₗ[F] Module.Dual F K :=
    { toFun := fun a =>
        { toFun := fun s => G.trF (a * s)
          map_add' := fun s s' => by rw [mul_add, G.trF_add]
          map_smul' := fun c s => by
            rw [hsmul, show a * (G.θ c * s) = G.θ c * (a * s) by ring, G.trF_smul]
            rfl }
      map_add' := fun a a' => by
        ext s
        show G.trF ((a + a') * s) = G.trF (a * s) + G.trF (a' * s)
        rw [add_mul, G.trF_add]
      map_smul' := fun c a => by
        ext s
        show G.trF ((c • a) * s) = c * G.trF (a * s)
        rw [hsmul, mul_assoc, G.trF_smul] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    obtain ⟨s₀, hs₀⟩ := G.trF_ne_zero
    have h1 : G.trF (a * (a⁻¹ * s₀)) = 0 := LinearMap.congr_fun ha (a⁻¹ * s₀)
    rw [mul_inv_cancel_left₀ hne] at h1
    exact hs₀ h1
  have hrank : Module.finrank F K = Module.finrank F (Module.Dual F K) :=
    (Subspace.dual_finrank_eq).symm
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj
  let fl : Module.Dual F K :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c s => by
        rw [hsmul, hhom]
        rfl }
  obtain ⟨a, ha⟩ := hsurj fl
  refine ⟨a, fun s => ?_⟩
  have := LinearMap.congr_fun ha s
  exact this.symm

theorem finrank_eq (G : GalData F K) :
    letI := G.θ.toAlgebra
    Module.finrank F K = 3 := by
  let _ := G.θ.toAlgebra
  have := G.finiteK
  have := G.finiteF
  have : Module.Finite F K := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := F) (V := K)
  rw [G.hK, G.hF] at h
  have hq := G.hq
  exact (Nat.pow_right_injective (by omega : 2 ≤ G.q) h).symm

theorem indep3 (G : GalData F K) (a₀ a₁ a₂ : K)
    (h : ∀ s : K, a₀ * s + a₁ * G.σ s + a₂ * G.σ (G.σ s) = 0) : a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
  classical
  have := G.finiteK
  have := Fintype.ofFinite K
  have hq := G.hq
  have h' : ∀ s : K, a₀ * s + a₁ * s ^ G.q + a₂ * s ^ (G.q * G.q) = 0 := by
    intro s
    have := h s
    rwa [G.hσ, G.hσ, ← pow_mul] at this
  let P : K[X] := C a₀ * X ^ 1 + C a₁ * X ^ G.q + C a₂ * X ^ (G.q * G.q)
  have hq1 : G.q ≠ 1 := by omega
  have hqq1 : G.q * G.q ≠ 1 := by nlinarith
  have hqqq : G.q * G.q ≠ G.q := by nlinarith
  have hdeg : P.natDegree < Fintype.card K := by
    have h1 : G.q < G.q * G.q := by nlinarith
    have : P.natDegree ≤ G.q * G.q := by
      refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · exact (natDegree_C_mul_X_pow_le a₀ 1).trans (by omega)
      · exact (natDegree_C_mul_X_pow_le a₁ G.q).trans h1.le
      · exact natDegree_C_mul_X_pow_le a₂ _
    rw [← Nat.card_eq_fintype_card, G.hK]
    have : G.q * G.q < G.q ^ 3 := by nlinarith
    omega
  have hzero : P = 0 := by
    apply Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card P _
    · rw [Cardinal.mk_fintype]; exact_mod_cast hdeg
    intro x
    simp [P, h' x]
  have hc1 : P.coeff 1 = a₀ := by
    simp [P, coeff_X_pow, coeff_C_mul, Ne.symm hq1, Ne.symm hqq1]
  have hcq : P.coeff G.q = a₁ := by
    simp [P, coeff_X_pow, coeff_C_mul, coeff_X, Ne.symm hq1, Ne.symm hqqq]
  have hcqq : P.coeff (G.q * G.q) = a₂ := by
    simp [P, coeff_X_pow, coeff_C_mul, coeff_X, Ne.symm hqq1, hqqq]
  rw [hzero] at hc1 hcq hcqq
  simp at hc1 hcq hcqq
  exact ⟨hc1.symm, hcq.symm, hcqq.symm⟩

theorem lin_rep (G : GalData F K) (f : K → K) (hadd : ∀ s s', f (s + s') = f s + f s')
    (hhom : ∀ (c : F) s, f (G.θ c * s) = G.θ c * f s) :
    ∃ a₀ a₁ a₂ : K, ∀ s, f s = a₀ * s + a₁ * G.σ s + a₂ * G.σ (G.σ s) := by
  classical
  let _ := G.θ.toAlgebra
  have hsm : ∀ (c : F) (s : K), c • s = G.θ c * s := fun c s => rfl
  have hfin := G.finiteK
  have : Module.Finite F K := Module.Finite.of_finite
  let L0 : K →ₗ[F] K := LinearMap.id
  let L1 : K →ₗ[F] K :=
    { toFun := G.σ
      map_add' := map_add G.σ
      map_smul' := fun c s => by rw [hsm, RingHom.id_apply, hsm, map_mul, G.σ_θ] }
  let L2 : K →ₗ[F] K :=
    { toFun := fun s => G.σ (G.σ s)
      map_add' := fun s s' => by simp only [map_add]
      map_smul' := fun c s => by
        rw [hsm, RingHom.id_apply, hsm]
        simp only [map_mul, G.σ_θ] }
  let fl : K →ₗ[F] K :=
    { toFun := f
      map_add' := hadd
      map_smul' := fun c s => by rw [hsm, RingHom.id_apply, hsm, hhom] }
  have hli : LinearIndependent K ![L0, L1, L2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h : ∀ s, g 0 * s + g 1 * G.σ s + g 2 * G.σ (G.σ s) = 0 := fun s => by
      have := LinearMap.congr_fun hg s
      simpa [Fin.sum_univ_three, L0, L1, L2] using this
    have := G.indep3 _ _ _ h
    fin_cases i <;> simp [this]
  have hrank : Module.finrank K (K →ₗ[F] K) = 3 := by
    rw [Module.finrank_linearMap F K K K, G.finrank_eq]
    simp
  have hspan : Submodule.span K (Set.range ![L0, L1, L2]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hrank])
  have hmem : fl ∈ Submodule.span K (Set.range ![L0, L1, L2]) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨g 0, g 1, g 2, fun s => ?_⟩
  have := LinearMap.congr_fun hg s
  simpa [Fin.sum_univ_three, L0, L1, L2, fl] using this.symm

end GalData

end CFSG.GH74.GLS.Stage4.Hex
