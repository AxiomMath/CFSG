module

public import CFSG.LieType.Chevalley.EvenRootCommutatorTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem isSign_mul {R : Type*} [CommRing R] {a b : R} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem isSign_pow {R : Type*} [CommRing R] {a : R} (ha : a = 1 ∨ a = -1) (n : ℕ) :
    a ^ n = 1 ∨ a ^ n = -1 := by
  induction n with
  | zero => exact Or.inl (pow_zero a)
  | succ n ih =>
    rw [pow_succ]
    exact isSign_mul ih ha

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps MvPolynomial
open scoped commutatorElement

variable {τ : Tag}

theorem pinnedX_commutator_smul_signs {R : Type*} [CommRing R] {r : PairRow}
    (hr : r ∈ pairTable τ) (w : WeylGroup τ) :
    ∃ e : (Fin τ.rank → ℤ) → R, (∀ γ, e γ = 1 ∨ e γ = -1) ∧ ∀ x y : R,
      pinnedX τ R (w • orbitCertRoot τ r.1) (e (orbitCertRoot τ r.1) * x) *
        pinnedX τ R (w • orbitCertRoot τ r.2.1) (e (orbitCertRoot τ r.2.1) * y) *
        pinnedX τ R (w • orbitCertRoot τ r.1) (e (orbitCertRoot τ r.1) * -x) *
        pinnedX τ R (w • orbitCertRoot τ r.2.1) (e (orbitCertRoot τ r.2.1) * -y) =
      (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
        (e (orbitCertRoot τ f.2.2.1) * ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1))).prod := by
  obtain ⟨-, -, hα, hβ, -, -, -, -, hfac, -, -, hid⟩ := (rank_two_pair_certificate τ).2 r hr
  set n := canonicalRep (coxeterSystem τ) (MvPolynomial (Fin 2) ℤ) w
  have hsign : ∀ γ : Fin τ.rank → ℤ, ∃ ε : MvPolynomial (Fin 2) ℤ, (ε = 1 ∨ ε = -1) ∧
      (IsRoot τ γ → ∀ c, n * pinnedX τ (MvPolynomial (Fin 2) ℤ) γ c * n⁻¹ =
        pinnedX τ (MvPolynomial (Fin 2) ℤ) (w • γ) (ε * c)) := by
    intro γ
    by_cases hγ : IsRoot τ γ
    · obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (MvPolynomial (Fin 2) ℤ) w hγ
      exact ⟨ε, mul_self_eq_one_iff.1 hε, fun _ => h⟩
    · exact ⟨1, Or.inl rfl, fun h => absurd h hγ⟩
  choose ε hε hconj using hsign
  have hroot : ∀ f ∈ r.2.2.2, IsRoot τ (orbitCertRoot τ f.2.2.1) := fun f hf =>
    isRoot_decodeVec_witness ((hfac f.1 f.2.1 f.2.2.1).1 ⟨f.2.2.2, hf⟩).2.2.1
  have hid' := congrArg (fun g => n * g * n⁻¹) hid
  have e4 : ∀ a b c d : (Module.End (MvPolynomial (Fin 2) ℤ)
      (RootModule τ (MvPolynomial (Fin 2) ℤ)))ˣ, n * (a * b * c * d) * n⁻¹ =
      (n * a * n⁻¹) * (n * b * n⁻¹) * (n * c * n⁻¹) * (n * d * n⁻¹) := fun _ _ _ _ => by group
  have hprod : ∀ L : List (ℕ × ℕ × ℕ × ℤ), (∀ f ∈ L, IsRoot τ (orbitCertRoot τ f.2.2.1)) →
      n * (L.map fun f => pinnedX τ (MvPolynomial (Fin 2) ℤ) (orbitCertRoot τ f.2.2.1)
        ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1)).prod * n⁻¹ =
      (L.map fun f => pinnedX τ (MvPolynomial (Fin 2) ℤ) (w • orbitCertRoot τ f.2.2.1)
        (ε (orbitCertRoot τ f.2.2.1) *
          ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1))).prod := by
    intro L hL
    induction L with
    | nil => simp
    | cons f L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← ih fun g hg => hL g (List.mem_cons_of_mem _ hg), ← hconj _ (hL f List.mem_cons_self)]
      group
  simp only [e4, hconj _ hα, hconj _ hβ, hprod _ hroot] at hid'
  have hgε' : ∀ (g : MvPolynomial (Fin 2) ℤ →+* R) γ, g (ε γ) = 1 ∨ g (ε γ) = -1 := fun g γ => by
    rcases hε γ with h | h <;> rw [h]
    · exact Or.inl (map_one g)
    · exact Or.inr (by rw [map_neg, map_one])
  refine ⟨fun γ => (Int.castRingHom R) (if ε γ = 1 then 1 else -1), ?_, ?_⟩
  · intro γ
    by_cases h : ε γ = 1
    · simp [h]
    · simp [h]
  · intro x y
    set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![x, y]
    have hg0 : g (X 0) = x := eval₂Hom_X' _ _ _
    have hg1 : g (X 1) = y := eval₂Hom_X' _ _ _
    have hgε : ∀ γ, g (ε γ) = (Int.castRingHom R) (if ε γ = 1 then 1 else -1) := fun γ => by
      rcases hε γ with h | h
      · simp [h]
      · have : ¬ ((-1 : MvPolynomial (Fin 2) ℤ) = 1) := by
          intro h1
          have := congrArg (MvPolynomial.constantCoeff) h1
          simp at this
        simp [h, this]
    have hL := (((baseChange_pinnedX g (w • orbitCertRoot τ r.1)
      (ε (orbitCertRoot τ r.1) * X 0)).mul
      (baseChange_pinnedX g (w • orbitCertRoot τ r.2.1) (ε (orbitCertRoot τ r.2.1) * X 1))).mul
      (baseChange_pinnedX g (w • orbitCertRoot τ r.1) (ε (orbitCertRoot τ r.1) * -X 0))).mul
      (baseChange_pinnedX g (w • orbitCertRoot τ r.2.1) (ε (orbitCertRoot τ r.2.1) * -X 1))
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hid'] at hL
    have hR := baseChange_prod_map_pinnedX g r.2.2.2 (fun f => w • orbitCertRoot τ f.2.2.1)
      (fun f => ε (orbitCertRoot τ f.2.2.1) *
        ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1))
    simp only [map_mul, map_neg, hg0, hg1, hgε, map_pow, map_intCast] at hL hR
    refine Units.ext ?_
    simp only [Units.val_mul]
    exact hL.unique hR


theorem commutatorElement_pinnedX_signs {R : Type*} [CommRing R] {r : PairRow}
    (hr : r ∈ pairTable τ) (w : WeylGroup τ) {α β : Fin τ.rank → ℤ}
    (hα : w • orbitCertRoot τ r.1 = α) (hβ : w • orbitCertRoot τ r.2.1 = β) :
    ∃ σ : ℕ × ℕ × ℕ × ℤ → R, (∀ f, σ f = 1 ∨ σ f = -1) ∧ ∀ x y : R,
      ⁅pinnedX τ R α x, pinnedX τ R β y⁆ =
        (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
          (σ f * ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1))).prod := by
  subst hα hβ
  obtain ⟨e, he, hform⟩ := pinnedX_commutator_smul_signs (R := R) hr w
  have hsq : ∀ γ, e γ * e γ = 1 := fun γ => by rcases he γ with h | h <;> simp [h]
  refine ⟨fun f => e (orbitCertRoot τ f.2.2.1) *
    (e (orbitCertRoot τ r.1) ^ f.1 * e (orbitCertRoot τ r.2.1) ^ f.2.1), ?_, ?_⟩
  · intro f
    exact isSign_mul (he _) (isSign_mul (isSign_pow (he _) _) (isSign_pow (he _) _))
  · intro x y
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
    have h := hform (e (orbitCertRoot τ r.1) * x) (e (orbitCertRoot τ r.2.1) * y)
    have e1 : e (orbitCertRoot τ r.1) * (e (orbitCertRoot τ r.1) * x) = x := by
      rw [← mul_assoc, hsq, one_mul]
    have e2 : e (orbitCertRoot τ r.2.1) * (e (orbitCertRoot τ r.2.1) * y) = y := by
      rw [← mul_assoc, hsq, one_mul]
    have e3 : e (orbitCertRoot τ r.1) * -(e (orbitCertRoot τ r.1) * x) = -x := by
      rw [mul_neg, ← mul_assoc, hsq, one_mul]
    have e4 : e (orbitCertRoot τ r.2.1) * -(e (orbitCertRoot τ r.2.1) * y) = -y := by
      rw [mul_neg, ← mul_assoc, hsq, one_mul]
    rw [e1, e2, e3, e4] at h
    rw [h]
    refine congrArg List.prod (List.map_congr_left fun f _ => ?_)
    congr 1
    simp only [mul_pow]
    ring

theorem commute_pinnedX_of_nil {R : Type*} [CommRing R] {r : PairRow} (hr : r ∈ pairTable τ)
    (hnil : r.2.2.2 = []) (w : WeylGroup τ) {α β : Fin τ.rank → ℤ}
    (hα : w • orbitCertRoot τ r.1 = α) (hβ : w • orbitCertRoot τ r.2.1 = β) (x y : R) :
    Commute (pinnedX τ R α x) (pinnedX τ R β y) := by
  obtain ⟨σ, -, h⟩ := commutatorElement_pinnedX_signs (R := R) hr w hα hβ
  have h1 := h x y
  rwa [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute] at h1

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
