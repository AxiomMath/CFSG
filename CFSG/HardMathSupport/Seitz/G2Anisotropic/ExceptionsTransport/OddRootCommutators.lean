module

public import CFSG.LieType.Chevalley.EvenRootCommutatorTransport

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  MvPolynomial
open scoped commutatorElement

variable {τ : Tag}

theorem pinnedX_commutator_smul_signed
    {r : PairRow} (hr : r ∈ pairTable τ) (w : WeylGroup τ) :
    ∃ εf : ℕ × ℕ × ℕ × ℤ → ℤ, (∀ f, εf f = 1 ∨ εf f = -1) ∧
      ∀ {R : Type} [CommRing R] (x y : R),
        pinnedX τ R (w • orbitCertRoot τ r.1) x * pinnedX τ R (w • orbitCertRoot τ r.2.1) y *
            pinnedX τ R (w • orbitCertRoot τ r.1) (-x) *
            pinnedX τ R (w • orbitCertRoot τ r.2.1) (-y) =
          (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
            (((εf f * f.2.2.2 : ℤ) : R) * x ^ f.1 * y ^ f.2.1)).prod := by
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
  classical
  let eint : (Fin τ.rank → ℤ) → ℤ := fun γ => if ε γ = 1 then 1 else -1
  have heint : ∀ γ, eint γ = 1 ∨ eint γ = -1 := fun γ => by
    by_cases h : ε γ = 1 <;> simp [eint, h]
  have hne : (-1 : MvPolynomial (Fin 2) ℤ) ≠ 1 := by
    intro h1
    have := congrArg MvPolynomial.constantCoeff h1
    simp at this
  have hεint : ∀ γ, ε γ = ((eint γ : ℤ) : MvPolynomial (Fin 2) ℤ) := fun γ => by
    rcases hε γ with h | h
    · simp [eint, h]
    · have h1 : ¬ ε γ = 1 := by rw [h]; exact hne
      simp [eint, h]
  have hsq : ∀ γ, eint γ * eint γ = 1 := fun γ => by
    rcases heint γ with h | h <;> rw [h] <;> norm_num
  have hunit : ∀ γ, IsUnit (eint γ) := fun γ => by
    rcases heint γ with h | h <;> rw [h]
    · exact isUnit_one
    · exact (Int.isUnit_iff.2 (Or.inr rfl))
  refine ⟨fun f => eint (orbitCertRoot τ f.2.2.1) * eint (orbitCertRoot τ r.1) ^ f.1 *
    eint (orbitCertRoot τ r.2.1) ^ f.2.1, fun f => ?_, ?_⟩
  · exact Int.isUnit_iff.1 (((hunit _).mul ((hunit _).pow _)).mul ((hunit _).pow _))
  · intro R _ x y
    set a₀ := orbitCertRoot τ r.1 with ha₀
    set b₀ := orbitCertRoot τ r.2.1 with hb₀
    set g : MvPolynomial (Fin 2) ℤ →+* R :=
      eval₂Hom (Int.castRingHom R) ![((eint a₀ : ℤ) : R) * x, ((eint b₀ : ℤ) : R) * y] with hg
    have hg0 : g (X 0) = ((eint a₀ : ℤ) : R) * x := eval₂Hom_X' _ _ _
    have hg1 : g (X 1) = ((eint b₀ : ℤ) : R) * y := eval₂Hom_X' _ _ _
    have hgε : ∀ γ, g (ε γ) = ((eint γ : ℤ) : R) := fun γ => by
      rw [hεint γ]; exact map_intCast g _
    have hsqR : ∀ γ, ((eint γ : ℤ) : R) * ((eint γ : ℤ) : R) = 1 := fun γ => by
      have := congrArg (Int.cast : ℤ → R) (hsq γ)
      simpa using this
    have hL := (((baseChange_pinnedX g (w • a₀) (ε a₀ * X 0)).mul
      (baseChange_pinnedX g (w • b₀) (ε b₀ * X 1))).mul
      (baseChange_pinnedX g (w • a₀) (ε a₀ * -X 0))).mul
      (baseChange_pinnedX g (w • b₀) (ε b₀ * -X 1))
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hid'] at hL
    have hR := baseChange_prod_map_pinnedX g r.2.2.2 (fun f => w • orbitCertRoot τ f.2.2.1)
      (fun f => ε (orbitCertRoot τ f.2.2.1) *
        ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1))
    simp only [map_mul, map_neg, hg0, hg1, hgε, map_pow, map_intCast] at hL hR
    have e1 : ∀ (γ : Fin τ.rank → ℤ) (z : R), ((eint γ : ℤ) : R) * (((eint γ : ℤ) : R) * z) = z := fun γ z => by
      rw [← mul_assoc, hsqR, one_mul]
    simp only [mul_neg, e1] at hL
    have hmap : (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
        ((((eint (orbitCertRoot τ f.2.2.1) * eint a₀ ^ f.1 * eint b₀ ^ f.2.1 * f.2.2.2 : ℤ)
          : R) * x ^ f.1 * y ^ f.2.1))) =
        (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
        (((eint (orbitCertRoot τ f.2.2.1) : ℤ) : R) *
          ((f.2.2.2 : R) * (((eint a₀ : ℤ) : R) * x) ^ f.1 * (((eint b₀ : ℤ) : R) * y) ^ f.2.1))) := by
      refine List.map_congr_left fun f _ => ?_
      congr 1
      push_cast
      ring
    rw [hmap]
    refine Units.ext ?_
    simp only [Units.val_mul]
    exact hL.unique hR

theorem commutatorElement_pinnedX_signed
    {r : PairRow} (hr : r ∈ pairTable τ) (w : WeylGroup τ) :
    ∃ εf : ℕ × ℕ × ℕ × ℤ → ℤ, (∀ f, εf f = 1 ∨ εf f = -1) ∧
      ∀ {R : Type} [CommRing R] {α β : Fin τ.rank → ℤ}
        (_ : w • orbitCertRoot τ r.1 = α) (_ : w • orbitCertRoot τ r.2.1 = β) (x y : R),
        ⁅pinnedX τ R α x, pinnedX τ R β y⁆ =
          (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
            (((εf f * f.2.2.2 : ℤ) : R) * x ^ f.1 * y ^ f.2.1)).prod := by
  obtain ⟨εf, hεf, h⟩ := pinnedX_commutator_smul_signed hr w
  refine ⟨εf, hεf, fun {R} _ {α β} hα hβ x y => ?_⟩
  subst hα hβ
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact h x y

theorem commute_pinnedX_of_nil
    {r : PairRow} (hr : r ∈ pairTable τ) (hnil : r.2.2.2 = []) (w : WeylGroup τ)
    {R : Type} [CommRing R] {α β : Fin τ.rank → ℤ} (hα : w • orbitCertRoot τ r.1 = α)
    (hβ : w • orbitCertRoot τ r.2.1 = β) (x y : R) :
    Commute (pinnedX τ R α x) (pinnedX τ R β y) := by
  obtain ⟨εf, -, h⟩ := commutatorElement_pinnedX_signed hr w
  have := h hα hβ x y
  rwa [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute] at this

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
