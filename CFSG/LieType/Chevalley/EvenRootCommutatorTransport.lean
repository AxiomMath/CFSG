module

public import CFSG.LieType.Chevalley.RootCommutatorCertificate
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps MvPolynomial
open scoped commutatorElement

variable {τ : Tag}

theorem baseChange_prod_map_pinnedX
    {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    {ι : Type*} (L : List ι) (γ : ι → Fin τ.rank → ℤ) (c : ι → R) :
    BaseChange g
      (((L.map fun i => pinnedX τ R (γ i) (c i)).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R))
      (((L.map fun i => pinnedX τ S (γ i) (g (c i))).prod : (Module.End S (RootModule τ S))ˣ) :
        Module.End S (RootModule τ S)) := by
  induction L with
  | nil => simpa using BaseChange.one (τ := τ) (f := g)
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact (baseChange_pinnedX g (γ a) (c a)).mul ih

theorem pinnedX_commutator_smul_of_two_eq_zero
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {r : PairRow} (hr : r ∈ pairTable τ) (w : WeylGroup τ) (x y : R) :
    pinnedX τ R (w • orbitCertRoot τ r.1) x * pinnedX τ R (w • orbitCertRoot τ r.2.1) y *
        pinnedX τ R (w • orbitCertRoot τ r.1) (-x) *
        pinnedX τ R (w • orbitCertRoot τ r.2.1) (-y) =
      (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
        ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod := by
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
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![x, y]
  have hg0 : g (X 0) = x := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = y := eval₂Hom_X' _ _ _
  have hgε : ∀ γ, g (ε γ) = 1 := fun γ => by
    rcases hε γ with h | h <;> rw [h]
    · exact map_one g
    · rw [map_neg, map_one]
      exact neg_eq_iff_add_eq_zero.2 (by rw [one_add_one_eq_two, h2])
  have hL := (((baseChange_pinnedX g (w • orbitCertRoot τ r.1)
    (ε (orbitCertRoot τ r.1) * X 0)).mul
    (baseChange_pinnedX g (w • orbitCertRoot τ r.2.1) (ε (orbitCertRoot τ r.2.1) * X 1))).mul
    (baseChange_pinnedX g (w • orbitCertRoot τ r.1) (ε (orbitCertRoot τ r.1) * -X 0))).mul
    (baseChange_pinnedX g (w • orbitCertRoot τ r.2.1) (ε (orbitCertRoot τ r.2.1) * -X 1))
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hid'] at hL
  have hR := baseChange_prod_map_pinnedX g r.2.2.2 (fun f => w • orbitCertRoot τ f.2.2.1)
    (fun f => ε (orbitCertRoot τ f.2.2.1) *
      ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1))
  simp only [map_mul, map_neg, hg0, hg1, hgε, one_mul, map_pow, map_intCast] at hL hR
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact hL.unique hR

theorem commutatorElement_pinnedX_of_two_eq_zero
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {r : PairRow} (hr : r ∈ pairTable τ) (w : WeylGroup τ) {α β : Fin τ.rank → ℤ}
    (hα : w • orbitCertRoot τ r.1 = α) (hβ : w • orbitCertRoot τ r.2.1 = β) (x y : R) :
    ⁅pinnedX τ R α x, pinnedX τ R β y⁆ =
      (r.2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
        ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod := by
  subst hα hβ
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact pinnedX_commutator_smul_of_two_eq_zero h2 hr w x y

theorem commute_pinnedX_of_two_eq_zero
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {r : PairRow} (hr : r ∈ pairTable τ) (hnil : r.2.2.2 = []) (w : WeylGroup τ)
    {α β : Fin τ.rank → ℤ} (hα : w • orbitCertRoot τ r.1 = α)
    (hβ : w • orbitCertRoot τ r.2.1 = β) (x y : R) :
    Commute (pinnedX τ R α x) (pinnedX τ R β y) := by
  have h := commutatorElement_pinnedX_of_two_eq_zero h2 hr w hα hβ x y
  rwa [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute] at h

end CFSG.LieType.Chevalley
