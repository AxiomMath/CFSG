module

public import CFSG.LargeExtraspecial.S12ARS
public import CFSG.LargeExtraspecial.S12TriInput
public import CFSG.LargeExtraspecial.S12Seven

public section

namespace CFSG.LargeExtraspecial

open Subgroup

open CFSG.Open Matrix in
@[expose] def S12FischerConclusion (G : Type) [Group G] (D : Set G) : Prop :=
    (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
    (∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) ∨
    (Nat.card G = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∧ Nat.card D = 3510) ∨
    (Nat.card G = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∧ Nat.card D = 31671) ∨
    (Nat.card G = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 ∧
      Nat.card D = 306936)

@[expose] def S12FischerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G),
    (∃ d₀ : G, D = {g | IsConj d₀ g}) → (∀ d ∈ D, orderOf d = 2) →
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    Subgroup.closure D = ⊤ → Subgroup.center G = ⊥ → IsSimpleGroup (commutator G) →
    S12FischerConclusion G D

namespace S12TranspositionData

variable {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y} {E : Set Y} {t : Y}
  (hD : S12TranspositionData X E t)

include hD

omit [Finite Y] in
theorem preimage_eq_isConj :
    (Subtype.val ⁻¹' E : Set X) = {g | IsConj hD.t' g} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, isConj_iff]
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := hD.cls _ hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy.symm⟩
  · rintro ⟨c, rfl⟩
    exact hD.conj c c.2 t hD.mem

theorem fischer (hTri : FischerTrialityInput) (hFischer : S12FischerStatement)
    (hcen : ∀ y ∈ X, (∀ x ∈ X, x * y = y * x) → y = 1) (hO2 : S12NoNormalTwo X)
    (hO3 : ∀ P : Subgroup Y, P ≤ X → IsPGroup 3 P → X ≤ normalizer (P : Set Y) → P = ⊥)
    (hdeg : ¬ ∃ d ∈ E, ∃ e ∈ E, orderOf (d * e) = 4)
    (hloc : S12NoNormalTwo (fischerQ E ⊓ centralizer {t}) →
      Group.IsSolvable (fischerQ E ⊓ centralizer {t} : Subgroup Y)) :
    S12FischerConclusion X (Subtype.val ⁻¹' E) := by
  have hclass : ∃ d₀ : X, (Subtype.val ⁻¹' E : Set X) = {g | IsConj d₀ g} :=
    ⟨hD.t', hD.preimage_eq_isConj⟩
  have hinv : ∀ d ∈ (Subtype.val ⁻¹' E : Set X), orderOf d = 2 := by
    intro d hd
    refine orderOf_eq_prime ?_ fun h => hD.ne_one _ hd (congrArg Subtype.val h)
    rw [pow_two]
    exact hD.invol' hd
  have hprod : ∀ d ∈ (Subtype.val ⁻¹' E : Set X), ∀ e ∈ (Subtype.val ⁻¹' E : Set X),
      orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
    intro d hd e he
    have hle : orderOf (d * e) ≤ 4 := by
      rw [s12_orderOf_mul_coe]
      exact hD.ord _ hd _ he
    have hne : orderOf (d * e) ≠ 4 := by
      rw [s12_orderOf_mul_coe]
      exact fun h => hdeg ⟨_, hd, _, he, h⟩
    have hpos : 0 < orderOf (d * e) := orderOf_pos _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hgen := s12_closure_preimage_eq_top hD.gen
  have hcenter := s12_center_eq_bot hcen
  have hP : CFSG.Blueprint.Fischer.Pair X (Subtype.val ⁻¹' E) :=
    ⟨inferInstance, hclass, hinv, hprod, hgen⟩
  have h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot (fun P h1 h2 h3 => hO2 P h1 h2 h3) N hN hp
  have h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥ := fun N hN hp =>
    s12_normal_pGroup_eq_bot hO3 N hN hp
  by_cases hcos : ∀ d ∈ (Subtype.val ⁻¹' E : Set X), ∀ e ∈ (Subtype.val ⁻¹' E : Set X),
      d * e ∈ fischerQ (Subtype.val ⁻¹' E : Set X)
  · exact hFischer X _ hclass hinv hprod hgen hcenter
      ((isSimpleGroup_commutator_iff hP hcenter h2 h3).2 hcos)
  · exfalso
    push Not at hcos
    obtain ⟨hns, hno2⟩ := hTri X _ hP hcenter h2 h3 hcos hD.t' hD.mem
    have hmap : (fischerQ (Subtype.val ⁻¹' E : Set X) ⊓ centralizer {hD.t'}).map X.subtype =
        fischerQ E ⊓ centralizer {t} :=
      map_subtype_fischerQ_inf_centralizer hD.subset hD.t'
    have hsol := hloc (hmap ▸ hno2.map_subtype)
    rw [← hmap] at hsol
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := ((fischerQ (Subtype.val ⁻¹' E : Set X) ⊓ centralizer {hD.t'}).equivMapOfInjective
        X.subtype X.subtype_injective).toMonoidHom) (MulEquiv.injective _))

end S12TranspositionData

end CFSG.LargeExtraspecial
