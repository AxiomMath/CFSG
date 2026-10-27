module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailShortRoot

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (P : HypPair Q) (A : Submodule K V)

@[expose] noncomputable def exchTorus : Subgroup (V ≃ₗ[K] V) :=
  orthElementaryGroup Q ⊓ (MulAction.stabilizer (V ≃ₗ[K] V) (K ∙ P.e) ⊓
    MulAction.stabilizer (V ≃ₗ[K] V) (K ∙ P.f) ⊓ MulAction.stabilizer (V ≃ₗ[K] V) A)

variable {P A}

theorem mem_exchTorus {g : V ≃ₗ[K] V} :
    g ∈ exchTorus P A ↔ g ∈ orthElementaryGroup Q ∧
      (K ∙ P.e).map (g : V →ₗ[K] V) = K ∙ P.e ∧ (K ∙ P.f).map (g : V →ₗ[K] V) = K ∙ P.f ∧
      A.map (g : V →ₗ[K] V) = A := by
  simp only [exchTorus, Subgroup.mem_inf, Submodule.mem_stabilizer_submodule_iff_map_eq,
    and_assoc]
  rfl

theorem map_span_singleton_of_apply_eq {g : V ≃ₗ[K] V} {x : V} {c : K} (hc : c ≠ 0)
    (hg : g x = c • x) : (K ∙ x).map (g : V →ₗ[K] V) = K ∙ x := by
  rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hg,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

section Weyl

variable (P) {b : V} (hb : b ∈ P.perp) (hd : Q b ≠ 0)
include hb hd

theorem shortWeyl_inv : (shortWeyl P b)⁻¹ = shortWeyl P b :=
  inv_eq_of_mul_eq_one_right (shortWeyl_mul_self P hb hd)

omit hb hd in
theorem shortWeyl_neg :
    shortWeyl P (-b) =
      eichler Q P.e (-b) * eichler Q P.f (-((Q b)⁻¹ • b)) * eichler Q P.e (-b) := by
  rw [shortWeyl, QuadraticMap.map_neg, smul_neg]

omit hd in
theorem shortWeyl_neg_mul_eichler :
    shortWeyl P (-b) * eichler Q P.e b = eichler Q P.e (-b) * eichler Q P.f (-((Q b)⁻¹ • b)) := by
  have hpb : polar Q P.e b = 0 := (HypPair.mem_perp.1 hb).1
  rw [shortWeyl_neg P, mul_assoc,
    eichler_mul (by rw [polar_neg_right, hpb, neg_zero]) hpb, neg_add_cancel,
    eichler_zero_right, mul_one]

theorem map_shortWeyl_eq (hA : A ≤ P.perp) (hbA : b ∈ A) :
    A.map (shortWeyl P b : V →ₗ[K] V) = A := by
  have hmaps : ∀ z ∈ A, shortWeyl P b z ∈ A := fun z hz => by
    rw [shortWeyl_perp P hb hd (hA hz)]
    exact sub_mem hz (Submodule.smul_mem _ _ hbA)
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hmaps z hz
  · refine ⟨shortWeyl P b z, hmaps z hz, ?_⟩
    change (shortWeyl P b * shortWeyl P b) z = z
    rw [shortWeyl_mul_self P hb hd, LinearEquiv.coe_one, id_eq]

end Weyl

section Torus

variable (P) {a₀ a : V} (ha₀ : a₀ ∈ P.perp) (hd₀ : Q a₀ ≠ 0) (ha : a ∈ P.perp) (hd : Q a ≠ 0)
include ha₀ hd₀ ha hd

theorem shortWeyl_mul_inv_e :
    (shortWeyl P a₀ * (shortWeyl P (-a))⁻¹) P.e = ((Q a)⁻¹ * Q a₀) • P.e := by
  have ha' : -a ∈ P.perp := neg_mem ha
  have hd' : Q (-a) ≠ 0 := by rwa [QuadraticMap.map_neg]
  rw [shortWeyl_inv P ha' hd', LinearEquiv.mul_apply, shortWeyl_e P ha' hd', map_smul,
    shortWeyl_f P ha₀ hd₀, QuadraticMap.map_neg, smul_smul]
  congr 1
  ring

theorem shortWeyl_mul_inv_f :
    (shortWeyl P a₀ * (shortWeyl P (-a))⁻¹) P.f = (Q a * (Q a₀)⁻¹) • P.f := by
  have ha' : -a ∈ P.perp := neg_mem ha
  have hd' : Q (-a) ≠ 0 := by rwa [QuadraticMap.map_neg]
  rw [shortWeyl_inv P ha' hd', LinearEquiv.mul_apply, shortWeyl_f P ha' hd', map_smul,
    shortWeyl_e P ha₀ hd₀, QuadraticMap.map_neg, smul_smul]
  congr 1
  ring

theorem shortWeyl_mul_inv_mem_exchTorus (hA : A ≤ P.perp) (ha₀A : a₀ ∈ A) (haA : a ∈ A) :
    shortWeyl P a₀ * (shortWeyl P (-a))⁻¹ ∈ exchTorus P A := by
  have ha' : -a ∈ P.perp := neg_mem ha
  have hd' : Q (-a) ≠ 0 := by rwa [QuadraticMap.map_neg]
  refine mem_exchTorus.2 ⟨mul_mem (shortWeyl_mem P a₀) (inv_mem (shortWeyl_mem P (-a))),
    map_span_singleton_of_apply_eq (mul_ne_zero (inv_ne_zero hd) hd₀)
      (shortWeyl_mul_inv_e P ha₀ hd₀ ha hd),
    map_span_singleton_of_apply_eq (mul_ne_zero hd (inv_ne_zero hd₀))
      (shortWeyl_mul_inv_f P ha₀ hd₀ ha hd), ?_⟩
  have h₀ : shortWeyl P a₀ ∈ MulAction.stabilizer (V ≃ₗ[K] V) A :=
    Submodule.mem_stabilizer_submodule_iff_map_eq.2 (map_shortWeyl_eq P ha₀ hd₀ hA ha₀A)
  have h₁ : shortWeyl P (-a) ∈ MulAction.stabilizer (V ≃ₗ[K] V) A :=
    Submodule.mem_stabilizer_submodule_iff_map_eq.2 (map_shortWeyl_eq P ha' hd' hA (neg_mem haA))
  exact Submodule.mem_stabilizer_submodule_iff_map_eq.1 (mul_mem h₀ (inv_mem h₁))

omit hd₀ hd ha₀ in
theorem shortWeyl_mul_eichler_eq :
    shortWeyl P a₀ * eichler Q P.e a = shortWeyl P a₀ * (shortWeyl P (-a))⁻¹ *
      eichler Q P.e (-a) * eichler Q P.f (-((Q a)⁻¹ • a)) := by
  rw [mul_assoc (shortWeyl P a₀ * (shortWeyl P (-a))⁻¹), ← shortWeyl_neg_mul_eichler P ha,
    mul_assoc, inv_mul_cancel_left]

end Torus


theorem orthogonal_geometry_tail_short_root_exchange {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (P : HypPair Q) {A : Submodule K V} (hA : A ≤ P.perp)
    (hani : ∀ a ∈ A, Q a = 0 → a = 0) {a₀ : V} (ha₀ : a₀ ∈ A) (ha₀0 : a₀ ≠ 0) :
    ∀ a ∈ A, a ≠ 0 →
      shortWeyl P a₀ * (shortWeyl P (-a))⁻¹ ∈ exchTorus P A ∧
      shortWeyl P a₀ * eichler Q P.e a = shortWeyl P a₀ * (shortWeyl P (-a))⁻¹ *
        eichler Q P.e (-a) * eichler Q P.f (-((Q a)⁻¹ • a)) ∧
      ∃ g ∈ Subgroup.closure ((exchTorus P A : Set (V ≃ₗ[K] V)) ∪ eichler Q P.e '' (A : Set V)),
        ∃ b ∈ A, shortWeyl P a₀ * eichler Q P.e a = g * eichler Q P.f b := by
  intro a haA ha0
  have hd₀ : Q a₀ ≠ 0 := fun h => ha₀0 (hani a₀ ha₀ h)
  have hd : Q a ≠ 0 := fun h => ha0 (hani a haA h)
  have hT := shortWeyl_mul_inv_mem_exchTorus P (hA ha₀) hd₀ (hA haA) hd hA ha₀ haA
  have heq := shortWeyl_mul_eichler_eq (a₀ := a₀) P (hA haA)
  refine ⟨hT, heq, _, mul_mem (Subgroup.subset_closure (Or.inl hT))
    (Subgroup.subset_closure (Or.inr ⟨-a, neg_mem haA, rfl⟩)), _,
    neg_mem (Submodule.smul_mem _ _ haA), heq⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
