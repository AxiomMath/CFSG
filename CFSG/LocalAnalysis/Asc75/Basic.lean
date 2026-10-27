module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {X : Subgroup G} {g x : G} :
    x ∈ conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ X
    rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem conjugate_mul (X : Subgroup G) (a b : G) :
    conjugate X (a * b) = conjugate (conjugate X a) b := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]

theorem conjugate_one (X : Subgroup G) : conjugate X 1 = X := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem conjugate_of_mem_normalizer {X : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (X : Set G)) : conjugate X a = X := by
  ext x
  rw [mem_conjugate_iff]
  exact ((Subgroup.mem_normalizer_iff.1 ha x).symm)

theorem conj_mem_conjugate {X : Subgroup G} {x : G} (hx : x ∈ X) (g : G) :
    g⁻¹ * x * g ∈ conjugate X g := by
  rw [mem_conjugate_iff]
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

theorem mem_normalizer_of_conjugate_eq {X : Subgroup G} {a : G} (h : conjugate X a = X) :
    a ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have := (congrArg (fun Y : Subgroup G => x ∈ Y) h)
  simp only [mem_conjugate_iff, eq_iff_iff] at this
  simpa only [SetLike.mem_coe] using this.symm

theorem conjugate_eq_iff_mem_normalizer {X : Subgroup G} {a : G} :
    conjugate X a = X ↔ a ∈ Subgroup.normalizer (X : Set G) :=
  ⟨mem_normalizer_of_conjugate_eq, conjugate_of_mem_normalizer⟩

theorem conjugate_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) : conjugate X g ≤ conjugate Y g :=
  fun _ hx => mem_conjugate_iff.2 (h (mem_conjugate_iff.1 hx))

theorem conjugate_inf (X Y : Subgroup G) (g : G) :
    conjugate (X ⊓ Y) g = conjugate X g ⊓ conjugate Y g := by
  ext x
  simp only [Subgroup.mem_inf, mem_conjugate_iff]

theorem conjugate_inv_conjugate (X : Subgroup G) (g : G) : conjugate (conjugate X g) g⁻¹ = X := by
  rw [← conjugate_mul, mul_inv_cancel, conjugate_one]

theorem card_conjugate [Finite G] (X : Subgroup G) (g : G) :
    Nat.card (conjugate X g) = Nat.card X := by
  unfold conjugate
  exact (Nat.card_congr (Subgroup.equivMapOfInjective X (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

end CFSG.Asc75
