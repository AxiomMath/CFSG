module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.FooteLit.L24V

open CFSG Subgroup CFSG.ABGLocalTools

variable {A : Type*} [Group A]

theorem le_of_isSylowOf_centralizer {p : ℕ} [Fact p.Prime] [Finite A] {V P : Subgroup A}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVp : IsPGroup p V)
    (hP : IsSylowOf p P (centralizer (V : Set A))) : V ≤ P := by
  obtain ⟨Q, rfl⟩ := hP
  have hVC : V ≤ centralizer (V : Set A) := fun v hv =>
    mem_centralizer_iff.mpr fun w hw => hVc w hw v hv
  have hV'n : (V.comap (centralizer (V : Set A)).subtype).Normal := ⟨fun n hn g => by
    have h1 : (g : A) * n = n * g := (mem_centralizer_iff.mp g.2 n hn).symm
    show ((g : A) * n * (g : A)⁻¹) ∈ V
    rw [h1, mul_inv_cancel_right]
    exact hn⟩
  have hle := (hVp.comap_of_injective _
    (centralizer (V : Set A)).subtype_injective).le_sylow_of_normal Q
  intro v hv
  exact ⟨⟨v, hVC hv⟩, hle hv, rfl⟩

theorem le_and_isPGroup_of_isSylowOf {p : ℕ} {P K : Subgroup A} (hP : IsSylowOf p P K) :
    P ≤ K ∧ IsPGroup p P := by
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨map_subtype_le _, Q.isPGroup'.map _⟩

theorem exists_eq_zpowers_sup {C : Type*} [Group C] [IsCyclic C] (χ : A →* C)
    {V P : Subgroup A} (hVP : V ≤ P) (hker : ∀ x ∈ P, χ x = 1 → x ∈ V) :
    ∃ f ∈ P, P = zpowers f ⊔ V := by
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := P.map χ)
  obtain ⟨f, hfP, hfy⟩ := y.2
  refine ⟨f, hfP, le_antisymm ?_ (sup_le (zpowers_le.mpr hfP) hVP)⟩
  intro x hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hy ⟨χ x, x, hx, rfl⟩)
  have h1 : χ (f ^ k) = χ x := by
    have h2 := congrArg Subtype.val hk
    rw [SubgroupClass.coe_zpow, ← hfy, ← map_zpow] at h2
    exact h2
  have h3 : (f ^ k)⁻¹ * x ∈ V := hker _ (P.mul_mem (P.inv_mem (P.zpow_mem hfP k)) hx) (by
    rw [map_mul, map_inv, h1, inv_mul_cancel])
  rw [show x = f ^ k * ((f ^ k)⁻¹ * x) by group]
  exact mul_mem (le_sup_left (a := zpowers f) (zpow_mem_zpowers f k)) (le_sup_right (b := V) h3)

end CFSG.ComponentClassification.FooteLit.L24V
