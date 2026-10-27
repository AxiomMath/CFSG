module

public import CFSG.Open.Catalog
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG

variable {G : Type} [Group G]

@[expose] def zIn (P : Subgroup G) : Subgroup G := P ⊓ centralizer (P : Set G)

theorem zIn_le (P : Subgroup G) : zIn P ≤ P := inf_le_left

theorem mem_normalizer_of_conj_le {K : Subgroup G} {g : G}
    (h1 : ∀ x ∈ K, g * x * g⁻¹ ∈ K) (h2 : ∀ x ∈ K, g⁻¹ * x * g ∈ K) :
    g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h1 x
  · intro hx
    have := h2 _ hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_zIn (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (zIn P : Set G) := by
  intro g hg
  have key : ∀ g ∈ normalizer (P : Set G), ∀ x ∈ zIn P, g * x * g⁻¹ ∈ zIn P := by
    intro g hg x hx
    refine ⟨(mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    show g * x * g⁻¹ ∈ centralizer (P : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : g⁻¹ * y * g ∈ P := by
      have := (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
      simpa [mul_assoc] using this
    have hc := mem_centralizer_iff.mp hx.2 _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * y := by group
  exact mem_normalizer_of_conj_le (key g hg) (fun x hx => by
    simpa using key g⁻¹ (inv_mem hg) x hx)

@[expose, reducible] def IsMaxAbelianIn (P A : Subgroup G) : Prop :=
  A ∈ CFSG.ambientMaxCardAbelianFamily P

theorem thompson_eq_iSup (P : Subgroup G) :
    Open.thompsonSubgroup P = ⨆ (A : Subgroup G) (_ : IsMaxAbelianIn P A), A :=
  sSup_eq_iSup

theorem thompson_le (P : Subgroup G) : Open.thompsonSubgroup P ≤ P :=
  Open.thompsonSubgroup_le_self P

theorem le_thompson {P A : Subgroup G} (h : IsMaxAbelianIn P A) : A ≤ Open.thompsonSubgroup P := by
  rw [thompson_eq_iSup]
  exact le_iSup_of_le A (le_iSup_of_le h le_rfl)

theorem normalizer_le_normalizer_thompson (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (Open.thompsonSubgroup P : Set G) :=
  Open.normalizer_le_normalizer_thompsonSubgroup P

theorem exists_isMaxAbelianIn [Finite G] (P : Subgroup G) : ∃ A, IsMaxAbelianIn P A := by
  obtain ⟨A, ⟨hAP, hAc⟩, hmax⟩ := Set.exists_max_image
    {A : Subgroup G | A ≤ P ∧ IsMulCommutative A} (fun A => Nat.card A) (Set.toFinite _)
    ⟨⊥, bot_le, ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩⟩
  exact ⟨A, hAP, hAc, fun B hBP hBc => hmax B ⟨hBP, hBc⟩⟩

theorem thompson_eq_of_forall_le [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (h : ∀ A, IsMaxAbelianIn P A → A ≤ Q) :
    Open.thompsonSubgroup P = Open.thompsonSubgroup Q := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxAbelianIn P
  have hiff : ∀ A, IsMaxAbelianIn P A ↔ IsMaxAbelianIn Q A := by
    intro A
    constructor
    · intro hA
      exact ⟨h A hA, hA.2.1, fun B hBQ hBc => hA.2.2 B (hBQ.trans hQP) hBc⟩
    · intro hA
      refine ⟨hA.1.trans hQP, hA.2.1, fun B hBP hBc => ?_⟩
      exact (hA₀.2.2 B hBP hBc).trans (hA.2.2 A₀ (h A₀ hA₀) hA₀.2.1)
  rw [thompson_eq_iSup, thompson_eq_iSup]
  exact le_antisymm (iSup_le fun A => iSup_le fun hA => le_iSup_of_le A
      (le_iSup_of_le ((hiff A).mp hA) le_rfl))
    (iSup_le fun A => iSup_le fun hA => le_iSup_of_le A (le_iSup_of_le ((hiff A).mpr hA) le_rfl))

end CFSG.OddStandard.GH71
