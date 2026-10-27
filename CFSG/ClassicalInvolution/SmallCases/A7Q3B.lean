module

public import CFSG.ClassicalInvolution.SmallCases.A7Q3

public section

namespace CFSG.ClassicalInvolution.A7Q.Vertex

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Balance (OddQuot oddQuotMk modOdd)

variable {G : Type} [Group G]

theorem isSubnormal_of_open {M K : Subgroup G} (h : IsSubnormal M K) (hK : K.IsSubnormal) :
    M.IsSubnormal :=
  h.mathlib hK

theorem isSubnormal_modOdd {c : G} {M : Subgroup G}
    (h : IsSubnormal M (Subgroup.centralizer ({c} : Set G))) : (modOdd c M).IsSubnormal := by
  have h1 := isSubnormal_subgroupOf h (Subgroup.centralizer ({c} : Set G))
  rw [Subgroup.subgroupOf_self] at h1
  exact (isSubnormal_of_open h1 Subgroup.IsSubnormal.top).map (QuotientGroup.mk'_surjective _)

theorem commute_modOdd {c : G} {M M' : Subgroup G}
    (h : ⁅M, M'⁆ ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G))) :
    ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x := by
  rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
  obtain ⟨o, ho, hoe⟩ := h (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hk)
    (Subgroup.mem_subgroupOf.mp hk'))
  have h2 : oddQuotMk c (k * k' * k⁻¹ * k'⁻¹) = 1 := by
    rw [show k * k' * k⁻¹ * k'⁻¹ = o from
      Subtype.ext ((commutatorElement_def (k : G) k').symm.trans hoe.symm)]
    exact (QuotientGroup.eq_one_iff _).mpr ho
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  calc oddQuotMk c k * oddQuotMk c k'
      = (oddQuotMk c k * oddQuotMk c k' * (oddQuotMk c k)⁻¹ * (oddQuotMk c k')⁻¹) *
          (oddQuotMk c k' * oddQuotMk c k) := by group
    _ = oddQuotMk c k' * oddQuotMk c k := by rw [h2, one_mul]

theorem commute_of_mem_sup {c : G} {M M' : Subgroup G}
    (hM : M ≤ Subgroup.centralizer ({c} : Set G)) (hM' : M' ≤ Subgroup.centralizer ({c} : Set G))
    {L : Subgroup (OddQuot c)} (h : ∀ x ∈ modOdd c M, ∀ y ∈ L, x * y = y * x)
    (h' : ∀ x ∈ modOdd c M', ∀ y ∈ L, x * y = y * x) {a : G} (ha : a ∈ M ⊔ M')
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) :
    ∀ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y = y * oddQuotMk c ⟨a, haC⟩ := by
  have hle : ∀ {N : Subgroup G} (hN : N ≤ Subgroup.centralizer ({c} : Set G)),
      (∀ x ∈ modOdd c N, ∀ y ∈ L, x * y = y * x) →
        N ≤ ((Subgroup.centralizer (L : Set (OddQuot c))).comap (oddQuotMk c)).map
          (Subgroup.centralizer ({c} : Set G)).subtype := fun {N} hN hc n hn =>
    ⟨⟨n, hN hn⟩, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hc _ ⟨⟨n, hN hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩ y hy).symm, rfl⟩
  obtain ⟨b, hb, hbe⟩ := sup_le (hle hM h) (hle hM' h') ha
  obtain rfl : b = ⟨a, haC⟩ := Subtype.ext hbe
  exact fun y hy => (Subgroup.mem_centralizer_iff.mp hb y hy).symm

variable [Finite G]

theorem hyp51At_of_triangle {c : G} (hc2 : c * c = 1) (hc1 : c ≠ 1) {B : Subgroup G}
    (hBc : B ≤ Subgroup.centralizer ({c} : Set G)) {M₁ M₂ M₃ : Subgroup G}
    (hs₁ : IsSubnormal M₁ (Subgroup.centralizer ({c} : Set G)))
    (hs₂ : IsSubnormal M₂ (Subgroup.centralizer ({c} : Set G)))
    (hs₃ : IsSubnormal M₃ (Subgroup.centralizer ({c} : Set G)))
    (h₁₂ : ⁅M₁, M₂⁆ ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)))
    (h₂₃ : ⁅M₂, M₃⁆ ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G)))
    (h₁₃ : ⁅M₁, M₃⁆ ≤ oddCoreOf (Subgroup.centralizer ({c} : Set G))) {a₁ a₂ a₃ : G}
    (ha₁ : a₁ ∈ M₁ ⊔ M₂) (ha₂ : a₂ ∈ M₂ ⊔ M₃) (ha₃ : a₃ ∈ M₁ ⊔ M₃) (hB₁ : a₁ ∈ B)
    (hB₂ : a₂ ∈ B) (hB₃ : a₃ ∈ B) (hsq₁ : a₁ * a₁ = 1) (hsq₂ : a₂ * a₂ = 1) (hsq₃ : a₃ * a₃ = 1)
    (hn₁ : a₁ ≠ 1) (hn₂ : a₂ ≠ 1) (hn₃ : a₃ ≠ 1) (hc₁ : a₁ ≠ c) (hc₂ : a₂ ≠ c) (hc₃ : a₃ ≠ c) :
    Hyp51At B c := by
  suffices hno : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ¬ MovedByAll B c L from
    ⟨fun L₁ _ h₁ _ m₁ _ => absurd m₁ (hno L₁ h₁), fun L hL hm => absurd hm (hno L hL)⟩
  intro L hL hmov
  have hle := fun {M : Subgroup G} (hs : IsSubnormal M (Subgroup.centralizer ({c} : Set G))) =>
    isSubnormal_le hs
  have hmv : ∀ {a : G} (hB : a ∈ B), a * a = 1 → a ≠ 1 → a ≠ c →
      ∃ y ∈ L, oddQuotMk c ⟨a, hBc hB⟩ * y ≠ y * oddQuotMk c ⟨a, hBc hB⟩ := fun hB hsq hn hc =>
    hmov _ ⟨_, hB, rfl⟩ (not_mem_modOdd_zpowers hc2 hc1 hsq hn hc (hBc hB))
  obtain ⟨y₁, hy₁, hne₁⟩ := hmv hB₁ hsq₁ hn₁ hc₁
  obtain ⟨y₂, hy₂, hne₂⟩ := hmv hB₂ hsq₂ hn₂ hc₂
  obtain ⟨y₃, hy₃, hne₃⟩ := hmv hB₃ hsq₃ hn₃ hc₃
  have hdich : ∀ {M : Subgroup G}, IsSubnormal M (Subgroup.centralizer ({c} : Set G)) →
      L ≤ modOdd c M ∨ ∀ x ∈ modOdd c M, ∀ y ∈ L, x * y = y * x := fun hs => by
    rcases LocalCores.component_subnormal_subgroup hL (isSubnormal_modOdd hs) with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx y hy =>
        Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hy) x hx
  have hin : ∀ {M M' : Subgroup G}, L ≤ modOdd c M →
      (∀ x ∈ modOdd c M', ∀ y ∈ modOdd c M, x * y = y * x) →
        ∀ x ∈ modOdd c M', ∀ y ∈ L, x * y = y * x := fun hLM hc x hx y hy => hc x hx y (hLM hy)
  have c₁₂ := commute_modOdd h₁₂
  have c₂₃ := commute_modOdd h₂₃
  have c₁₃ := commute_modOdd h₁₃
  have sym : ∀ {M M' : Subgroup G}, (∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x) →
      ∀ x ∈ modOdd c M', ∀ y ∈ modOdd c M, x * y = y * x := fun h x hx y hy => (h y hy x hx).symm
  rcases hdich hs₃ with h₃ | h₃
  · exact hne₁ (commute_of_mem_sup (hle hs₁) (hle hs₂) (hin h₃ c₁₃) (hin h₃ c₂₃) ha₁ _ y₁ hy₁)
  rcases hdich hs₁ with h₁ | h₁
  · exact hne₂ (commute_of_mem_sup (hle hs₂) (hle hs₃) (hin h₁ (sym c₁₂)) (hin h₁ (sym c₁₃)) ha₂
      _ y₂ hy₂)
  rcases hdich hs₂ with h₂ | h₂
  · exact hne₃ (commute_of_mem_sup (hle hs₁) (hle hs₃) (hin h₂ c₁₂) (hin h₂ (sym c₂₃)) ha₃
      _ y₃ hy₃)
  exact hne₁ (commute_of_mem_sup (hle hs₁) (hle hs₂) h₁ h₂ ha₁ _ y₁ hy₁)

end CFSG.ClassicalInvolution.A7Q.Vertex
