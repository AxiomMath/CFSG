module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup

section Index2

variable {G : Type*} [Group G] {H K : Subgroup G}

theorem ovg_exists_mem_notMem (h2 : (K.subgroupOf H).index = 2) : ∃ a ∈ H, a ∉ K := by
  by_contra hcon
  push Not at hcon
  have htop : K.subgroupOf H = ⊤ := by
    ext x
    simp only [mem_subgroupOf, mem_top, iff_true]
    exact hcon x x.2
  rw [htop, index_top] at h2
  exact absurd h2 (by norm_num)

theorem ovg_inv_mul_mem (h2 : (K.subgroupOf H).index = 2) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (haK : a ∉ K) (hbK : b ∉ K) : a⁻¹ * b ∈ K := by
  have hiff : (⟨a⁻¹, H.inv_mem ha⟩ : H) ∈ K.subgroupOf H ↔ (⟨b, hb⟩ : H) ∈ K.subgroupOf H :=
    iff_of_false (fun h => haK (by simpa using K.inv_mem (mem_subgroupOf.1 h))) hbK
  exact mem_subgroupOf.1
    ((mul_mem_iff_of_index_two (a := ⟨a⁻¹, H.inv_mem ha⟩) (b := ⟨b, hb⟩) h2).2 hiff)

theorem ovg_mul_self_mem (h2 : (K.subgroupOf H).index = 2) {a : G} (ha : a ∈ H) :
    a * a ∈ K :=
  mul_self_mem_of_index_two h2 ⟨a, ha⟩

theorem ovg_conj_mem (hKH : K ≤ H) (h2 : (K.subgroupOf H).index = 2) {k a : G}
    (hk : k ∈ K) (ha : a ∈ H) : a * k * a⁻¹ ∈ K := by
  have := normal_of_index_eq_two h2
  exact this.conj_mem ⟨k, hKH hk⟩ (mem_subgroupOf.2 hk) ⟨a, ha⟩

theorem card_invariant_subset_of_index_two [Finite G] (hKH : K ≤ H)
    (h2 : (K.subgroupOf H).index = 2) {S T : Set G} (hSinv : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S)
    (hStrans : ∀ s ∈ S, ∀ s' ∈ S, ∃ h ∈ H, h * s * h⁻¹ = s') (hTS : T ⊆ S)
    (hTK : ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T) (hne : T.Nonempty) :
    T = S ∨ 2 * T.ncard = S.ncard := by
  obtain ⟨h₀, hh₀H, hh₀K⟩ := ovg_exists_mem_notMem h2
  have hh₀inv : h₀⁻¹ ∈ H := H.inv_mem hh₀H
  have hsq : h₀ * h₀ ∈ K := ovg_mul_self_mem h2 hh₀H
  have C1 : ∀ h ∈ H, h ∈ K ∨ h₀⁻¹ * h ∈ K := fun h hh => by
    by_cases hK : h ∈ K
    · exact Or.inl hK
    · exact Or.inr (ovg_inv_mul_mem h2 hh₀H hh hh₀K hK)
  set σ : G → G := fun t => h₀ * t * h₀⁻¹ with hσ
  have hσinj : Function.Injective σ := fun a b hab => by
    simpa [hσ] using hab
  have C2 : ∀ t ∈ T, σ t ∈ S := fun t ht => hSinv h₀ hh₀H t (hTS ht)
  have C3 : ∀ k ∈ K, ∀ t ∈ T, ∃ t' ∈ T, k * σ t * k⁻¹ = σ t' := fun k hk t ht => by
    refine ⟨(h₀⁻¹ * k * h₀) * t * (h₀⁻¹ * k * h₀)⁻¹, hTK _ ?_ t ht, ?_⟩
    · simpa using ovg_conj_mem hKH h2 hk hh₀inv
    · simp only [hσ]
      group
  have C4 : ∀ t ∈ T, σ (σ t) ∈ T := fun t ht => by
    have h := hTK (h₀ * h₀) hsq t ht
    convert h using 1
    simp only [hσ]
    group
  obtain ⟨t₀, ht₀⟩ := hne
  have C6 : ∀ s ∈ S, s ∈ T ∨ s ∈ σ '' T := fun s hs => by
    obtain ⟨h, hhH, hh⟩ := hStrans t₀ (hTS ht₀) s hs
    rcases C1 h hhH with hK | hK
    · left
      rw [← hh]
      exact hTK h hK t₀ ht₀
    · right
      refine ⟨(h₀⁻¹ * h) * t₀ * (h₀⁻¹ * h)⁻¹, hTK _ hK t₀ ht₀, ?_⟩
      rw [← hh]
      simp only [hσ]
      group
  by_cases hinter : ∃ c, c ∈ T ∧ c ∈ σ '' T
  · left
    obtain ⟨c, hcT, c₁, hc₁T, hc₁⟩ := hinter
    refine Set.Subset.antisymm hTS (fun s hs => ?_)
    obtain ⟨h, hhH, hh⟩ := hStrans c (hTS hcT) s hs
    rcases C1 h hhH with hK | hK
    · rw [← hh]
      exact hTK h hK c hcT
    · obtain ⟨t'', ht'', hct''⟩ := C3 (h₀⁻¹ * h) hK c₁ hc₁T
      have hs' : s = σ (σ t'') := by
        rw [← hct'', show σ c₁ = c from hc₁, ← hh]
        simp only [hσ]
        group
      rw [hs']
      exact C4 t'' ht''
  · right
    push Not at hinter
    have hdisj : Disjoint T (σ '' T) := Set.disjoint_left.2 hinter
    have hSeq : S = T ∪ σ '' T :=
      Set.Subset.antisymm (fun s hs => C6 s hs)
        (Set.union_subset hTS (by rintro _ ⟨t, ht, rfl⟩; exact C2 t ht))
    rw [hSeq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ hσinj]
    ring

end Index2

end CFSG.EvenSporadicStandard.Induction.Hyp
