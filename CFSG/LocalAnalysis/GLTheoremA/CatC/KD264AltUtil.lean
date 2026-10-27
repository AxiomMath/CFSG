module

public import CFSG.Open.LocalVocabulary

public section

open Subgroup

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Util

theorem card_comap_eq_mul {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H)
    (Q : Subgroup H) (hQ : Q ≤ φ.range) :
    Nat.card (Q.comap φ) = Nat.card Q * Nat.card φ.ker := by
  set φ' : (Q.comap φ) →* H := φ.comp (Q.comap φ).subtype with hφ'
  have hrange : φ'.range = Q := by
    ext h
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hh
      obtain ⟨g, hg⟩ := hQ hh
      exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact hh⟩, by simpa [hφ'] using hg⟩
  have hker : Nat.card φ'.ker = Nat.card φ.ker := by
    have hmap : φ'.ker.map (Q.comap φ).subtype = φ.ker := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx1 : φ x = 1 := by simpa [hφ'] using hx
        exact hx1
      · intro hg
        have hgQ : φ g = 1 := hg
        refine ⟨⟨g, by rw [Subgroup.mem_comap, hgQ]; exact Q.one_mem⟩, ?_, rfl⟩
        simpa [hφ'] using hgQ
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hk := Subgroup.card_ker_mul_card_range φ'
  rw [hker, hrange] at hk
  rw [← hk, mul_comm]

theorem isElemAbelian_range_of_hom {p : ℕ} {G H : Type*} [Group G] [Group H]
    (hG : IsMulCommutative G) (hexp : ∀ g : G, g ^ p = 1) (φ : G →* H) :
    CFSG.Open.IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨g, hg⟩ := x.2
    obtain ⟨h, hh⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hg, ← hh, ← map_mul, ← map_mul, hG.is_comm.comm g h]
  · intro x hx
    obtain ⟨g, hg⟩ := hx
    rw [← hg, ← map_pow, hexp g, map_one]

theorem isElemAbelian_map_of_hom {p : ℕ} {G H : Type*} [Group G] [Group H] {S : Subgroup G}
    (hS : CFSG.Open.IsElemAbelian p S) (φ : G →* H) :
    CFSG.Open.IsElemAbelian p (S.map φ) := by
  have hcomm : ∀ u ∈ S.map φ, ∀ v ∈ S.map φ, u * v = v * u := by
    intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hv
    have hst : s * t = t * s := by
      have := hS.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
      exact congrArg Subtype.val this
    rw [← map_mul, ← map_mul, hst]
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hx
  rw [← hsx, ← map_pow, hS.2 s hs, map_one]

theorem support_mul_subset' {α : Type*} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    (σ * τ).support ⊆ σ.support ∪ τ.support := by
  intro x hx
  rw [Equiv.Perm.mem_support] at hx
  by_contra h
  simp only [Finset.mem_union, Equiv.Perm.mem_support, not_or, not_not] at h
  apply hx
  simp [Equiv.Perm.mul_apply, h.1, h.2]

theorem maps_into_of_fix_outside {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (S : Finset α) (hσ : ∀ t, t ∉ S → σ t = t) {t : α} (ht : t ∈ S) (hσt : σ t ≠ t) :
    σ t ∈ S := by
  by_contra h
  have h1 := hσ (σ t) h
  apply hσt
  exact σ.injective (by rw [h1])

end CFSG.LocalAnalysis.GLTheoremA.KD264Util
