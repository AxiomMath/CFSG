module

public import CFSG.LargeExtraspecial.S12TriQ
public import CFSG.LargeExtraspecial.S12Good

public section

namespace CFSG.LargeExtraspecial

open Subgroup

@[expose] def FischerTrialityInput : Prop :=
  ∀ (X : Type) [Group X] (E : Set X), CFSG.Blueprint.Fischer.Pair X E →
    center X = ⊥ → (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) →
    (∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) →
    (∃ d ∈ E, ∃ e ∈ E, d * e ∉ fischerQ E) → ∀ d ∈ E,
      ¬ Group.IsSolvable (fischerQ E ⊓ centralizer {d} : Subgroup X) ∧
        S12NoNormalTwo (fischerQ E ⊓ centralizer {d})

theorem S12NoNormalTwo.map_subtype {Y : Type*} [Group Y] {H : Subgroup Y} {A : Subgroup H}
    (hA : S12NoNormalTwo A) : S12NoNormalTwo (A.map H.subtype) := by
  intro P hPA hP hAP
  have hPH : P ≤ H := hPA.trans (map_subtype_le A)
  have hP'A : P.comap H.subtype ≤ A := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hPA (mem_comap.mp hx)
    rwa [← Subtype.ext hax]
  have hAP' : A ≤ normalizer (P.comap H.subtype : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro x
    simpa only [SetLike.mem_coe, mem_comap, coe_subtype, coe_mul, coe_inv] using
      mem_normalizer_iff.mp (hAP ⟨a, ha, rfl⟩) x
  have hbot := hA _ hP'A hP.comap_subtype hAP'
  rw [eq_bot_iff]
  intro y hy
  have hy' : (⟨y, hPH hy⟩ : H) ∈ P.comap H.subtype := hy
  rw [hbot, mem_bot] at hy'
  rw [mem_bot]
  exact congrArg Subtype.val hy'

theorem map_subtype_fischerQ_inf_centralizer {Y : Type*} [Group Y] {H : Subgroup Y} {E : Set Y}
    (hE : E ⊆ H) (t : H) :
    (fischerQ (Subtype.val ⁻¹' E : Set H) ⊓ centralizer {t}).map H.subtype =
      fischerQ E ⊓ centralizer {(t : Y)} := by
  rw [← map_subtype_fischerQ hE]
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, coe_subtype]
  constructor
  · rintro ⟨x, ⟨hxQ, hxt⟩, rfl⟩
    exact ⟨⟨x, hxQ, rfl⟩, congrArg Subtype.val hxt⟩
  · rintro ⟨⟨x, hxQ, rfl⟩, hxt⟩
    exact ⟨x, ⟨hxQ, Subtype.ext hxt⟩, rfl⟩

end CFSG.LargeExtraspecial
