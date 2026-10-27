module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup CFSG.ABGLocalTools

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

theorem isSylowOf_map [Finite G] [Finite H] [Fact p.Prime] (f : G →* H) {P S : Subgroup G}
    (h : IsSylowOf p P S) : IsSylowOf p (P.map f) (S.map f) := by
  obtain ⟨Q, rfl⟩ := h
  set f' : S →* S.map f := (f.comp S.subtype).codRestrict (S.map f) fun s => ⟨s, s.2, rfl⟩
  have hf' : Function.Surjective f' := by
    rintro ⟨_, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  refine ⟨Q.mapSurjective hf', ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem exists_isSylowOf_ge [Finite G] [Fact p.Prime] {Q R : Subgroup G} (hQ : IsPGroup p Q)
    (hQR : Q ≤ R) : ∃ T : Subgroup G, IsSylowOf p T R ∧ Q ≤ T := by
  have hQ' : IsPGroup p (Q.subgroupOf R) := hQ.comap_subtype
  obtain ⟨T', hT'⟩ := hQ'.exists_le_sylow
  refine ⟨(T' : Subgroup R).map R.subtype, ⟨T', rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQR hq⟩, hT' (show (⟨q, hQR hq⟩ : R) ∈ Q.subgroupOf R from hq), rfl⟩

theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ y ∈ K, x * y * x⁻¹ ∈ K) : x ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  set c : K → K := fun k => ⟨x * k * x⁻¹, h k k.2⟩
  have hc : Function.Injective c := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [c, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hc ⟨_, hy⟩
  have := congrArg Subtype.val hk
  simp only [c, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact k.2

theorem mem_normalizer_sup_zpowers [Finite G] {A : Subgroup G} {t x : G}
    (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A ⊔ zpowers t) (ht : x * t * x⁻¹ ∈ A ⊔ zpowers t) :
    x ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have hle : A ⊔ zpowers t ≤ (A ⊔ zpowers t).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (zpowers_le.mpr ht)
  exact hle hy

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
