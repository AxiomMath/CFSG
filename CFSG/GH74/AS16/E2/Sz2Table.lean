module

public import CFSG.GH74.AS16.E2.Sz2Pure
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.Cover
public import CFSG.GH74.KGroups.CoverSz8
import CFSG.Goldschmidt.Steps.G3MFSz8

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.KGroups
open CFSG.GH74.E2 (Shape2Sz8)

theorem twoSzTable_of_shape
    {K : Type} [Group K] [Finite K] (h : Shape2Sz8 K) (Q : Subgroup K)
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) : TwoSzTable K Q := by
  obtain ⟨hq, hZc, hS⟩ := h
  refine twoSzTable_of_data Q hQ hQi hZc ?_ ?_
  · intro T' hT' hT'i
    obtain ⟨h1, -, -, -⟩ := Sz8.bender hS T' hT' hT'i
    exact ⟨h1, Sz8.bender_card hS T' hT' hT'i⟩
  · intro T
    obtain ⟨hperf0, hsimple, -⟩ := hq
    have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
    have hquasi : CFSG.Open.IsQuasisimple K := ⟨hperf, hsimple⟩
    obtain ⟨eS⟩ := CoverSz8.equiv_sz_of_lieModel hS
    have hZ2 : ∀ z ∈ center K, z ^ 2 = 1 := by
      intro z hz
      have := pow_card_eq_one' (G := ↥(center K)) (x := ⟨z, hz⟩)
      rw [hZc] at this
      exact congrArg Subtype.val this
    have hel : CFSG.Open.IsElemAbelian 2 (center K) :=
      ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)⟩⟩, hZ2⟩
    exact CFSG.Goldschmidt.GMFSz8 K hquasi hel ⟨eS⟩ T

theorem out_inner_of_shape2Sz8
    {K : Type} [Group K] [Finite K] (h : Shape2Sz8 K) (φ : MulAut K)
    (n : ℕ) (hφ : φ ^ 2 ^ n = 1) : ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  obtain ⟨hq, -, hS⟩ := h
  have hperf : Group.IsPerfect K := hq.1
  have h1 : (inducedHom φ) ^ 2 ^ n = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨kb, hk⟩ := Sz8.out_inner hS (inducedHom φ) n h1
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
  refine ⟨k, ?_⟩
  have h2 : inducedHom φ = inducedHom (MulAut.conj k) := by
    ext y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hk]
    rfl
  have h3 := inducedHom_injective hperf h2
  intro x
  exact congrArg (fun f : MulAut K => f x) h3

end CFSG.GH74.AS16.E2
