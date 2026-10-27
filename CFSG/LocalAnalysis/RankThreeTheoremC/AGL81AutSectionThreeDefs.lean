module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

@[expose] def ThreeAutFour (K : Type*) [Group K] : Prop :=
  ∀ E : Subgroup K, IsPGroup 3 E → ∀ g ∈ Subgroup.normalizer (E : Set K),
    ∃ k : ℕ, ∀ x ∈ E, g ^ (4 * 3 ^ k) * x = x * g ^ (4 * 3 ^ k)

@[expose] def SevenCentralizesTwo (K : Type*) [Group K] : Prop :=
  ∀ E : Subgroup K, IsPGroup 2 E → ∀ g ∈ Subgroup.normalizer (E : Set K), g ^ 7 = 1 →
    ∀ x ∈ E, g * x = x * g

@[expose] def GLThreeAutFour (q : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W],
    Module.finrank (ZMod q) W ≤ 3 → ThreeAutFour (Module.End (ZMod q) W)ˣ

@[expose] def SevenCentralizesTwoGL (q : ℕ) : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W],
    Module.finrank (ZMod q) W ≤ 4 → ∀ R : Subgroup (Module.End (ZMod q) W)ˣ, IsPGroup 2 R →
    ∀ y : (Module.End (ZMod q) W)ˣ, (∃ k : ℕ, y ^ (7 ^ k) = 1) →
    y ∈ Subgroup.normalizer (R : Set (Module.End (ZMod q) W)ˣ) → ∀ x ∈ R, y * x = x * y

variable {H K : Type*} [Group H] [Group K]

theorem map_mem_normalizer_map (f : H →* K) {E : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.normalizer (E : Set H)) :
    f g ∈ Subgroup.normalizer ((E.map f : Subgroup K) : Set K) :=
  Subgroup.le_normalizer_map f ⟨g, hg, rfl⟩

theorem ThreeAutFour.of_injective (f : H →* K) (hf : Function.Injective f)
    (hK : ThreeAutFour K) : ThreeAutFour H := by
  intro E hE g hg
  obtain ⟨k, hk⟩ := hK (E.map f) (hE.map f) (f g) (map_mem_normalizer_map f hg)
  refine ⟨k, fun x hx => hf ?_⟩
  simpa only [map_mul, map_pow] using hk (f x) ⟨x, hx, rfl⟩

theorem SevenCentralizesTwo.of_injective (f : H →* K) (hf : Function.Injective f)
    (hK : SevenCentralizesTwo K) : SevenCentralizesTwo H := by
  intro E hE g hg hg7 x hx
  refine hf ?_
  simpa only [map_mul] using hK (E.map f) (hE.map f) (f g) (map_mem_normalizer_map f hg)
    (by rw [← map_pow, hg7, map_one]) (f x) ⟨x, hx, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
