module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Direct

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

structure Rank2NoDelta5Parts : Prop where
  l3 : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (f : ℕ), 1 ≤ f →
    (IsPSL 3 2 f ↥L ∨ IsSL3 (2 ^ f) ↥L) → IsMaxParabolic2 L P →
      ¬ IsDelta5Group ↥(perfectCore P)
  sp4 : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (f : ℕ), 2 ≤ f →
    IsPSp4 2 f ↥L → IsMaxParabolic2 L P → ¬ IsDelta5Group ↥(perfectCore P)
  g2 : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (f : ℕ), 2 ≤ f →
    IsG2 2 f ↥L → IsMaxParabolic2 L P → ¬ IsDelta5Group ↥(perfectCore P)
  d4 : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (f : ℕ), 1 ≤ f →
    Is3D4 2 f ↥L → IsMaxParabolic2 L P → ¬ IsDelta5Group ↥(perfectCore P)
  f4 : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (f : ℕ), Odd f → 3 ≤ f →
    Is2F4 f ↥L → IsMaxParabolic2 L P → ¬ IsDelta5Group ↥(perfectCore P)
  tits : ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsTits ↥L →
    IsMaxParabolic2 L P → ¬ IsDelta5Group ↥(perfectCore P)

theorem rank2NoDelta5_of_parts (h : Rank2NoDelta5Parts) : Rank2NoDelta5 := by
  intro G _ _ L P hrk hP
  rcases hrk with ⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hodd, hf, hm⟩⟩ | hT
  · exact h.l3 G L P f hf (Or.inl hm) hP
  · exact h.l3 G L P f hf (Or.inr hm) hP
  · exact h.sp4 G L P f hf hm hP
  · exact h.g2 G L P f hf hm hP
  · exact h.d4 G L P f hf hm hP
  · exact h.f4 G L P f hodd hf hm hP
  · exact h.tits G L P hT hP

end CFSG.QuasithinUnique.A5.G3
