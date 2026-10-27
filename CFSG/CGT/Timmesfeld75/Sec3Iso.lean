module

public import CFSG.CGT.Timmesfeld75.Sec3Fpf

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def Sec3Iso (T T₁ : Subgroup G) : Prop :=
  ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal, ∃ f : ℕ, f ≠ 0 ∧
    Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 f))

@[expose] def Sec3IsoGlobal (T : Subgroup G) : Prop :=
  ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
    Sec3Iso T (conjSubgroup g T)

@[expose] def Section3IsoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, Sec3 T T₁ → Sec3Iso T T₁

theorem Sec3IsoGlobal.of_input {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hI : Section3IsoInput) (hnab : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G}
    (hS : ∀ g : G, conjSubgroup g T ≠ T → normIn T (conjSubgroup g T) ≠ ⊥ →
      Sec3 T (conjSubgroup g T)) : Sec3IsoGlobal T :=
  fun g hne hL => hI G hnab T (conjSubgroup g T) (hS g hne hL)

theorem Sec3.exists_isL2Pair {G : Type} [Group G] {T T₁ : Subgroup G} [Finite G]
    (hS : Sec3 T T₁) (h : Sec3Iso T T₁) :
    ∃ (_ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal) (f : ℕ), f ≠ 0 ∧
      IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
        ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))))
        (2 ^ f) := by
  obtain ⟨hN, f, hf, hiso⟩ := h
  exact ⟨hN, f, hf, hS.isL2Pair_quotient hf hiso⟩

end CFSG.CGT.Timmesfeld75
