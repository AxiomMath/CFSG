module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Defs

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_27Concl {G : Type*} [Group G] (T H S L : Subgroup G) : Prop :=
  (S.relIndex T = 2 ∧ baum S = thompsonJ S ∧ thompsonJ S = thompsonJ T) ∧
  (∀ x ∈ T, x ∉ S → ∀ r ∈ S, r ∉ baum S →
    ∃ A₁ : Subgroup G, (A₁ ⊓ pCoreOf 2 H).relIndex A₁ = 2 ∧
      ∀ B : Subgroup G, IsMaxElemAbelian T B ↔
        B = pCoreOf 2 H ∨ B = conjR (pCoreOf 2 H) x ∨ B = A₁ ∨ B = conjR A₁ r) ∧
  (IsElemAbelian 2 (blockTC T S L) ∧ pCoreOf 2 H = blockTC T S L ⊔ blockU0 S L ∧
    blockTC T S L ⊓ blockU0 S L = ⊥ ∧
    ∀ x ∈ T, x ∉ S → blockTC T S L ⊓ conjR (blockTC T S L) x = ⊥) ∧
  (∀ x ∈ T, x ∉ S →
    baum S = blockTC T S L ⊔ (blockU0 S L ⊔ conjR (blockU0 S L) x) ∧
    blockTC T S L ⊓ (blockU0 S L ⊔ conjR (blockU0 S L) x) = ⊥ ∧
    (∀ t ∈ blockTC T S L, ∀ y ∈ blockU0 S L ⊔ conjR (blockU0 S L) x, t * y = y * t) ∧
    ⁅conjJoin S L, conjR (blockU0 S L) x⁆ = conjJoin S L)

@[expose] def Lemma2_4_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) →
    Lemma2_4_27Concl T H S L

@[expose] def Lemma2_4_27_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ((IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L)) →
    S.relIndex T = 2 ∧ baum S = thompsonJ S ∧ thompsonJ S = thompsonJ T

@[expose] def Lemma2_4_27_1A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L ≠ L →
    S.relIndex T = 2 ∧ baum S = thompsonJ S ∧ thompsonJ S = thompsonJ T

@[expose] def Lemma2_4_27_1A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L →
    S.relIndex T = 2 ∧ baum S = thompsonJ S ∧ thompsonJ S = thompsonJ T

theorem Lemma2_4_27_1.toA3 (h : Lemma2_4_27_1) : Lemma2_4_27_1A3 :=
  fun G _ _ T M H S L hcs h3 hne => h G T M H S L hcs (Or.inr ⟨h3, hne⟩)

theorem Lemma2_4_27_1.toA5 (h : Lemma2_4_27_1) : Lemma2_4_27_1A5 :=
  fun G _ _ T M H S L hcs h5 hj => h G T M H S L hcs (Or.inl ⟨h5, hj⟩)

theorem lemma2_4_27_1_of_cases (h5 : Lemma2_4_27_1A5) (h3 : Lemma2_4_27_1A3) : Lemma2_4_27_1 := by
  intro G _ _ T M H S L hcs hcase
  rcases hcase with ⟨h5', hj⟩ | ⟨h3', hne⟩
  · exact h5 G T M H S L hcs h5' hj
  · exact h3 G T M H S L hcs h3' hne

@[expose] def Lemma2_4_27A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 5 → conjJoin S L = L → Lemma2_4_27Concl T H S L

@[expose] def Lemma2_4_27A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    IsAltType L 3 → conjJoin S L ≠ L → Lemma2_4_27Concl T H S L

theorem lemma2_4_27_of_cases (h5 : Lemma2_4_27A5) (h3 : Lemma2_4_27A3) : Lemma2_4_27 := by
  intro G _ _ T M H S L hcs hcase
  rcases hcase with ⟨h5', hj⟩ | ⟨h3', hne⟩
  · exact h5 G T M H S L hcs h5' hj
  · exact h3 G T M H S L hcs h3' hne

end CFSG.QuasithinUnique.DoubleA3
