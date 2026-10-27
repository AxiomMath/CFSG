module

public import CFSG.LieType.Simplicity.Classical
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

@[expose] def L4U4Form (X : Type) [Group X] (p f : ℕ) : Prop :=
  (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = p ^ f ∧
      Nonempty (X ≃* StatedProj (StatedSL 4 F))) ∨
    (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
      Nonempty (X ≃* StatedProj (StatedSU 4 (p ^ f) F)))

theorem L4U4Form.of_mulEquiv {X X' : Type} [Group X] [Group X'] {p f : ℕ} (e : X' ≃* X)
    (h : L4U4Form X p f) : L4U4Form X' p f := by
  rcases h with ⟨hq, F, hF, hFt, hc, ⟨e'⟩⟩ | ⟨hq, F, hF, hu, ⟨e'⟩⟩
  · exact Or.inl ⟨hq, F, hF, hFt, hc, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨hq, F, hF, hu, ⟨e.trans e'⟩⟩

theorem L4U4Form.lieModel {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : L4U4Form X p f) :
    (p ^ f % 4 = 3 ∧ Blueprint.LieModel X .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ Blueprint.LieModel X .PSU 4 p f) := by
  rcases h with ⟨hq, F, _, _, hc, ⟨e⟩⟩ | ⟨hq, F, _, hu, ⟨e⟩⟩
  · refine Or.inl ⟨hq, Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp, by simp⟩, F,
      inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hc], ⟨e⟩⟩⟩
  · refine Or.inr ⟨hq, Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp⟩, F, inferInstance,
      hu.finite, by rw [hu.card, ← pow_mul, mul_comm], ⟨e⟩⟩⟩

theorem isSimpleGroup_of_lieModel_psl {X : Type} [Group X] {n p e : ℕ} (hn : n ≠ 0)
    (h : Blueprint.LieModel X .PSL n p e) : IsSimpleGroup X := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact (LieType.Simplicity.fam_PSL_simplicity X n p e h).2
  all_goals exact absurd h0 hn

theorem L4U4Form.isSimpleGroup {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : L4U4Form X p f) : IsSimpleGroup X := by
  rcases h.lieModel hp hf with ⟨-, h⟩ | ⟨-, h⟩
  · exact isSimpleGroup_of_lieModel_psl (by norm_num) h
  · rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact (ClassicalGroups.Unitary.fam_PSU_simplicity X 4 p f h).2
    all_goals exact absurd h0 (by norm_num)

end CFSG.ComponentClassification.GSThmB.Pump516
