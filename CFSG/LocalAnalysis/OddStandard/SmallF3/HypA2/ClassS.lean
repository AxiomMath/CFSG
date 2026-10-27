module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Open

@[expose] def classSBound : ℕ := 141214764960

@[expose] def InSA (S : Type) [Group S] : Prop :=
  Catalog S ∧ 20160 ≤ Nat.card S ∧
    (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ HarrisLit.IsSimpleChevalleyOver r S) ∧
    ¬ LieModel S .PSL 3 2 2 ∧ ¬ NativeSporadic.IsSporadic S .He ∧
    ¬ NativeSporadic.IsSporadic S .M12 ∧ ¬ NativeSporadic.IsSporadic S .J2

@[expose] def InSB (S : Type) [Group S] : Prop :=
  HarrisLit.IsSimpleChevalleyOver 3 S ∧ classSBound ≤ Nat.card S ∧
    (∃ (j : ℕ) (τ : StatedLieTag) (n : ℕ), LieModel S τ n 3 (2 ^ j)) ∧
    (∀ e : ℕ, LieModel S .PSL 2 3 e → ∃ j : ℕ, e = 2 ^ j) ∧
    ¬ LieModel S .POmegaPlus 4 3 1 ∧ ¬ LieModel S .POmegaMinus 4 3 1

@[expose] def InS (S : Type) [Group S] : Prop := InSA S ∨ InSB S

private theorem isSimpleChevalleyOver_of_mulEquiv {A B : Type} [Group A] [Group B] (r : ℕ)
    (e : A ≃* B) (h : HarrisLit.IsSimpleChevalleyOver r A) :
    HarrisLit.IsSimpleChevalleyOver r B := by
  obtain ⟨τ, n, f, hτ⟩ := h
  exact ⟨τ, n, f, LieModel.of_mulEquiv e hτ⟩

private theorem inSA_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : InSA A) :
    InSA B := by
  unfold InSA at h ⊢
  rcases h with ⟨hcat, hcard, hchev, hpsl, hHe, hM12, hJ2⟩
  refine ⟨(CFSG.SectionRank.catalog_congr e).mp hcat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hcard
  · intro r hr hr2 hch
    exact hchev r hr hr2 (isSimpleChevalleyOver_of_mulEquiv r e.symm hch)
  · intro h
    exact hpsl (LieModel.of_mulEquiv e.symm h)
  · rintro ⟨e'⟩
    exact hHe ⟨e.trans e'⟩
  · rintro ⟨e'⟩
    exact hM12 ⟨e.trans e'⟩
  · rintro ⟨e'⟩
    exact hJ2 ⟨e.trans e'⟩

private theorem inSB_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : InSB A) :
    InSB B := by
  unfold InSB at h ⊢
  rcases h with ⟨hchev, hcard, ⟨j, τ, n, hτ⟩, hpsl2, hpom, hhom⟩
  refine ⟨isSimpleChevalleyOver_of_mulEquiv 3 e hchev, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hcard
  · exact ⟨j, τ, n, LieModel.of_mulEquiv e hτ⟩
  · intro f hf
    exact hpsl2 f (LieModel.of_mulEquiv e.symm hf)
  · intro h
    exact hpom (LieModel.of_mulEquiv e.symm h)
  · intro h
    exact hhom (LieModel.of_mulEquiv e.symm h)

theorem inSA_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) : InSA A ↔ InSA B :=
  ⟨inSA_of_mulEquiv e, inSA_of_mulEquiv e.symm⟩

theorem inSB_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) : InSB A ↔ InSB B :=
  ⟨inSB_of_mulEquiv e, inSB_of_mulEquiv e.symm⟩

theorem inS_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) : InS A ↔ InS B := by
  unfold InS
  exact ⟨fun h => h.elim (Or.inl ∘ (inSA_congr e).mp) (Or.inr ∘ (inSB_congr e).mp),
    fun h => h.elim (Or.inl ∘ (inSA_congr e).mpr) (Or.inr ∘ (inSB_congr e).mpr)⟩

theorem twentyThousand_le_card_of_inS {S : Type} [Group S] (h : InS S) : 20160 ≤ Nat.card S := by
  rcases h with h | h
  · exact h.2.1
  · exact le_trans (by norm_num [classSBound]) h.2.1

end CFSG.OddStandard.SmallF3.HypA2
