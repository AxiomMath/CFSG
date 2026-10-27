module

public import CFSG.GH74.GLS.Stage2.Final.ModelOrders
public import CFSG.GH74.GLS.Stage2.Final.ClassicalClosed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Final.ModelArith

theorem lieModel_psp_unpack {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSp 2 p f) :
    1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) := by
  rcases h with ⟨-, hadm, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact ⟨hadm.2.1, K, iK, fK, hK, he⟩
  all_goals exact absurd h0 (by norm_num)

theorem lieModel_psl_unpack {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSL 4 p f) :
    1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (Gs ≃* StatedProj (StatedSL 4 F)) := by
  rcases h with ⟨-, hadm, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact ⟨hadm.2.1, K, iK, fK, hK, he⟩
  all_goals exact absurd h0 (by norm_num)

theorem lieModel_psu_unpack {Gs : Type} [Group Gs] {p f : ℕ} (h : LieModel Gs .PSU 4 p f) :
    1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ f) ^ 2 ∧
      Nonempty (Gs ≃* StatedProj (StatedSU 4 (p ^ f) F)) := by
  rcases h with ⟨-, hadm, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact ⟨hadm.2.1, K, iK, fK, hK, he⟩
  all_goals exact absurd h0 (by norm_num)

theorem modelsDisjoint : ModelsDisjoint := by
  intro Gs _ p f p' f' hp hp2 hp' hp'2 hS
  obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psp_unpack hS
  constructor
  · intro hL
    obtain ⟨hf', F', iF', fF', hF', ⟨e'⟩⟩ := lieModel_psl_unpack hL
    refine card_psp4_ne_card_psl4 hp hp2 hp' hp'2 hf hf' hF hF' ?_
    rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv]
  · intro hU
    obtain ⟨hf', F', iF', fF', hF', ⟨e'⟩⟩ := lieModel_psu_unpack hU
    refine card_psp4_ne_card_psu4 hp hp2 hp' hp'2 hf hf' hF hF' ?_
    rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv]

theorem ivk_PSp4_ne_LU : Stage1.Thm3.Sec7.IVK_PSp4_ne_LU := by
  intro K _ _ q ⟨F, iF, fF, hF, ⟨e⟩⟩
  constructor
  · rintro (⟨-, F', iF', fF', hF', ⟨e'⟩⟩ | ⟨h, -⟩)
    · have hlt := card_psp4_lt_card_psl4 (F := F) (F' := F') (hF.trans hF'.symm)
      rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv] at hlt
      exact lt_irrefl _ hlt
    · exact absurd h (by norm_num)
  · rintro (⟨h, -⟩ | ⟨-, F', iF', fF', hF', ⟨e'⟩⟩)
    · exact absurd h (by norm_num)
    · have hlt := card_psp4_lt_card_psu4 (F := F) (F' := F') hF hF'
      rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv] at hlt
      exact lt_irrefl _ hlt

end CFSG.GH74.GLS.Stage2.Final
