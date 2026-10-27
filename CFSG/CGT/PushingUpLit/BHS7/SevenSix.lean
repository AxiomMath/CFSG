module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS6.SixNine

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem le_cStarIn_self (hT : IsSylowTwoOf T G) (hne : cStarIn G T ≠ G) : T ≤ cStarIn G T := by
  have hb0 : baum T ≠ ⊥ := fun h0 => hne (cStarIn_eq_of_baum_eq_bot h0)
  have hT0 : T ≠ ⊥ := fun h0 => hb0 (by rw [h0]; exact le_bot_iff.1 (inf_le_left))
  exact fun t ht => inf_normalizer_le_cStarIn hT.2.1 hT0 ⟨hT.1 ht, Subgroup.le_normalizer ht⟩

theorem exists_not_le_cStarIn_of_not_isMinParabolic2 (hT : IsSylowTwoOf T G)
    (hne : cStarIn G T ≠ G) (h5 : ¬ IsMinParabolic2 T G) :
    ∃ X : Subgroup Γ, T ≤ X ∧ X < G ∧ ¬ X ≤ cStarIn G T := by
  by_contra hno
  push Not at hno
  apply h5
  have hb0 : baum T ≠ ⊥ := fun h0 => hne (cStarIn_eq_of_baum_eq_bot h0)
  have hT0 : T ≠ ⊥ := fun h0 => hb0 (by rw [h0]; exact le_bot_iff.1 (inf_le_left))
  refine ⟨hT, fun hGn => hne ?_, cStarIn G T, le_cStarIn_self hT hne,
    lt_of_le_of_ne (cStarIn_le G T) hne, fun X hTX hXG => hno X hTX hXG⟩
  refine le_antisymm (cStarIn_le G T) fun g hg => ?_
  exact inf_normalizer_le_cStarIn hT.2.1 hT0 ⟨hg, hGn hg⟩

theorem exists_isBTBlock_not_le (h : MinCex G T) (h5 : ¬ IsMinParabolic2 T G) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨X, hTX, hXG, hXC⟩ := exists_not_le_cStarIn_of_not_isMinParabolic2 hT h.ne h5
  have hBX : baum T ≤ X := (inf_le_left : baum T ≤ T).trans hTX
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBX
  obtain ⟨-, -, 𝒢, hblock, -, -, hc, -⟩ := seven_three h hT ⟨hXG, hBX, hXC⟩ hS
  have hSX : baum S = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hXG.le) hBS
  by_contra hall
  push Not at hall
  apply hXC
  rw [← hc]
  refine sup_le (two_three_d hT hb0 hXG.le hS hBS) (iSup₂_le fun F hF => ?_)
  by_contra hFC
  exact hFC (hall F (isBTBlock_of_sub (hblock F hF) hXG.le hSX hFC))

theorem exists_maximal_isBTBlock_ge {F : Subgroup Γ} (hF : IsBTBlock G T F) :
    ∃ E : Subgroup Γ, IsBTBlock G T E ∧ F ≤ E ∧
      ∀ F' : Subgroup Γ, IsBTBlock G T F' → E ≤ F' → F' = E := by
  have hne : {E : Subgroup Γ | IsBTBlock G T E ∧ F ≤ E}.Nonempty := ⟨F, hF, le_rfl⟩
  obtain ⟨E, ⟨hE, hFE⟩, hmax⟩ := Set.exists_max_image {E : Subgroup Γ | IsBTBlock G T E ∧ F ≤ E}
    (fun E => Nat.card E) (Set.toFinite _) hne
  refine ⟨E, hE, hFE, fun F' hF' hEF' => ?_⟩
  have h1 : Nat.card F' ≤ Nat.card E := hmax F' ⟨hF', hFE.trans hEF'⟩
  exact (Subgroup.eq_of_le_of_card_ge hEF' h1).symm

theorem seven_six (h : MinCex G T) (h5 : ¬ IsMinParabolic2 T G) :
    (∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T) ∧
      ∀ F : Subgroup Γ, IsBTBlock G T F → ¬ F ≤ cStarIn G T → ∃ E ∈ bStarT G T, F ≤ E := by
  refine ⟨exists_isBTBlock_not_le h h5, fun F hF hFC => ?_⟩
  obtain ⟨E, hE, hFE, hmax⟩ := exists_maximal_isBTBlock_ge hF
  exact ⟨E, ⟨⟨BHS6.six_nine h.charTwo h.sylow hE hmax, hE⟩, fun hEC => hFC (hFE.trans hEC)⟩,
    hFE⟩

end CFSG.CGT.PushingUpLit.BHS7
