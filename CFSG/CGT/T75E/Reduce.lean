module

public import CFSG.CGT.T75E.Quotient
public import CFSG.Timmesfeld.Bridge.Asc72ZMain

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Lemma26SimpleConcl (K : Type) [Group K] (T : Subgroup K) : Prop :=
  ((∃ n m : ℕ, 2 ≤ n ∧ 1 ≤ m ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL n 2 m) ∨
      (∃ m : ℕ, 2 ≤ m ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 m) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel K .twistedB2 0 2 s) ∨
      Nonempty (K ≃* alternatingGroup (Fin 6))) ∧
    (¬ Nonempty (K ≃* alternatingGroup (Fin 6)) →
      ∀ U₁ U₂ V₁ V₂ : Subgroup K, (∃ x : K, U₁ = conjSubgroup x T) →
        (∃ x : K, U₂ = conjSubgroup x T) → (∃ x : K, V₁ = conjSubgroup x T) →
        (∃ x : K, V₂ = conjSubgroup x T) → U₁ ≠ U₂ → V₁ ≠ V₂ →
          ∃ g : K, conjSubgroup g U₁ = V₁ ∧ conjSubgroup g U₂ = V₂)

@[expose] def Lemma26Simple : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K] (T : Subgroup K), Lemma26Hyp K T →
    Lemma26SimpleConcl K T


theorem hyp_isSimple_quotient {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (h : Lemma26Hyp G T) : IsSimpleGroup (G ⧸ Subgroup.center G) := by
  have h' := hyp_map h
  exact lemma215 _ _ h'.1 (hyp_four_le_card h') (hyp_normalClosure_eq_top h') (hyp_solvable_bot h)

theorem lemma26_of_simple (hS : Lemma26Simple) : Lemma26Input := by
  intro G _ _ T hT h4 hcl hroot hgen
  have hyp : Lemma26Hyp G T := ⟨hT, h4, hcl, hroot, hgen⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hyp_isSimple_quotient hyp
  obtain ⟨h1, h2⟩ := hS (G ⧸ Subgroup.center G) (T.map (toCenterQuot G)) (hyp_map hyp)
  refine ⟨h1, fun hnA U₁ U₂ V₁ V₂ hU₁ hU₂ hV₁ hV₂ hne1 hne2 => ?_⟩
  have himg : ∀ {W : Subgroup G}, (∃ x : G, W = conjSubgroup x T) →
      ∃ x : G ⧸ Subgroup.center G,
        W.map (toCenterQuot G) = conjSubgroup x (T.map (toCenterQuot G)) := by
    rintro W ⟨x, rfl⟩
    exact ⟨toCenterQuot G x, map_conjSubgroup _ _ _⟩
  have hinj : ∀ {W W' : Subgroup G}, (∃ x : G, W = conjSubgroup x T) →
      (∃ x : G, W' = conjSubgroup x T) →
      W.map (toCenterQuot G) = W'.map (toCenterQuot G) → W = W' := by
    rintro W W' ⟨x, rfl⟩ ⟨y, rfl⟩ hmap
    exact eq_of_map_eq_center_quot hyp hmap
  obtain ⟨gb, hg1, hg2⟩ := h2 hnA _ _ _ _ (himg hU₁) (himg hU₂) (himg hV₁) (himg hV₂)
    (fun e => hne1 (hinj hU₁ hU₂ e)) (fun e => hne2 (hinj hV₁ hV₂ e))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) gb
  have hconj : ∀ {W : Subgroup G}, (∃ x : G, W = conjSubgroup x T) →
      ∃ x : G, conjSubgroup g W = conjSubgroup x T := by
    rintro W ⟨x, rfl⟩
    exact ⟨g * x, conjSubgroup_conjSubgroup g x T⟩
  refine ⟨g, hinj (hconj hU₁) hV₁ ?_, hinj (hconj hU₂) hV₂ ?_⟩
  · rw [map_conjSubgroup]
    exact hg1
  · rw [map_conjSubgroup]
    exact hg2

end CFSG.CGT.T75E
