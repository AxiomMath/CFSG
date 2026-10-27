module

public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.KS.Pres

open CFSG.Sporadic.Bridge

theorem card_closure_le_k {G : Type*} [Group G] (P : TauCeti.GroupPresentation) {x : ℕ → G}
    (hrel : ∀ v ∈ P.relatorLetters, wordProd x v = 1) [Finite P.Group] :
    Nat.card (Subgroup.closure (Set.range fun i : Fin P.generatorCount => x i.val)) ≤
      Nat.card P.Group := by
  have hle : Subgroup.closure (Set.range fun i : Fin P.generatorCount => x i.val) ≤
      (presHom P x hrel).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨presGen P i.val, presHom_presGen P x hrel i.isLt⟩
  have hs := (presHom P x hrel).rangeRestrict_surjective
  have : Finite (presHom P x hrel).range := Finite.of_surjective _ hs
  exact (Subgroup.card_le_of_le hle).trans (Nat.card_le_card_of_surjective _ hs)

theorem card_closure_le_k' {G : Type*} [Group G] (P : TauCeti.GroupPresentation) {k : ℕ}
    (hk : P.generatorCount = k) {x : ℕ → G} (hrel : ∀ v ∈ P.relatorLetters, wordProd x v = 1)
    [Finite P.Group] :
    Nat.card (Subgroup.closure (Set.range fun i : Fin k => x i.val)) ≤ Nat.card P.Group := by
  subst hk
  exact card_closure_le_k P hrel

theorem wordProd_mem_closure {G : Type*} [Group G] {x : ℕ → G} {k : ℕ} (w : List (ℕ × Bool))
    (hw : ∀ l ∈ w, l.1 < k) :
    wordProd x w ∈ Subgroup.closure (Set.range fun i : Fin k => x i.val) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ (ih fun l' h => hw l' (List.mem_cons_of_mem _ h))
    have hl : x l.1 ∈ Subgroup.closure (Set.range fun i : Fin k => x i.val) :=
      Subgroup.subset_closure ⟨⟨l.1, hw l List.mem_cons_self⟩, rfl⟩
    split
    · exact hl
    · exact Subgroup.inv_mem _ hl

end CFSG.KS.Pres

end
