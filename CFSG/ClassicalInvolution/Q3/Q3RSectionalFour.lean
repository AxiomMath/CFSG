module

public import CFSG.ClassicalInvolution.Q3.Q3RCoreStepPieces
public import CFSG.ClassicalInvolution.SmallCases.SectionalFourBranch

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

@[expose] def NoWeakClassical3 (F : Type) [Group F] : Prop :=
  ∀ (K : Subgroup F) (z : F), ¬ IsClassicalMember3 K z

theorem NoWeakClassical3.of_mulEquiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F')
    (h : NoWeakClassical3 F') : NoWeakClassical3 F := fun _ _ hK =>
  h _ _ (hK.map_mulEquiv e)

@[expose] def SectionalFourNonLie3 : Prop :=
  (∀ n : ℕ, 8 ≤ n → n ≤ 11 → NoWeakClassical3 (alternatingGroup (Fin n))) ∧
  (∀ (G : Type) [Group G], (LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨
      LieModel G .PSL 3 2 2 ∨ LieModel G .twistedB2 0 2 3) → NoWeakClassical3 G) ∧
  (∀ (G : Type) [Group G], (NativeSporadic.IsSporadic G .M12 ∨
      NativeSporadic.IsSporadic G .M22 ∨ NativeSporadic.IsSporadic G .M23 ∨
      NativeSporadic.IsSporadic G .J1 ∨ NativeSporadic.IsSporadic G .J2 ∨
      NativeSporadic.IsSporadic G .J3 ∨ NativeSporadic.IsSporadic G .McL ∨
      NativeSporadic.IsSporadic G .Ly) → NoWeakClassical3 G)

theorem citSectionalFour3_of_gh74 (hGH : GH74SectionalModels)
    (hAlt : ∀ n : ℕ, 8 ≤ n → n ≤ 11 → NoWeakClassical3 (alternatingGroup (Fin n)))
    (hTwo : ∀ (G : Type) [Group G], (LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨
      LieModel G .PSL 3 2 2 ∨ LieModel G .twistedB2 0 2 3) → NoWeakClassical3 G)
    (hSpor : ∀ (G : Type) [Group G], (NativeSporadic.IsSporadic G .M12 ∨
      NativeSporadic.IsSporadic G .M22 ∨ NativeSporadic.IsSporadic G .M23 ∨
      NativeSporadic.IsSporadic G .J1 ∨ NativeSporadic.IsSporadic G .J2 ∨
      NativeSporadic.IsSporadic G .J3 ∨ NativeSporadic.IsSporadic G .McL ∨
      NativeSporadic.IsSporadic G .Ly) → NoWeakClassical3 G) : CITSectionalFour3 := by
  intro F _ _ _ hnab z K hK hrank hsect
  rcases hGH F hnab hrank hsect with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hf, hm, h⟩ |
    ⟨p, f, hp, hf, hm, h⟩ | h | ⟨n, h8, h11, ⟨e⟩⟩ | h
  · left
    rcases h with h | h
    · exact oddLieType_of_lieModel h hp hp2 (by decide)
    · exact oddLieType_of_lieModel h hp hp2 (by decide)
  · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
  · exact Or.inl (oddLieType_of_lieModel h Nat.prime_three (by norm_num) (by decide))
  · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
  · exact Or.inl (oddLieType_of_lieModel h hp hp2 (by decide))
  · exact Or.inl (oddLieType_of_lieModel h hp (ne_two_of_pow_mod_four hf (Or.inl hm))
      (by decide))
  · exact Or.inl (oddLieType_of_lieModel h hp (ne_two_of_pow_mod_four hf (Or.inr hm))
      (by decide))
  · exact (hTwo F h K z hK).elim
  · exact (NoWeakClassical3.of_mulEquiv e (hAlt n h8 h11) K z hK).elim
  · exact (hSpor F h K z hK).elim

theorem citSectionalFour3_of_gh74_nonLie (hGH : GH74SectionalModels) (h : SectionalFourNonLie3) :
    CITSectionalFour3 :=
  citSectionalFour3_of_gh74 hGH h.1 h.2.1 h.2.2

end CFSG.ClassicalInvolution.Q3
