module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie
public import CFSG.ClassicalInvolution.SmallCases.Partition
public import CFSG.ClassicalInvolution.SmallCases.Sporadic

public section

namespace CFSG.ClassicalInvolution

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def GH74SectionalModels : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) → 3 ≤ CFSG.Open.twoRank G →
    (∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (CFSG.Blueprint.LieModel G .G2 0 p f ∨ CFSG.Blueprint.LieModel G .trialityD4 0 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel G .PSp 2 p f) ∨
    (∃ f : ℕ, CFSG.Blueprint.LieModel G .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧
      CFSG.Blueprint.LieModel G .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧
      CFSG.Blueprint.LieModel G .PSU 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel G .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel G .PSU 5 p f) ∨
    (CFSG.Blueprint.LieModel G .PSL 2 2 3 ∨ CFSG.Blueprint.LieModel G .PSL 2 2 4 ∨
      CFSG.Blueprint.LieModel G .PSL 3 2 2 ∨ CFSG.Blueprint.LieModel G .twistedB2 0 2 3) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J3 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .McL ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .Ly)

set_option linter.unusedVariables false in
theorem oddLieType_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ≠ .twistedB2) :
    OddLieType G :=
  ⟨t, n, p, f, hp, hp2, CFSG.Blueprint.LieModel.admissible h, h⟩

theorem ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

theorem citSectionalFour_of_gh74 (hLy : NoNonsolvableClassical (NativeSporadic.Carrier .Ly))
    (hGH : GH74SectionalModels) : CITSectionalFour := by
  intro F _ _ _ hnab z hz K hzK hK hw hns hP
  obtain ⟨hrank, hsect⟩ := hP
  have hex : NoNonsolvableClassical F → False := fun hN => hN z hz K hzK hK hw hns
  rcases hGH F hnab hrank hsect with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨f, h⟩ |
    ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hp2, hf, -, h⟩ | ⟨p, f, hp, hf, hm, h⟩ |
    ⟨p, f, hp, hf, hm, h⟩ | h | ⟨n, -, -, ⟨e⟩⟩ | h
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
  · exfalso
    rcases h with h | h | h | h
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
    · exact hex (noNonsolvableClassical_of_lieModel_two h (by decide) (by decide))
  · exact (hex (NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_alternating n))).elim
  · exact (hex (noNonsolvableClassical_of_gh74_models hLy h)).elim

end CFSG.ClassicalInvolution
