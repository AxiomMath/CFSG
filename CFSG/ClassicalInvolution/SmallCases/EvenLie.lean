module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Parabolic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.RankOne
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Chevalley
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Linear
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Unitary
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Symplectic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Orthogonal

public section

namespace CFSG.ClassicalInvolution

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem noNonsolvableClassical_of_lieModel_two {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) (hF4 : t ≠ .twistedF4) (hTits : t ≠ .Tits) :
    NoNonsolvableClassical X := by
  rcases h with ⟨ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, rfl, hm⟩
  ·
    have hadm := hm.1
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact noNonsolvableClassical_of_psl_model hm
    · exact noNonsolvableClassical_of_psu_model hm
    · exact noNonsolvableClassical_of_psp_model hm
    · exact absurd rfl hadm.2.2.2
    · exact noNonsolvableClassical_of_pOmega_model (Or.inl rfl) hm
    · exact noNonsolvableClassical_of_pOmega_model (Or.inr rfl) hm
  · exact noNonsolvableClassical_of_chevalleyExceptionalModel hm
  ·
    have hadm := hm.1
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact absurd rfl hF4
    · exact absurd rfl hTits
  · exact noNonsolvableClassical_of_suzukiModel hm

theorem noNonsolvableClassical_of_lieModel_two_of_isEvenCharacteristic {X : Type} [Group X]
    [Finite X] {t : StatedLieTag} {n f : ℕ} (h : LieModel X t n 2 f)
    (hRT : (t = .twistedF4 ∨ t = .Tits) → IsEvenCharacteristic X) : NoNonsolvableClassical X := by
  by_cases h4 : t = .twistedF4 ∨ t = .Tits
  · exact noNonsolvableClassical_of_lieModel_of_isEvenCharacteristic h (hRT h4)
  · exact noNonsolvableClassical_of_lieModel_two h (fun h' => h4 (Or.inl h'))
      (fun h' => h4 (Or.inr h'))

end CFSG.ClassicalInvolution
