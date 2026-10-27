module

public import CFSG.ClassicalInvolution.Q3.Q3T6XStmt
import CFSG.ClassicalInvolution.Q3.Q3T6XTriv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

@[expose] def DiagInputTrivOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {Q : Subgroup F} {r u : F}, Mem3 Q r → r ∈ S → u ∈ S → u * u = 1 → u * r = r * u →
    Q ≠ conjSub u Q → ∀ {I : Subgroup F}, Mem3 I u → (∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) →
      ∀ {q : F}, q ∈ Q → IsPGroup 2 (Subgroup.zpowers q) →
        q * (u * q * u⁻¹) = (u * q * u⁻¹) * q →
          q * (u * q * u⁻¹) ∈ Subgroup.normalizer (I : Set F)

@[expose] def DiagInputNontrivOn (F : Type) [Group F] [Finite F] (S : Set F) : Prop :=
  ∀ {Q : Subgroup F} {r u : F}, Mem3 Q r → r ∈ S → u ∈ S → u * u = 1 → u * r = r * u →
    Q ≠ conjSub u Q → ∀ {I : Subgroup F}, Mem3 I u → r ∈ Subgroup.normalizer (I : Set F) →
      ¬ (∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) →
        ∀ {q : F}, q ∈ Q → IsPGroup 2 (Subgroup.zpowers q) →
          q * (u * q * u⁻¹) = (u * q * u⁻¹) * q →
            q * (u * q * u⁻¹) ∈ Subgroup.normalizer (I : Set F)

theorem mem_normalizer_of_trivial {r : F} (hr2 : r * r = 1) {I : Subgroup F}
    (htriv : ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I) : r ∈ Subgroup.normalizer (I : Set F) :=
  CFSG.ClassicalInvolution.Q3.Q3T6X.mem_normalizer_of_trivial hr2 htriv

theorem diagInputNormOn_iff (S : Set F) :
    DiagInputNormOn F S ↔ DiagInputTrivOn F S ∧ DiagInputNontrivOn F S := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro Q r u hQ hrS huS hu2 hur hne I hI htriv q hq hq2 hqc
      exact h hQ hrS huS hu2 hur hne hI (mem_normalizer_of_trivial hQ.mul_self htriv) hq hq2 hqc
    · intro Q r u hQ hrS huS hu2 hur hne I hI hrI _ q hq hq2 hqc
      exact h hQ hrS huS hu2 hur hne hI hrI hq hq2 hqc
  · rintro ⟨hT, hN⟩ Q r u hQ hrS huS hu2 hur hne I hI hrI q hq hq2 hqc
    by_cases htriv : ∀ j ∈ I, ⁅r, j⁆ ∈ oddCoreOf I
    · exact hT hQ hrS huS hu2 hur hne hI htriv hq hq2 hqc
    · exact hN hQ hrS huS hu2 hur hne hI hrI htriv hq hq2 hqc

theorem fusion3MinOn_of_parts {S : Set F} (hsym : SymOuterOn F S) (htriv : DiagInputTrivOn F S)
    (hnt : DiagInputNontrivOn F S) : Fusion3MinOn F S :=
  ⟨hsym, (diagInputNormOn_iff S).mpr ⟨htriv, hnt⟩⟩

end CFSG.ClassicalInvolution.Q3.Q3T6Y
