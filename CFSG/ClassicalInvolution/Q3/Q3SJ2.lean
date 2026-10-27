module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria
public import CFSG.ClassicalInvolution.Q3.Q3SJ2Inputs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution CFSG.Monster.B.Co2
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

@[expose] def J2TwoAWitness : Prop :=
  ∃ g₁ g₂ : Equiv.Perm (Fin 315), g₁ ∈ P ∧ g₂ ∈ P ∧ g₁ * permTwoA = permTwoA * g₁ ∧
    g₂ * permTwoA = permTwoA * g₂ ∧ g₁ ^ 3 = 1 ∧ g₂ ^ 3 = 1 ∧ (g₁ * g₂) ^ 2 = 1 ∧
    g₁ * g₂ ≠ 1 ∧ g₁ * g₂ ≠ permTwoA

theorem j2TwoAWitness_of_check (h : j2WitnessCheck = true) : J2TwoAWitness := by
  have hrep : ∀ i < 2, Rep 315 cent2AStrong[i]! (permOfArr 315 cent2AStrong[i]!) := fun i hi =>
    rep_permOfArr_of_chainOK J2Proof.cent2A_ok (by
      have : cent2AStrong.size = 5 := rfl
      omega)
  have hmem : ∀ i < 2, permOfArr 315 cent2AStrong[i]! ∈ cent2AChain.originalSubgroup := by
    intro i hi
    rw [cent2AChain, ofArrays_originalSubgroup]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hK : cent2AChain.originalSubgroup ≤ centralizerIn P permTwoA := cent2A_facts.1
  have r₁ := hrep 0 (by norm_num)
  have r₂ := hrep 1 (by norm_num)
  have m₁ := hmem 0 (by norm_num)
  have m₂ := hmem 1 (by norm_num)
  have c₁ := mem_centralizerIn.1 (hK (mul_mem (mul_mem m₁ m₂) (mul_mem m₁ m₂)))
  have c₂ := mem_centralizerIn.1 (hK (mul_mem (mul_mem m₂ m₁) (mul_mem m₂ m₁)))
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := witnessCheckA_sound (g₁ := j2WitnessG₁) (g₂ := j2WitnessG₂)
    (rep_compA (rep_compA r₁ r₂) (rep_compA r₁ r₂))
    (rep_compA (rep_compA r₂ r₁) (rep_compA r₂ r₁)) rep_permTwoA h
  exact ⟨_, _, c₁.1, c₂.1, c₁.2, c₂.2, e₁, e₂, e₃, e₄, e₅⟩

theorem noWeakClassical3_J2P (hW : J2TwoAWitness) : NoWeakClassical3 P := by
  obtain ⟨hcov, -, he1, -, he2⟩ := inner_classes
  refine noWeakClassical3_of_reps P [permA, permTwoA] hcov ?_
  intro r hr hrep
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
  rcases hrep with rfl | rfl
  · obtain ⟨N, hNK, hcard, hnotin⟩ := J2Proof.cent2B_structure
    exact NoWeakClassical3At.of_ambient_index_two P ⟨permA, hr⟩ N (he1 ▸ hNK) (he1 ▸ hcard)
      hnotin
  · obtain ⟨g₁, g₂, h₁, h₂, c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := hW
    have h9 : ¬ 9 ∣ Nat.card (CFSG.Sporadic.Schreier.centralizerIn P permTwoA) := by
      rw [he2, (cent2A_facts).2.1]
      norm_num
    exact NoWeakClassical3At.of_ambient_witness P hr h9 h₁ h₂ c₁ c₂ hg₁ hg₂ ht ht1 htz

theorem noWeakClassical3_J2 (hW : J2TwoAWitness) :
    NoWeakClassical3 CFSG.Blueprint.NativeSporadic.J2 :=
  NoWeakClassical3.of_mulEquiv nativeEquivP (noWeakClassical3_J2P hW)

end CFSG.ClassicalInvolution.Q3
