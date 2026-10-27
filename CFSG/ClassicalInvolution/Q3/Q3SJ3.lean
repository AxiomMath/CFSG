module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria
public import CFSG.ClassicalInvolution.Q3.Q3SJ3Inputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.J3Proof CFSG.Monster.B.Co2
open CFSG.Sporadic.Schreier (mem_centralizerIn)

@[expose] def J3Witness : Prop :=
  ∃ g₁ g₂ : Equiv.Perm (Fin 20520), g₁ ∈ P3 ∧ g₂ ∈ P3 ∧ g₁ * pa = pa * g₁ ∧
    g₂ * pa = pa * g₂ ∧ g₁ ^ 3 = 1 ∧ g₂ ^ 3 = 1 ∧ (g₁ * g₂) ^ 2 = 1 ∧ g₁ * g₂ ≠ 1 ∧
    g₁ * g₂ ≠ pa

theorem j3Witness_of_check (h : j3WitnessCheck = true) : J3Witness := by
  have r₁ := kGen_rep 0 (by norm_num)
  have r₂ := kGen_rep 1 (by norm_num)
  have m₁ := kGen_mem_K 0 (by norm_num)
  have m₂ := kGen_mem_K 1 (by norm_num)
  have c₁ := mem_centralizerIn.1 (kChain_le_cent (mul_mem m₁ m₂))
  have c₂ := mem_centralizerIn.1 (kChain_le_cent
    (mul_mem m₂ (mul_mem m₁ (mul_mem m₁ (mul_mem m₂ (mul_mem m₂ (mul_mem m₁
      (mul_mem m₂ m₁))))))))
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := witnessCheckA_sound (g₁ := j3WitnessG₁) (g₂ := j3WitnessG₂)
    (rep_compA r₁ r₂)
    (rep_compA r₂ (rep_compA r₁ (rep_compA r₁ (rep_compA r₂ (rep_compA r₂ (rep_compA r₁
      (rep_compA r₂ r₁))))))) rep_pa h
  exact ⟨_, _, c₁.1, c₂.1, c₁.2, c₂.2, e₁, e₂, e₃, e₄, e₅⟩

theorem noWeakClassical3_P3 (hP : Nat.card P3 = 50232960) (hW : J3Witness) :
    NoWeakClassical3 P3 := by
  have hS2 : IsPGroup 2 sChain.originalSubgroup :=
    IsPGroup.of_card (n := 7) (by rw [card_sChain]; norm_num)
  have hidx : ¬ 2 ∣ (sChain.originalSubgroup.subgroupOf P3).index := by
    have h := (sChain.originalSubgroup.subgroupOf P3).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sChain_le_P3).toEquiv, card_sChain, hP]
      at h
    omega
  refine noWeakClassical3_of_sylow_cover_at P3 sChain.originalSubgroup hS2 hidx pa_mem
    cover_S ?_
  obtain ⟨g₁, g₂, h₁, h₂, c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := hW
  have h9 : ¬ 9 ∣ Nat.card (CFSG.Sporadic.Schreier.centralizerIn P3 pa) := by
    rw [centralizerIn_P3 hP, card_kChain]
    norm_num
  exact NoWeakClassical3At.of_ambient_witness P3 pa_mem h9 h₁ h₂ c₁ c₂ hg₁ hg₂ ht ht1 htz

theorem noWeakClassical3_J3 (hW : J3Witness) :
    NoWeakClassical3 CFSG.Blueprint.NativeSporadic.J3 :=
  NoWeakClassical3.of_mulEquiv nativeEquivP3 (noWeakClassical3_P3 card_P3 hW)

end CFSG.ClassicalInvolution.Q3
