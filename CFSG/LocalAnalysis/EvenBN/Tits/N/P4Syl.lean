module

public import CFSG.Goldschmidt.Steps.G3aGlue
public import CFSG.Goldschmidt.Steps.TICrit

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_tInv_sylow {K : Subgroup Γ} {t : Γ} (ht : t * t = 1)
    (htK : t ∈ normalizer (K : Set Γ)) :
    ∃ S : Subgroup Γ, fusionIsSylowIn 2 S K ∧ ∀ s ∈ S, t * s * t⁻¹ ∈ S := by
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
  obtain ⟨k, hk, hkord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using hord : orderOf t ∣ 2 ^ 1)
  have hP : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hkord])
  have hle : K ≤ zpowers t ⊔ K := le_sup_right
  have hnorm : (K.subgroupOf (zpowers t ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer (zpowers_le.2 htK)
  obtain ⟨T, htT, hT⟩ := CFSG.Goldschmidt.TICrit.exists_fusionIsSylowIn hP (le_sup_left :
    zpowers t ≤ zpowers t ⊔ K)
  have hsub : (K.subgroupOf (zpowers t ⊔ K)).IsSubnormal :=
    Subgroup.IsSubnormal.step _ ⊤ le_top Subgroup.IsSubnormal.top (hnorm.subgroupOf ⊤)
  have hS := CFSG.Goldschmidt.G3a.fusionIsSylowIn_inf hT hle hsub
  refine ⟨T ⊓ K, hS, fun s hs => ?_⟩
  obtain ⟨hsT, hsK⟩ := Subgroup.mem_inf.1 hs
  refine Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem (htT (mem_zpowers t)) hsT)
    (T.inv_mem (htT (mem_zpowers t))), ?_⟩
  exact (mem_normalizer_iff.1 htK s).1 hsK

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
