module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLeafConj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddLeafNormal

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78

theorem comm_of_mem_ker_rho0
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160) {d : Equiv.Perm (Fin 1782)}
    (hd : d ∈ K) (hd2 : orderOf d = 2) {τ : Equiv.Perm (Fin 1782)} (hτ : τ ∈ suzT)
    (hτt : τ * suzInv 0 = suzInv 0 * τ)
    (hdev : ∀ x ∈ K, x * d = d * x → x ^ 4 = 1 →
      τ * x * τ⁻¹ = x ∨ τ * x * τ⁻¹ = suzInv 0 * x)
    {n : Equiv.Perm (Fin 1782)} (hn : n ∈ invE 0) (hnk : (⟨n, hn⟩ : invE 0) ∈ rho0.ker) :
    τ * n = n * τ := by
  have hcommK : ∀ x ∈ K, x * d = d * x → x ^ 4 = 1 → τ * x = x * τ := by
    intro x hx hxd hx4
    rcases hdev x hx hxd hx4 with h | h
    · calc τ * x = (τ * x * τ⁻¹) * τ := by group
        _ = x * τ := by rw [h]
    · exfalso
      have hconj : τ * x * τ⁻¹ ∈ K := conj_mem_of_mem_suzT hK hperf hcard hτ hτt hx
      have ht0x : suzInv 0 * x ∈ K := h ▸ hconj
      refine suzInv_zero_not_mem hK hperf hcard ?_
      simpa [mul_assoc] using K.mul_mem ht0x (K.inv_mem hx)
  obtain ⟨hτE, hτD⟩ :=
    exists_mem_invE_zero_and_rho0_mem_suzD_of_forall_comm hK hperf hcard hd hd2 hτ hτt hcommK
  obtain ⟨hK', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  obtain ⟨k, hkK, n₀, hn₀, hτeq⟩ := suz_quot2Data.exists_mul_ker hK' hcard' hτD
  have hkn : k * ⟨n, hn⟩ = ⟨n, hn⟩ * k := suz_quot2Data.comm_ker hK' hcard' hkK hnk
  have hn₀n : n₀ * ⟨n, hn⟩ = ⟨n, hn⟩ * n₀ := mul_comm_of_mem_ker_rho0 hn₀ hnk
  have hτcomm : (⟨τ, hτE⟩ : invE 0) * ⟨n, hn⟩ = ⟨n, hn⟩ * ⟨τ, hτE⟩ := by
    rw [hτeq]
    calc k * n₀ * ⟨n, hn⟩ = k * (n₀ * ⟨n, hn⟩) := by rw [mul_assoc]
      _ = k * (⟨n, hn⟩ * n₀) := by rw [hn₀n]
      _ = k * ⟨n, hn⟩ * n₀ := by rw [mul_assoc]
      _ = (⟨n, hn⟩ * k) * n₀ := by rw [hkn]
      _ = ⟨n, hn⟩ * (k * n₀) := by rw [mul_assoc]
  exact congrArg Subtype.val hτcomm

end CFSG.ComponentClassification.GrSLit.L34Sec5S
