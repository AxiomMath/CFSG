module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78

theorem conj_mem_of_mem_suzT
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160) {τ : Equiv.Perm (Fin 1782)}
    (hτ : τ ∈ suzT) (hτt : τ * suzInv 0 = suzInv 0 * τ) {x : Equiv.Perm (Fin 1782)}
    (hx : x ∈ K) : τ * x * τ⁻¹ ∈ K := by
  set K' : Subgroup (Equiv.Perm (Fin 1782)) := K.map (MulAut.conj τ).toMonoidHom with hK'def
  have hxK' : τ * x * τ⁻¹ ∈ K' := ⟨x, hx, rfl⟩
  have hτinv : τ⁻¹ * suzInv 0 = suzInv 0 * τ⁻¹ :=
    (show Commute τ (suzInv 0) from hτt).inv_left
  have hK'le : K' ≤ invE 0 := by
    rintro _ ⟨y, hy, rfl⟩
    have hyE := mem_invE_zero.1 (hK hy)
    refine mem_invE_zero.2 ⟨suzT_conj_mem_suzM hτ hyE.1, ?_⟩
    calc τ * y * τ⁻¹ * suzInv 0
        = τ * (y * (τ⁻¹ * suzInv 0)) := by group
      _ = τ * (y * (suzInv 0 * τ⁻¹)) := by rw [hτinv]
      _ = τ * (y * suzInv 0) * τ⁻¹ := by group
      _ = τ * (suzInv 0 * y) * τ⁻¹ := by rw [hyE.2]
      _ = (τ * suzInv 0) * y * τ⁻¹ := by group
      _ = (suzInv 0 * τ) * y * τ⁻¹ := by rw [hτt]
      _ = suzInv 0 * (τ * y * τ⁻¹) := by group
  have hK'perf : Group.IsPerfect K' := by
    rw [hK'def]
    exact Group.IsPerfect.map (MulAut.conj τ).toMonoidHom
  have hK'card : Nat.card K' = 20160 := by
    rw [hK'def, Subgroup.card_map_of_injective (MulAut.conj τ).injective, hcard]
  obtain ⟨hKperf', hKcard'⟩ := suz_subgroupOf_data hK hperf hcard
  obtain ⟨hK'perf', hK'card'⟩ := suz_subgroupOf_data hK'le hK'perf hK'card
  have heq := suz_quot2Data.eq_of_perfect hKperf' hKcard' hK'perf' hK'card'
  have hK'eq : K' = K := by
    have h := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.2 hK'le, inf_eq_left.2 hK] at h
  rwa [← hK'eq]

theorem suzInv_zero_not_mem
    {K : Subgroup (Equiv.Perm (Fin 1782))} (hK : K ≤ invE 0)
    (hperf : Group.IsPerfect K) (hcard : Nat.card K = 20160) : suzInv 0 ∉ K := by
  intro hmem
  have hM : suzInv 0 ∈ suzM :=
    CTUC_Suz_four_exact_involution_centralizers.2.2.2.2.2.1
  have ht : suzInv 0 ∈ invE 0 := suzInv_mem_invE (i := 0) (by norm_num) hM
  have hker : (⟨suzInv 0, ht⟩ : invE 0) ∈ rho0.ker :=
    suzInv_mem_ker (i := 0) (m := 42) (by norm_num) hm0 ht
  obtain ⟨hK', hcard'⟩ := suz_subgroupOf_data hK hperf hcard
  have hone : (⟨suzInv 0, ht⟩ : invE 0) = 1 :=
    suz_quot2Data.eq_one_of_map_eq_one hK' hcard'
      (Subgroup.mem_subgroupOf.2 hmem) (MonoidHom.mem_ker.1 hker)
  exact suzInv_ne_one (i := 0) (by norm_num) (congrArg Subtype.val hone)

theorem mul_comm_of_mem_ker_rho0
    {a b : invE 0} (ha : a ∈ rho0.ker) (hb : b ∈ rho0.ker) : a * b = b * a := by
  have hcard : Nat.card rho0.ker = 2 ^ 2 := by
    rw [card_ker_rho0]
    norm_num
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
