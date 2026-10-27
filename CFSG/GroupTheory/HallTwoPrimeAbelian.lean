module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

public section

namespace CFSG

theorem isMulCommutative_of_isHallSubgroup_of_quotient_pCore
    {Y : Type} [Group Y] [Finite Y] {B H : Subgroup Y} (hB : B.Normal)
    (hH : IsHallSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} H) (hHB : H ≤ B)
    (hcomm : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B)) : IsMulCommutative ↥H := by
  classical
  let P : Subgroup ↥B := CFSG.pCore 2 ↥B
  let K : Subgroup ↥B := H.subgroupOf B
  haveI : P.Normal := CFSG.pCore_normal
  have h2not : ¬ 2 ∣ Nat.card H := by
    intro h2
    have hmem : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ {p : Nat.Primes | (p : ℕ) ≠ 2} :=
      hH.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h2
    exact hmem rfl
  have hKcard : Nat.card K = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv
  have hcop : Nat.Coprime (Nat.card K) (Nat.card P) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
    have hPcard : Nat.card P = 2 ^ n := hn
    rw [hKcard, hPcard]
    exact Nat.prime_two.coprime_pow_of_not_dvd h2not
  have hdisj : Disjoint K P := Subgroup.disjoint_of_coprime_natCard hcop
  let φ : ↥H →* (↥B ⧸ P) := (QuotientGroup.mk' P).comp (Subgroup.inclusion hHB)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
    have hxP : Subgroup.inclusion hHB x ∈ P := by
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hHB x)).mp (by simpa [φ] using hx1)
    have hxK : Subgroup.inclusion hHB x ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      exact x.2
    have hmem : Subgroup.inclusion hHB x ∈ K ⊓ P := ⟨hxK, hxP⟩
    rw [hdisj.eq_bot] at hmem
    have hincl1 : Subgroup.inclusion hHB x = 1 := by simpa using hmem
    exact Subgroup.inclusion_injective hHB (by simpa using hincl1)
  refine IsMulCommutative.of_comm fun a b => hφinj ?_
  calc
    φ (a * b) = φ a * φ b := map_mul φ a b
    _ = φ b * φ a := hcomm.is_comm.comm (φ a) (φ b)
    _ = φ (b * a) := (map_mul φ b a).symm

end CFSG
