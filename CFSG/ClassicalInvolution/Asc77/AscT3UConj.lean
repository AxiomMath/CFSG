module

public import CFSG.ClassicalInvolution.Asc77.AscT3SInv
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77.T3CII.T3S
open scoped commutatorElement Pointwise

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_exactCore_sup {K K' : Subgroup G} {z c t : G}
    (hK : IsClassicalMember p f K z) (hK' : IsClassicalMember p f K' z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcK : c ∈ trivialOnQuot K)
    (hcK' : c ∈ trivialOnQuot K') (hKN' : K ≤ Subgroup.normalizer (K' : Set G))
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) (ht : t ∈ K ⊔ K') (ht2 : t * t = 1)
    (htc : c * t = t * c) :
    ∃ g ∈ K ⊔ K', c * g = g * c ∧ g * t * g⁻¹ ∈ exactCore c K ⊔ exactCore c K' := by
  classical
  set M : Subgroup G := K ⊔ K' with hM
  set N₀ : Subgroup G := oddCoreOf M with hN₀
  have hNodd : Odd (Nat.card N₀) := oddCoreOf_odd_natCard M
  have hKN : oddCoreOf K ≤ N₀ := oddCoreOf_le_oddCoreOf_sup hK'N
  have hK'N₀ : oddCoreOf K' ≤ N₀ := by
    have := oddCoreOf_le_oddCoreOf_sup hKN'
    rwa [sup_comm] at this
  have hNnorm : ∀ x ∈ M, ∀ n ∈ N₀, x * n * x⁻¹ ∈ N₀ := fun x hx n hn =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hx)) n).mp hn
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htM : t ∈ M := ht
  have hmul : t ∈ (K : Set G) * (K' : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K K' hKN']
    exact ht
  obtain ⟨k, hk, k', hk', hkk'⟩ := hmul
  obtain ⟨i, hi, n, hn, hkin⟩ := exactCore_cover hK hc2 hcK k hk
  obtain ⟨i', hi', n', hn', hkin'⟩ := exactCore_cover hK' hc2 hcK' k' hk'
  have hiM : i ∈ M := Subgroup.mem_sup_left (exactCore_le_left c K hi)
  have hi'M : i' ∈ M := Subgroup.mem_sup_right (exactCore_le_left c K' hi')
  set P₀ : Subgroup G := exactCore c K ⊔ exactCore c K' with hP₀
  set pp : G := i * i' with hpp
  have hppP : pp ∈ P₀ := P₀.mul_mem (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right hi')
  set m : G := (i'⁻¹ * n * i') * n' with hmdef
  have hmN : m ∈ N₀ := by
    refine N₀.mul_mem ?_ (hK'N₀ hn')
    have := hNnorm i'⁻¹ (M.inv_mem hi'M) n (hKN hn)
    simpa using this
  have htpm : t = pp * m := by
    rw [← hkk', hkin, hkin', hpp, hmdef]
    group
  have hcp : c * pp = pp * c := by
    have h1 : c * i = i * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (exactCore_le_centralizer c K hi)).symm
    have h2 : c * i' = i' * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (exactCore_le_centralizer c K' hi')).symm
    rw [hpp, ← mul_assoc, h1, mul_assoc, h2]
    group
  have hcpow : ∀ j : ℕ, c * pp ^ j = pp ^ j * c := fun j =>
    ((show Commute c pp from hcp).pow_right j).eq
  have hpm : pp = t * m⁻¹ := by
    rw [htpm]
    group
  have hq : pp * pp ∈ N₀ := by
    have e : pp * pp = (t * m⁻¹ * t⁻¹) * m⁻¹ := by
      calc pp * pp = (t * m⁻¹) * (t * m⁻¹) := by rw [← hpm]
        _ = (t * m⁻¹ * t⁻¹) * m⁻¹ := by rw [hti]; group
    rw [e]
    exact N₀.mul_mem (hNnorm t htM _ (N₀.inv_mem hmN)) (N₀.inv_mem hmN)
  set q : G := pp * pp with hqdef
  have hqodd : Odd (orderOf q) :=
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hq)
  obtain ⟨s, hs⟩ := hqodd
  set u : G := pp ^ orderOf q with hu
  have huP : u ∈ P₀ := P₀.pow_mem hppP _
  have huu : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, pow_mul, sq]
    exact pow_orderOf_eq_one q
  have hqs : q ^ s ∈ N₀ := N₀.pow_mem hq s
  have hut : u * t ∈ N₀ := by
    have e : u * t = q ^ s * (t * m⁻¹ * t⁻¹) := by
      have hu' : u = q ^ s * pp := by
        rw [hu, hs, pow_succ, pow_mul, sq]
      rw [hu', hti]
      nth_rewrite 1 [hpm]
      group
    rw [e]
    exact N₀.mul_mem hqs (hNnorm t htM _ (N₀.inv_mem hmN))
  have hutodd : Odd (orderOf (u * t)) :=
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N₀ hut)
  obtain ⟨j, hj⟩ := T3Core.exists_conj_of_mul_mem_odd huu ht2 hutodd
  have hcu : c * u = u * c := hcpow _
  have hcut : c * (u * t) = (u * t) * c := by
    rw [← mul_assoc, hcu, mul_assoc, htc, mul_assoc]
  have hcutj : c * (u * t) ^ j = (u * t) ^ j * c :=
    ((show Commute c (u * t) from hcut).pow_right j).eq
  have hgN : (u * t) ^ j ∈ N₀ := N₀.pow_mem hut j
  refine ⟨((u * t) ^ j)⁻¹, M.inv_mem (oddCoreOf_le_self M hgN), ?_, ?_⟩
  · have := ((show Commute c ((u * t) ^ j) from hcutj).inv_right).eq
    exact this
  · have e : ((u * t) ^ j)⁻¹ * t * (((u * t) ^ j)⁻¹)⁻¹ = u := by
      have h1 : (u * t) ^ j * u * ((u * t) ^ j)⁻¹ = t := hj
      calc ((u * t) ^ j)⁻¹ * t * (((u * t) ^ j)⁻¹)⁻¹
          = ((u * t) ^ j)⁻¹ * ((u * t) ^ j * u * ((u * t) ^ j)⁻¹) * (((u * t) ^ j)⁻¹)⁻¹ := by
            rw [h1]
        _ = u := by group
    rw [e]
    exact huP

end CFSG.ClassicalInvolution.Asc77.T3CII.T3U
