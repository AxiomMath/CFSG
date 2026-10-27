module

public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowPrime
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowHyperplane
public import CFSG.GroupTheory.SmallFixedTwoGroup.EightSylowTransfer

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem le_of_relIndex_prime {G : Type*} [Group G] {T C N : Subgroup G} (hTC : T ≤ C)
    (hCN : C ≤ N) (hprime : (T.relIndex N).Prime) {x : G} (hxC : x ∈ C) (hxT : x ∉ T) :
    N ≤ C := by
  have hmul : T.relIndex C * C.relIndex N = T.relIndex N :=
    Subgroup.relIndex_mul_relIndex T C N hTC hCN
  rcases Nat.prime_mul_iff.mp (hmul ▸ hprime) with ⟨_, hC1⟩ | ⟨_, hT1⟩
  · exact Subgroup.relIndex_eq_one.mp hC1
  · exact absurd (Subgroup.relIndex_eq_one.mp hT1 hxC) hxT

theorem false_of_relIndex_normalizer_eq_three {E : Type*} [Group E] [Finite E]
    (hE : ∀ N : Subgroup E, N.index ≠ 2) (P : Sylow 2 E)
    (hab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), a * b = b * a)
    (hcard : Nat.card (P : Subgroup E) = 8)
    (hCP : ∀ x : E, (∀ y ∈ (P : Subgroup E), x * y = y * x) → x ∈ (P : Subgroup E))
    (h3 : (P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E)) = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxN, hxord⟩ :=
    exists_mem_normalizer_orderOf_eq_of_prime_dvd_relIndex (T := (P : Subgroup E)) (r := 3)
      (by rw [h3])
  have hx3 : x ^ 3 = 1 := hxord ▸ pow_orderOf_eq_one x
  have hxT : x ∉ (P : Subgroup E) := by
    intro hxT
    have hdv : orderOf x ∣ Nat.card (P : Subgroup E) := Subgroup.orderOf_dvd_natCard _ hxT
    rw [hxord, hcard] at hdv
    norm_num at hdv
  have hne : ¬ (P : Subgroup E) ≤ centralizer ({x} : Set E) := by
    intro hle
    apply hxT
    refine hCP x (fun y hy => ?_)
    have hyc : y ∈ centralizer ({x} : Set E) := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    exact hyc.symm
  set F : Subgroup E := (P : Subgroup E) ⊓ centralizer ({x} : Set E) with hFdef
  have hF2 : Nat.card F = 2 := by
    rcases prime_order_acts_on_order_eight (T := (P : Subgroup E)) hcard (r := 3)
        (by norm_num) hx3 hxN hne with ⟨_, h⟩ | ⟨h7, _⟩
    · rwa [hFdef]
    · exact absurd h7 (by norm_num)
  obtain ⟨pF, hpF_ne, hpF_uniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF2
  have hpF_mem : (pF : E) ∈ F := pF.2
  have hFmem : ∀ y ∈ F, y = 1 ∨ y = (pF : E) := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · refine Or.inr ?_
      have : (⟨y, hy⟩ : F) = pF := hpF_uniq ⟨y, hy⟩ (fun h => hy1 (Subtype.ext_iff.mp h))
      exact congrArg Subtype.val this
  have hpT : (pF : E) ∈ (P : Subgroup E) := by
    have hFT : F ≤ (P : Subgroup E) := by rw [hFdef]; exact inf_le_left
    exact hFT hpF_mem
  have hpc : (pF : E) ∈ centralizer ({x} : Set E) := by
    have hFc : F ≤ centralizer ({x} : Set E) := by rw [hFdef]; exact inf_le_right
    exact hFc hpF_mem
  have hp1 : (pF : E) ≠ 1 := fun h => hpF_ne (Subtype.ext h)
  have hpx : x * (pF : E) * x⁻¹ = (pF : E) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hpc
    exact mul_inv_eq_iff_eq_mul.mpr hpc.symm
  have hFhyp : ∀ y ∈ (P : Subgroup E), x * y * x⁻¹ = y → y = 1 ∨ y = (pF : E) := by
    intro y hy hyx
    apply hFmem y
    refine mem_inf.mpr ⟨hy, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxy : x * y = y * x := mul_inv_eq_iff_eq_mul.mp hyx
    exact hxy.symm
  set C : Subgroup E := centralizer ({(pF : E)} : Set E) ⊓
    normalizer ((P : Subgroup E) : Set E) with hCdef
  have hTC : (P : Subgroup E) ≤ C := by
    rw [hCdef]
    refine le_inf (fun y hy => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab y hy (pF : E) hpT
  have hCN : C ≤ normalizer ((P : Subgroup E) : Set E) := by
    rw [hCdef]
    exact inf_le_right
  have hxC : x ∈ C := by
    rw [hCdef]
    refine mem_inf.mpr ⟨?_, hxN⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hpc
    exact hpc.symm
  have hprime : ((P : Subgroup E).relIndex (normalizer ((P : Subgroup E) : Set E))).Prime :=
    h3 ▸ Nat.prime_three
  have hNleC : normalizer ((P : Subgroup E) : Set E) ≤ C :=
    le_of_relIndex_prime (T := (P : Subgroup E)) (C := C)
      (N := normalizer ((P : Subgroup E) : Set E)) hTC hCN hprime hxC hxT
  have hfix : ∀ n ∈ normalizer ((P : Subgroup E) : Set E),
      n * (pF : E) * n⁻¹ = (pF : E) := by
    intro n hn
    have hnC : n ∈ C := hNleC hn
    have hnc : n ∈ centralizer ({(pF : E)} : Set E) := by
      have h := hnC
      rw [hCdef] at h
      exact (mem_inf.mp h).1
    rw [Subgroup.mem_centralizer_singleton_iff] at hnc
    exact mul_inv_eq_iff_eq_mul.mpr hnc
  have hp2 : (pF : E) * (pF : E) = 1 := by
    have hmem : (pF : E) * (pF : E) ∈ F := F.mul_mem hpF_mem hpF_mem
    rcases hFmem _ hmem with h | h
    · exact h
    · exfalso
      apply hp1
      have h' : (pF : E) * (pF : E) = (pF : E) * 1 := by rw [h, mul_one]
      exact mul_left_cancel h'
  obtain ⟨M, hMT, hMrel, hpM⟩ :=
    exists_relIndex_two_notMem_of_fixed (T := (P : Subgroup E)) hab hx3 hxN hpT hp1 hpx hFhyp
  exact false_of_fixed_involution hE P hab hpT hp2 hfix hMT hMrel hpM

end CFSG.GroupTheory.SmallFixedTwoGroup
