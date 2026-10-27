module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.OddCore

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_singleton_eq_map_sylow {C : Subgroup G} {t : G} (htC : t ∈ C)
    (hN : centralizer ({t} : Set G) ≤ normalizer (C : Set G))
    (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (Q : Sylow 2 C) (hQ : IsCyclic (Q : Subgroup C)) (htQ : (⟨t, htC⟩ : C) ∈ (Q : Subgroup C)) :
    C ⊓ centralizer ({t} : Set G) = (Q : Subgroup C).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hmul, -, -⟩ := CFSG.cyclic_sylow_normal_odd_complement Q hQ
  have hbot := map_pPrimeCore_inf_eq_bot hN hcore
  have hcommQ : ∀ q ∈ (Q : Subgroup C), q * ⟨t, htC⟩ = ⟨t, htC⟩ * q := fun q hq => by
    have := hQ.isMulCommutative.is_comm.comm (⟨q, hq⟩ : (Q : Subgroup C)) ⟨_, htQ⟩
    exact congrArg Subtype.val this
  have hQc : ∀ q ∈ (Q : Subgroup C), (q : G) ∈ centralizer ({t} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hcommQ q hq))
  refine le_antisymm ?_ ?_
  · rintro c ⟨hcC, hcH⟩
    have hmem : (⟨c, hcC⟩ : C) ∈ ((CFSG.pPrimeCore 2 C : Subgroup C) : Set C) *
        (Q : Set C) := by
      rw [hmul]
      exact Set.mem_univ _
    obtain ⟨k, hk, q, hq, hkq⟩ := Set.mem_mul.1 hmem
    have hkc : (k : G) * (q : G) = c := congrArg Subtype.val hkq
    have hkH : (k : G) ∈ centralizer ({t} : Set G) := by
      have : (k : G) = c * (q : G)⁻¹ := by rw [← hkc]; group
      rw [this]
      exact (centralizer ({t} : Set G)).mul_mem hcH
        ((centralizer ({t} : Set G)).inv_mem (hQc q hq))
    have hk1 : (k : G) = 1 := by
      have hmem' : (k : G) ∈ (CFSG.pPrimeCore 2 C).map C.subtype ⊓ centralizer ({t} : Set G) :=
        ⟨⟨k, hk, rfl⟩, hkH⟩
      rw [hbot, mem_bot] at hmem'
      exact hmem'
    refine ⟨q, hq, ?_⟩
    rw [← hkc, hk1, one_mul]
    rfl
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨q.2, hQc q hq⟩

theorem isCyclic_of_isPGroup_of_cyclicSylow {C : Subgroup G}
    (hS : ∃ S : Sylow 2 C, IsCyclic (S : Subgroup C)) {X : Subgroup C} (hX : IsPGroup 2 X) :
    IsCyclic X := by
  obtain ⟨S₀, hS₀⟩ := hS
  obtain ⟨S, hXS⟩ := hX.exists_le_sylow
  have hSc : IsCyclic (S : Subgroup C) := by
    let f : S₀ ≃* S := Sylow.equiv S₀ S
    exact isCyclic_of_surjective f.toMonoidHom f.surjective
  exact Subgroup.isCyclic_of_le hXS

end CFSG.EvenSporadicStandard.ThStd
