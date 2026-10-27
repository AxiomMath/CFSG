module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Open
open scoped Pointwise

section Sylow

variable {C : Type*} [Group C] [Finite C]

theorem exists_sylow_eq_zpowers (hS : ∀ S : Sylow 2 C, Nat.card S = 2) {t : C}
    (ht : orderOf t = 2) : ∃ Q : Sylow 2 C, (Q : Subgroup C) = zpowers t := by
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_zpowers, ht, pow_one]) : IsPGroup 2 (zpowers t)).exists_le_sylow
  exact ⟨Q, (eq_of_le_of_card_ge hQ (by rw [Nat.card_zpowers, ht, hS Q])).symm⟩

theorem isComplement'_pPrimeCore_sylow (S : Sylow 2 C) (hS : IsCyclic S) :
    (CFSG.pPrimeCore 2 C).IsComplement' (S : Subgroup C) := by
  obtain ⟨-, hmul, hinf, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hS
  have hmul' : ((CFSG.pPrimeCore 2 C : Subgroup C) : Set C) * ((S : Subgroup C) : Set C) =
      Set.univ := hmul
  exact isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hinf) hmul'

theorem isComplement'_pPrimeCore_zpowers (hS : ∀ S : Sylow 2 C, Nat.card S = 2) {t : C}
    (ht : orderOf t = 2) : (CFSG.pPrimeCore 2 C).IsComplement' (zpowers t) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_zpowers hS ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← hQ]
  exact isComplement'_pPrimeCore_sylow Q (isCyclic_of_prime_card (hS Q))

theorem exists_normal_odd_index_two (hS : ∀ S : Sylow 2 C, Nat.card S = 2) :
    ∃ K : Subgroup C, K.Normal ∧ Odd (Nat.card K) ∧ K.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  obtain ⟨-, -, -, ⟨hn, hodd, hidx, -⟩, -⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement S (isCyclic_of_prime_card (hS S))
  exact ⟨_, hn, hodd, hidx.trans (hS S)⟩

end Sylow

section OddCore

variable {G : Type*} [Group G]

theorem conj_mem_map_pPrimeCore {C : Subgroup G} {g : G}
    (hg : g ∈ normalizer (C : Set G)) {x : G}
    (hx : x ∈ (CFSG.pPrimeCore 2 C).map C.subtype) :
    g * x * g⁻¹ ∈ (CFSG.pPrimeCore 2 C).map C.subtype := by
  obtain ⟨k, hk, rfl⟩ := hx
  let φ : MulAut C := C.normalizerMonoidHom ⟨g, hg⟩
  have hφ : φ k ∈ CFSG.pPrimeCore 2 C := by
    have h1 := Subgroup.characteristic_iff_comap_eq.1
      (CFSG.pPrimeCore_characteristic (p := 2) (G := C)) φ
    rw [← h1] at hk
    exact hk
  exact ⟨φ k, hφ, rfl⟩

variable [Finite G]

theorem map_pPrimeCore_inf_eq_bot {C H : Subgroup G} (hHC : H ≤ normalizer (C : Set G))
    (hcore : standardComponentOddCore H = ⊥) :
    (CFSG.pPrimeCore 2 C).map C.subtype ⊓ H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := (CFSG.pPrimeCore 2 C).map C.subtype with hK'
  set D := K' ⊓ H with hD
  have hDodd : Odd (Nat.card D) := by
    have h1 : Odd (Nat.card K') := by
      rw [hK', Subgroup.card_map_of_injective C.subtype_injective]
      exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
    exact h1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hDn : (D.subgroupOf H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact ⟨conj_mem_map_pPrimeCore (hHC h.2) hn.1,
      H.mul_mem (H.mul_mem h.2 hn.2) (H.inv_mem h.2)⟩
  have hle : D.subgroupOf H ≤ standardComponentOddCore H :=
    le_sSup ⟨hDn, by rwa [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : D ≤ H)).toEquiv]⟩
  rw [hcore, le_bot_iff] at hle
  refine eq_bot_iff.2 fun x hx => ?_
  have hmem : (⟨x, hx.2⟩ : H) ∈ D.subgroupOf H := hx
  rw [hle, mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem inf_centralizer_singleton_eq_map_sylow {C : Subgroup G} {t : G} (htC : t ∈ C)
    (hN : centralizer ({t} : Set G) ≤ normalizer (C : Set G))
    (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 C) (hS : IsCyclic S) (htS : (⟨t, htC⟩ : C) ∈ S) :
    C ⊓ centralizer ({t} : Set G) = (S : Subgroup C).map C.subtype := by
  set H := centralizer ({t} : Set G) with hH
  have hcompl := isComplement'_pPrimeCore_sylow S hS
  have hbot := map_pPrimeCore_inf_eq_bot hN hcore
  have hSH : ∀ s ∈ (S : Subgroup C), (s : G) ∈ H := fun s hs => by
    have : IsCyclic (S : Subgroup C) := hS
    have h1 := IsCyclic.isMulCommutative.is_comm.comm (⟨s, hs⟩ : (S : Subgroup C))
      ⟨⟨t, htC⟩, htS⟩
    exact mem_centralizer_singleton_iff.2 (congrArg (fun x : (S : Subgroup C) => ((x : C) : G)) h1)
  refine le_antisymm ?_ ?_
  · rintro c ⟨hcC, hcH⟩
    have hmem : (⟨c, hcC⟩ : C) ∈ ((CFSG.pPrimeCore 2 C : Subgroup C) : Set C) *
        ((S : Subgroup C) : Set C) := by
      rw [hcompl.mul_eq]
      exact Set.mem_univ _
    obtain ⟨k, hk, s, hs, hks⟩ := Set.mem_mul.1 hmem
    have hkc : (k : G) * (s : G) = c := congrArg Subtype.val hks
    have hkH : (k : G) ∈ H := by
      have : (k : G) = c * (s : G)⁻¹ := by rw [← hkc]; group
      rw [this]
      exact H.mul_mem hcH (H.inv_mem (hSH s hs))
    have hk1 : (k : G) = 1 := by
      have hkK : (k : G) ∈ (CFSG.pPrimeCore 2 C).map C.subtype := ⟨k, hk, rfl⟩
      have hmem' : (k : G) ∈ (CFSG.pPrimeCore 2 C).map C.subtype ⊓ H := ⟨hkK, hkH⟩
      rw [hbot, mem_bot] at hmem'
      exact hmem'
    exact ⟨s, hs, by rw [← hkc, hk1, one_mul]; rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s.2, hSH s hs⟩

theorem inf_centralizer_singleton_eq_zpowers {C : Subgroup G} {t : G}
    (htC : t ∈ C) (ht2 : orderOf t = 2)
    (hN : centralizer ({t} : Set G) ≤ normalizer (C : Set G))
    (hcore : standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hS : ∀ S : Sylow 2 C, Nat.card S = 2) :
    C ⊓ centralizer ({t} : Set G) = zpowers t := by
  have ht₀ : orderOf (⟨t, htC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_zpowers hS ht₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htQ : (⟨t, htC⟩ : C) ∈ (Q : Subgroup C) := by
    rw [hQ]
    exact mem_zpowers _
  rw [inf_centralizer_singleton_eq_map_sylow htC hN hcore Q (isCyclic_of_prime_card (hS Q)) htQ,
    hQ, MonoidHom.map_zpowers]
  rfl

end OddCore

end CFSG.EvenSporadicStandard
