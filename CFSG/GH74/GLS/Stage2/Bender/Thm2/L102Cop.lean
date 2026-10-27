module

public import Mathlib.GroupTheory.Sylow
import CFSG.Walter.W67.Section5.P56AbHallTools

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem coprime_card_of_two {T O : Subgroup G} (hT2 : IsPGroup 2 T)
    (hO : Odd (Nat.card O)) : Nat.Coprime (Nat.card T) (Nat.card O) := by
  obtain ⟨n, hn⟩ := hT2.exists_card_dvd_pow
  exact Nat.Coprime.coprime_dvd_left hn ((Nat.coprime_two_left.mpr hO).pow_left n)

private theorem isHallSubgroup_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (P : Sylow p H) : CFSG.IsHallSubgroup ({⟨p, hp⟩} : Set Nat.Primes) (P : Subgroup H) := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.isHallSubgroup_of _ _ (fun r hr => ?_) (fun r hr hdvd => ?_)
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hk] at hr
    exact Set.mem_singleton_iff.mpr (Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq r.2 hp).mp (r.2.dvd_of_dvd_pow hr)))
  · have hrq : r = ⟨p, hp⟩ := hr
    rw [hrq] at hdvd
    exact P.not_dvd_index hdvd

private theorem isHallSubgroup_of_maximal {O V : Subgroup G} {p : ℕ} (hp : p.Prime) (hVO : V ≤ O)
    (hVp : IsPGroup p V) (hVmax : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V) :
    CFSG.IsHallSubgroup ({⟨p, hp⟩} : Set Nat.Primes) (V.subgroupOf O) := by
  have : Fact p.Prime := ⟨hp⟩
  have hVo : IsPGroup p (V.subgroupOf O) := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVO).symm
  obtain ⟨Q, hVQ⟩ := hVo.exists_le_sylow
  have hQV : (Q : Subgroup O).map O.subtype = V := by
    refine hVmax _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map O.subtype) ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hVO]
    exact Subgroup.map_mono hVQ
  have hQ : (Q : Subgroup O) = V.subgroupOf O := by
    rw [← hQV]
    exact (Subgroup.comap_map_eq_self_of_injective O.subtype_injective _).symm
  rw [← hQ]
  exact isHallSubgroup_sylow hp Q

private theorem isPGroup_and_maximal_of_isHallSubgroup {O S : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hSO : S ≤ O) (hS : CFSG.IsHallSubgroup ({⟨p, hp⟩} : Set Nat.Primes) (S.subgroupOf O)) :
    IsPGroup p S ∧ ∀ W : Subgroup G, W ≤ O → IsPGroup p W → S ≤ W → W = S := by
  have : Fact p.Prime := ⟨hp⟩
  have hSp : IsPGroup p S :=
    (CFSG.isPGroup_of_isPiSubgroup_singleton (q := ⟨p, hp⟩) hS.isPiSubgroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSO)
  refine ⟨hSp, fun W hWO hW hSW => ?_⟩
  have hWo : IsPGroup p (W.subgroupOf O) := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWO).symm
  obtain ⟨Q, hWQ⟩ := hWo.exists_le_sylow
  have hSQ : S.subgroupOf O ≤ (Q : Subgroup O) := (Subgroup.comap_mono hSW).trans hWQ
  have hEq : S.subgroupOf O = (Q : Subgroup O) := hS.eq_of_le (isHallSubgroup_sylow hp Q) hSQ
  have hWS : W.subgroupOf O ≤ S.subgroupOf O := hEq ▸ hWQ
  refine le_antisymm (fun w hw => ?_) hSW
  exact hWS (show (⟨w, hWO hw⟩ : O) ∈ W.subgroupOf O from hw)

theorem exists_invariant_sylow_ge {O T P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hO : Odd (Nat.card O)) (hT2 : IsPGroup 2 T) (hTO : T ≤ normalizer (O : Set G))
    (hPO : P ≤ O) (hP : IsPGroup p P) (hTP : T ≤ normalizer (P : Set G)) :
    ∃ V : Subgroup G, V ≤ O ∧ IsPGroup p V ∧ P ≤ V ∧ T ≤ normalizer (V : Set G) ∧
      ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V := by
  obtain ⟨S, hSO, hSHall, hTS, hPS⟩ := CFSG.Walter.W67.P56Ab.exists_hall_invariant
    (π := {⟨p, hp⟩}) hTO (CFSG.Walter.W67.P56Ab.isSolvable_of_odd hO)
    (coprime_card_of_two hT2 hO) hPO
    (CFSG.isPiSubgroup_singleton_of_isPGroup (q := ⟨p, hp⟩) hP) hTP
  obtain ⟨hSp, hSmax⟩ := isPGroup_and_maximal_of_isHallSubgroup hp hSO hSHall
  exact ⟨S, hSO, hSp, hPS, hTS, hSmax⟩

theorem exists_centralizer_conj {O U V V' : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hO : Odd (Nat.card O)) (hU2 : IsPGroup 2 U) (hUO : U ≤ normalizer (O : Set G))
    (hV : V ≤ O) (hVp : IsPGroup p V)
    (hVmax : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V ≤ W → W = V)
    (hUV : U ≤ normalizer (V : Set G)) (hV' : V' ≤ O) (hV'p : IsPGroup p V')
    (hV'max : ∀ W : Subgroup G, W ≤ O → IsPGroup p W → V' ≤ W → W = V')
    (hUV' : U ≤ normalizer (V' : Set G)) :
    ∃ c ∈ O ⊓ centralizer (U : Set G), ∀ x : G, x ∈ V' ↔ c⁻¹ * x * c ∈ V := by
  obtain ⟨c, hc, hcV⟩ := CFSG.Walter.W67.P56Ab.exists_conj_hall_invariant
    (π := {⟨p, hp⟩}) hUO (CFSG.Walter.W67.P56Ab.isSolvable_of_odd hO)
    (coprime_card_of_two hU2 hO) hV hV' (isHallSubgroup_of_maximal hp hV hVp hVmax)
    (isHallSubgroup_of_maximal hp hV' hV'p hV'max) hUV hUV'
  refine ⟨c, hc, fun x => ?_⟩
  rw [hcV, Subgroup.mem_map_equiv]
  rfl

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
