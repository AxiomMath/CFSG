module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H69S
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma620A

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem T_sylow : ∃ Q : Sylow 2 ↥(centralizer ({z} : Set G)),
    (Q : Subgroup ↥(centralizer ({z} : Set G))) = T.subgroupOf (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := h.oe.cfg
  have hT2 : IsPGroup 2 (T.subgroupOf (centralizer ({z} : Set G))) :=
    hc.T_pgroup.comap_subtype (K := centralizer ({z} : Set G))
  obtain ⟨Q, hTQ⟩ := IsPGroup.exists_le_sylow hT2
  refine ⟨Q, le_antisymm ?_ hTQ⟩
  have hmap : (Q : Subgroup ↥(centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype ≤ T := by
    refine hc.T_max _ ?_ (Q.isPGroup'.map _) ?_
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    · intro x hx
      have hxK : x ∈ centralizer ({z} : Set G) := hc.T_le hx
      have hmem : (⟨x, hxK⟩ : ↥(centralizer ({z} : Set G))) ∈
          T.subgroupOf (centralizer ({z} : Set G)) := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hTQ hmem, rfl⟩
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  exact hmap (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)

theorem card_T : Nat.card T = 2 ^ (Nat.card ↥(centralizer ({z} : Set G))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.T_sylow
  have h1 : Nat.card ↥(T.subgroupOf (centralizer ({z} : Set G))) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.oe.cfg.T_le).toEquiv
  rw [← h1, ← hQ]
  exact Sylow.card_eq_multiplicity Q

theorem cent_z_card_le {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({z} : Set G)) : Nat.card P ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK0 : Nat.card ↥(centralizer ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card ↥(centralizer ({z} : Set G)) := Subgroup.card_dvd_of_le hPC
  rw [hn] at hdvd ⊢
  have hle : n ≤ (Nat.card ↥(centralizer ({z} : Set G))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).1 hdvd
  rw [h.card_T]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem relIndex_cent_z_odd {Rs : Subgroup G} (hRs : IsPGroup 2 Rs)
    (hcard : Nat.card T ≤ Nat.card ↥(Rs ⊓ centralizer ({z} : Set G))) :
    ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(Rs ⊓ centralizer ({z} : Set G)) := hRs.to_le inf_le_left
  have hle := h.cent_z_card_le hP2 inf_le_right
  have hP : Nat.card ↥(Rs ⊓ centralizer ({z} : Set G)) = Nat.card T := le_antisymm hle hcard
  have h1 := card_inf_mul_relIndex Rs (centralizer ({z} : Set G))
  rw [hP] at h1
  have hK0 : Nat.card ↥(centralizer ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hT0 : 0 < Nat.card T := Nat.card_pos
  have hdiv : Nat.card ↥(centralizer ({z} : Set G)) /
      2 ^ (Nat.card ↥(centralizer ({z} : Set G))).factorization 2 =
        Rs.relIndex (centralizer ({z} : Set G)) := by
    rw [← h.card_T, ← h1]
    exact Nat.mul_div_cancel_left _ hT0
  have hcop := Nat.coprime_ordCompl Nat.prime_two hK0
  rw [hdiv] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
