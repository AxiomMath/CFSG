module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69S

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

theorem card_inf_mul_relIndex {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.card_mul_index (H.subgroupOf K)
  have h2 : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv
  rw [h2] at h1
  exact h1

namespace Hyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}
  (h : Hyp69 L z t T₀ E Q x β B S)

include h

theorem card_cent_z : Nat.card ↥(centralizer ({z} : Set G)) = 2 * Nat.card L := by
  have hc := h.conf.cfg
  let f : ↥L × ↥(zpowers z) → ↥(centralizer ({z} : Set G)) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), by rw [hc.cent_eq]; exact mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hab' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
    have hu : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [hab']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmemL : (a' : G)⁻¹ * (a : G) ∈ L := mul_mem (inv_mem a'.2) a.2
    have hmemZ : (a' : G)⁻¹ * (a : G) ∈ zpowers z := by
      rw [hu]; exact mul_mem b'.2 (inv_mem b.2)
    have h1 : (a' : G)⁻¹ * (a : G) = 1 := (Subgroup.disjoint_def.1 hc.disjoint) hmemL hmemZ
    have ha : a = a' := Subtype.ext (by
      calc (a : G) = (a' : G) * ((a' : G)⁻¹ * (a : G)) := by group
        _ = (a' : G) := by rw [h1, mul_one])
    subst ha
    have hb : (b : G) = (b' : G) := mul_left_cancel hab'
    exact Prod.ext rfl (Subtype.ext hb)
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hcC⟩
    rw [hc.cent_eq] at hcC
    obtain ⟨l, hl, a, ha, hca⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 hc.z_cent) hcC
    exact ⟨(⟨l, hl⟩, ⟨a, ha⟩), Subtype.ext hca.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hc.z_sq
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hc.z_ne
  rw [hord]
  exact Nat.mul_comm _ _

theorem cent_z_card_le {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({z} : Set G)) : Nat.card P ≤ 2 * Nat.card T₀ := by
  have hc := h.conf.cfg
  obtain ⟨m, hm, hLm⟩ := hc.T₀_odd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hc.T₀_pgroup
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card ↥(centralizer ({z} : Set G)) :=
    Subgroup.card_dvd_of_le hPC
  rw [h.card_cent_z, hLm, hk, hj] at hdvd
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.coprime_two_left).2 hm
  have hdvd' : 2 ^ j ∣ 2 ^ (k + 1) := by
    have : 2 ^ j ∣ 2 ^ (k + 1) * m := by
      convert hdvd using 1
      ring
    exact hcop.dvd_of_dvd_mul_right this
  have hjk : j ≤ k + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd'
  rw [hj, hk, ← pow_succ']
  exact Nat.pow_le_pow_right (by norm_num) hjk

theorem relIndex_cent_z_odd {Rs : Subgroup G} (hRs : IsPGroup 2 Rs)
    (hcard : 2 * Nat.card T₀ ≤ Nat.card ↥(Rs ⊓ centralizer ({z} : Set G))) :
    ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  have hc := h.conf.cfg
  obtain ⟨m, hm, hLm⟩ := hc.T₀_odd
  have hP2 : IsPGroup 2 ↥(Rs ⊓ centralizer ({z} : Set G)) := hRs.to_le inf_le_left
  have hle := h.cent_z_card_le hP2 inf_le_right
  have hP : Nat.card ↥(Rs ⊓ centralizer ({z} : Set G)) = 2 * Nat.card T₀ := le_antisymm hle hcard
  have h1 := card_inf_mul_relIndex Rs (centralizer ({z} : Set G))
  rw [h.card_cent_z, hLm, hP] at h1
  have hT : 0 < Nat.card T₀ := Nat.card_pos
  have h2 : Rs.relIndex (centralizer ({z} : Set G)) = m := by
    have : 2 * Nat.card T₀ * Rs.relIndex (centralizer ({z} : Set G)) =
        2 * Nat.card T₀ * m := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  rw [h2]
  exact (Nat.not_even_iff_odd.2 hm) ∘ even_iff_two_dvd.2

end Hyp69

end CFSG.EvenSporadicStandard.Fin76b
