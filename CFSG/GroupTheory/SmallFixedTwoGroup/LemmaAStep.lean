module

public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACenterSmall
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAChar
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaACentQuot
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAIndex
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup1

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup
open CFSG.GH74.GLS.Stage1.Thm6.Sec13

private theorem mem_zpowers_iff_of_mul_self_eq_one {T : Type*} [Group T] {z s : T}
    (hz2 : z * z = 1) : s ∈ zpowers z ↔ s = 1 ∨ s = z :=
  mem_zpowers_involution hz2

private theorem mul_comm_of_normal_zpowers {T : Type*} [Group T] {z : T} [(zpowers z).Normal]
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (g : T) : g * z = z * g := by
  have hconj : g * z * g⁻¹ ∈ zpowers z :=
    (inferInstance : (zpowers z).Normal).conj_mem z (mem_zpowers z) g
  rcases (mem_zpowers_iff_of_mul_self_eq_one hz2).1 hconj with h | h
  · exfalso
    have hz : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h]
        _ = 1 := by group
    exact hz1 hz
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h]

private theorem mem_center_of_normal_zpowers {T : Type*} [Group T] {z : T} [(zpowers z).Normal]
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : z ∈ center T := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact mul_comm_of_normal_zpowers hz2 hz1 g

section Step

variable {T : Type*} [Group T] [Finite T] {z : T} [(zpowers z).Normal]

theorem card_quotient_zpowers (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (T ⧸ zpowers z) * 2 = Nat.card T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  have hcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers z)
  rw [hcard] at h
  exact h.symm

theorem mk_ne_one_of_ne {s : T} (hz2 : z * z = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) :
    (QuotientGroup.mk s : T ⧸ zpowers z) ≠ 1 := by
  intro h
  rcases (mem_zpowers_iff_of_mul_self_eq_one hz2).1 ((QuotientGroup.eq_one_iff s).1 h) with
    h1 | hz
  · exact hs1 h1
  · exact hsz hz

theorem mk_notMem_center (h32 : 32 ≤ Nat.card T) (hz2 : z * z = 1) (hz1 : z ≠ 1) {s : T}
    (h8 : Nat.card (centralizer ({s} : Set T)) ≤ 8) :
    (QuotientGroup.mk s : T ⧸ zpowers z) ∉ center (T ⧸ zpowers z) := by
  intro hmem
  have hcomm : ∀ g : T, g * s * g⁻¹ = s ∨ g * s * g⁻¹ = z * s := by
    intro g
    have hcen := (Subgroup.mem_center_iff.mp hmem) (QuotientGroup.mk g)
    have heq : (QuotientGroup.mk s : T ⧸ zpowers z)
        = QuotientGroup.mk (g * s * g⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcen]
      group
    have hmem' : s⁻¹ * (g * s * g⁻¹) ∈ zpowers z := (QuotientGroup.eq).1 heq
    rcases (mem_zpowers_iff_of_mul_self_eq_one hz2).1 hmem' with h1 | hz
    · left
      calc g * s * g⁻¹ = s * (s⁻¹ * (g * s * g⁻¹)) := by group
        _ = s * 1 := by rw [h1]
        _ = s := by group
    · right
      calc g * s * g⁻¹ = s * (s⁻¹ * (g * s * g⁻¹)) := by group
        _ = s * z := by rw [hz]
        _ = z * s := mul_comm_of_normal_zpowers hz2 hz1 s
  have hidx : (centralizer ({s} : Set T)).index ≤ 2 := index_centralizer_le_two hcomm
  have hle : Nat.card (centralizer ({s} : Set T)) * (centralizer ({s} : Set T)).index ≤ 16 := by
    have := Nat.mul_le_mul h8 hidx
    omega
  have hcard : Nat.card T ≤ 16 := by
    rw [← Subgroup.card_mul_index (centralizer ({s} : Set T))]
    exact hle
  omega

theorem mk_centralizer_comm (hT : IsPGroup 2 T) (h32 : 32 ≤ Nat.card T) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {s : T} (hs : s * s = 1) (hs1 : s ≠ 1) (hsz : s ∉ center T)
    (h8 : Nat.card (centralizer ({s} : Set T)) ≤ 8) :
    ∀ a ∈ centralizer ({(QuotientGroup.mk s : T ⧸ zpowers z)} : Set (T ⧸ zpowers z)),
      ∀ b ∈ centralizer ({(QuotientGroup.mk s : T ⧸ zpowers z)} : Set (T ⧸ zpowers z)),
        a * b = b * a := by
  let R := T ⧸ zpowers z
  let sbar : R := QuotientGroup.mk s
  let C : Subgroup R := centralizer ({sbar} : Set R)
  have hR : IsPGroup 2 R := hT.to_quotient (zpowers z)
  have hz_center : z ∈ center T := mem_center_of_normal_zpowers hz2 hz1
  have hsz' : s ≠ z := fun h => hsz (by rw [h]; exact hz_center)
  have hsbar : sbar * sbar = 1 := by
    change (QuotientGroup.mk s : T ⧸ zpowers z) * QuotientGroup.mk s = 1
    rw [← QuotientGroup.mk_mul, hs, QuotientGroup.mk_one]
  have hsbar1 : sbar ≠ 1 := by
    change (QuotientGroup.mk s : T ⧸ zpowers z) ≠ 1
    exact mk_ne_one_of_ne hz2 hs1 hsz'
  by_contra hnc
  have hnc' : ¬ ∀ a b : ↥C, a * b = b * a := by
    intro hc
    apply hnc
    intro a ha b hb
    have := congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
    simpa using this
  have hZ : Nat.card (center ↥C) ≤ 2 :=
    card_center_le_two_of_not_commutative (by
      have hcq := card_centralizer_quotient_le (zpowers z) s
      change Nat.card ↥C ≤ 8
      exact hcq.trans h8) hnc'
  have hsbar_center : sbar ∈ center R :=
    mem_center_of_card_center_centralizer_le_two hR hsbar hsbar1 (by
      change Nat.card (center (centralizer ({sbar} : Set R))) ≤ 2
      exact hZ)
  have hnot : (QuotientGroup.mk s : T ⧸ zpowers z) ∉ center (T ⧸ zpowers z) :=
    mk_notMem_center h32 hz2 hz1 h8
  exact hnot (by simpa only [sbar, R] using hsbar_center)

theorem lift_index_two (hz : z ∈ center T) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (h16 : 16 ≤ Nat.card T) {M : Subgroup (T ⧸ zpowers z)} (hM : M.index = 2)
    (hcen : ∀ u ∈ M, u * u = 1 → u ≠ 1 →
      16 ≤ Nat.card (centralizer ({u} : Set (T ⧸ zpowers z)))) :
    ∃ M' : Subgroup T, M'.index = 2 ∧ ∀ u ∈ M', u * u = 1 → u ≠ 1 →
      16 ≤ Nat.card (centralizer ({u} : Set T)) := by
  let f : T →* T ⧸ zpowers z := QuotientGroup.mk' (zpowers z)
  let M' : Subgroup T := M.comap f
  refine ⟨M', ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective M (f := f)
      (QuotientGroup.mk'_surjective (zpowers z)), hM]
  · intro u hu hu2 hu1
    by_cases huz : u = z
    · rw [huz]
      have htop : centralizer ({z} : Set T) = ⊤ := by
        refine le_antisymm le_top ?_
        intro x _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp hz) x
      rw [htop, Subgroup.card_top]
      exact h16
    · have hmu : (QuotientGroup.mk u : T ⧸ zpowers z) ∈ M := by
        have hf : f u ∈ M := (Subgroup.mem_comap).1 hu
        simpa only [f, QuotientGroup.mk'_apply] using hf
      have hmu2 : (QuotientGroup.mk u : T ⧸ zpowers z) * QuotientGroup.mk u = 1 := by
        rw [← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
      have hmu1 : (QuotientGroup.mk u : T ⧸ zpowers z) ≠ 1 :=
        mk_ne_one_of_ne hz2 hu1 huz
      have h1 := hcen (QuotientGroup.mk u) hmu hmu2 hmu1
      have h2 := card_centralizer_quotient_le (zpowers z) u
      exact h1.trans h2

end Step

end CFSG.GroupTheory.SmallFixedTwoGroup
