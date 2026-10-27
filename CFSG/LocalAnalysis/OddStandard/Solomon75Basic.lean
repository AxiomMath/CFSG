module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def oddCoreOf (H : Subgroup G) : Subgroup G := (pPrimeCore 2 H).map H.subtype

theorem oddCoreOf_le (H : Subgroup G) : oddCoreOf H ≤ H := by
  rintro _ ⟨h, -, rfl⟩
  exact h.2

theorem oddCoreOf_subgroupOf (H : Subgroup G) : (oddCoreOf H).subgroupOf H = pPrimeCore 2 H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem le_normalizer_oddCoreOf (H : Subgroup G) : H ≤ normalizer (oddCoreOf H : Set G) := by
  have hn : ((oddCoreOf H).subgroupOf H).Normal := by
    rw [oddCoreOf_subgroupOf]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer (oddCoreOf_le H)).mp hn

theorem odd_card_oddCoreOf [Finite G] (H : Subgroup G) : Odd (Nat.card (oddCoreOf H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  have hcard : Nat.card (oddCoreOf H) = Nat.card (pPrimeCore 2 H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [hcard]
  exact Nat.coprime_two_left.mp hc

theorem le_oddCoreOf_of_normalized [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hn : H ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf H := by
  have hnorm : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hn
  have hcard : Nat.card (N.subgroupOf H) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf H)) := by
    rw [hcard]
    exact Nat.coprime_two_left.mpr hodd
  have hle : N.subgroupOf H ≤ pPrimeCore 2 H := le_sSup ⟨hnorm, hcop⟩
  have := Subgroup.map_mono (f := H.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at this

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {x : G} (hx : x ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp hx

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ normalizer (H : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr h

theorem mem_normalizer_commutator {H K : Subgroup G} {x : G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]

theorem mem_normalizer_sup {H K : Subgroup G} {x : G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]

theorem mem_normalizer_inf {H K : Subgroup G} {x : G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, map_conj_eq_of_mem_normalizer hH,
    map_conj_eq_of_mem_normalizer hK]

abbrev cen (b : G) : Subgroup G := centralizer ({b} : Set G)

section Elementary

variable {B A : Subgroup G}

theorem comm_of_sq_eq_one (hB2 : ∀ b ∈ B, b ^ 2 = 1) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    x * y = y * x := by
  have hx2 : x * x = 1 := by simpa [sq] using hB2 x hx
  have hy2 : y * y = 1 := by simpa [sq] using hB2 y hy
  have hxy2 : x * y * (x * y) = 1 := by simpa [sq] using hB2 _ (B.mul_mem hx hy)
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have h : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy2).symm
  rw [mul_inv_rev, hxi, hyi] at h
  exact h

theorem mem_cen_of_mem (hB2 : ∀ b ∈ B, b ^ 2 = 1) {b x : G} (hb : b ∈ B) (hx : x ∈ B) :
    x ∈ cen b := by
  rw [mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact comm_of_sq_eq_one hB2 hb hx

theorem isPGroup_two_of_sq (hB2 : ∀ b ∈ B, b ^ 2 = 1) : IsPGroup 2 B := by
  intro x
  exact ⟨1, Subtype.ext (by simpa using hB2 x x.2)⟩

theorem centralizer_le_cen {b : G} (hb : b ∈ A) : centralizer (A : Set G) ≤ cen b := by
  intro c hc
  rw [mem_centralizer_iff] at hc ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hc b hb

end Elementary

section Finite

variable [Finite G] {A : Subgroup G}

theorem cen_inf_oddCore_le {a : G} (ha : a ∈ A) :
    centralizer (A : Set G) ⊓ oddCoreOf (cen a) ≤ oddCoreOf (centralizer (A : Set G)) := by
  apply le_oddCoreOf_of_normalized inf_le_left
  · intro c hc
    apply mem_normalizer_inf
    · exact Subgroup.le_normalizer hc
    · exact le_normalizer_oddCoreOf (cen a) (centralizer_le_cen ha hc)
  · exact (odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

end Finite

end CFSG.OddStandard.Solomon75
