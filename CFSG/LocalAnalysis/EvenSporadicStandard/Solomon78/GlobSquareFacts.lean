module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G]

structure SylowSquareFacts (K S : Subgroup G) (u d : G) : Prop where
  S_le : S ≤ K
  S_card : Nat.card S = 2 ^ (Nat.card K).factorization 2
  d_mem : d ∈ K
  d_sq : d * d = 1
  d_ne_one : d ≠ 1
  d_ne_u : d ≠ u
  d_comm : ∀ s ∈ S, s * d = d * s
  center_inv : ∀ s ∈ S, s * s = 1 → (∀ x ∈ S, s * x = x * s) →
    s = 1 ∨ s = u ∨ s = d ∨ s = u * d
  d_nonsq : ∀ s ∈ S, s * s ≠ d
  ud_sq : ∃ s ∈ S, s * s = u * d

structure SquareFacts (K S : Subgroup G) (u d : G) : Prop extends SylowSquareFacts K S u d where
  u_mem : u ∈ K
  u_central : ∀ k ∈ K, k * u = u * k
  u_sq : u * u = 1
  central_inv : ∀ z ∈ K, z * z = 1 → (∀ y ∈ K, z * y = y * z) → z = 1 ∨ z = u

theorem SquareFacts.map {H : Type} [Group H] {K S : Subgroup G} {u d : G}
    (h : SquareFacts K S u d) (ι : G →* H) (hι : Function.Injective ι) :
    SquareFacts (K.map ι) (S.map ι) (ι u) (ι d) where
  u_mem := mem_map_of_mem ι h.u_mem
  u_central := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, h.u_central k hk]
  u_sq := by rw [← map_mul, h.u_sq, map_one]
  central_inv := by
    rintro _ ⟨z, hz, rfl⟩ hzz hzc
    have h1 : z * z = 1 := hι (by rw [map_mul, hzz, map_one])
    have h2 : ∀ y ∈ K, z * y = y * z := fun y hy =>
      hι (by rw [map_mul, map_mul]; exact hzc _ (mem_map_of_mem ι hy))
    rcases h.central_inv z hz h1 h2 with e | e
    · left
      rw [e, map_one]
    · right
      rw [e]
  S_le := Subgroup.map_mono h.S_le
  S_card := by
    rw [Subgroup.card_map_of_injective hι, Subgroup.card_map_of_injective hι]
    exact h.S_card
  d_mem := mem_map_of_mem ι h.d_mem
  d_sq := by rw [← map_mul, h.d_sq, map_one]
  d_ne_one := fun e => h.d_ne_one (hι (by rw [e, map_one]))
  d_ne_u := fun e => h.d_ne_u (hι e)
  d_comm := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, h.d_comm s hs]
  center_inv := by
    rintro _ ⟨s, hs, rfl⟩ hss hsc
    have h1 : s * s = 1 := hι (by rw [map_mul, hss, map_one])
    have h2 : ∀ x ∈ S, s * x = x * s := fun x hx =>
      hι (by rw [map_mul, map_mul]; exact hsc _ (mem_map_of_mem ι hx))
    rcases h.center_inv s hs h1 h2 with e | e | e | e
    · left
      rw [e, map_one]
    · right; left
      rw [e]
    · right; right; left
      rw [e]
    · right; right; right
      rw [e, map_mul]
  d_nonsq := by
    rintro _ ⟨s, hs, rfl⟩ e
    exact h.d_nonsq s hs (hι (by rw [map_mul]; exact e))
  ud_sq := by
    obtain ⟨s, hs, e⟩ := h.ud_sq
    exact ⟨ι s, mem_map_of_mem ι hs, by rw [← map_mul, e, map_mul]⟩

theorem SquareFacts.comap {H : Type} [Group H] {K S : Subgroup G} {u d : G}
    (h : SquareFacts K S u d) (ι : H →* G) (hι : Function.Injective ι) (hK : K ≤ ι.range)
    {u' d' : H} (hu : ι u' = u) (hd : ι d' = d) :
    SquareFacts (K.comap ι) (S.comap ι) u' d' := by
  have hK' : (K.comap ι).map ι = K := Subgroup.map_comap_eq_self hK
  have hS' : (S.comap ι).map ι = S := Subgroup.map_comap_eq_self (h.S_le.trans hK)
  have hlift : ∀ {x : G}, x ∈ K → ∃ y, ι y = x ∧ y ∈ K.comap ι := fun {x} hx => by
    obtain ⟨y, hy⟩ := hK hx
    exact ⟨y, hy, mem_comap.2 (hy ▸ hx)⟩
  have hliftS : ∀ {x : G}, x ∈ S → ∃ y, ι y = x ∧ y ∈ S.comap ι := fun {x} hx => by
    obtain ⟨y, hy⟩ := hK (h.S_le hx)
    exact ⟨y, hy, mem_comap.2 (hy ▸ hx)⟩
  have hcK : Nat.card (K.comap ι) = Nat.card K := by
    rw [← hK', Subgroup.card_map_of_injective hι, hK']
  have hcS : Nat.card (S.comap ι) = Nat.card S := by
    rw [← hS', Subgroup.card_map_of_injective hι, hS']
  have hmul : ∀ a b : H, ι (a * b) = ι a * ι b := fun a b => map_mul ι a b
  exact
  { S_le := Subgroup.comap_mono h.S_le
    S_card := by rw [hcS, hcK]; exact h.S_card
    d_mem := mem_comap.2 (hd ▸ h.d_mem)
    d_sq := hι (by rw [hmul, hd, h.d_sq, map_one])
    d_ne_one := fun e => h.d_ne_one (by rw [← hd, e, map_one])
    d_ne_u := fun e => h.d_ne_u (by rw [← hd, ← hu, e])
    d_comm := fun s hs => hι (by rw [hmul, hmul, hd]; exact h.d_comm _ hs)
    center_inv := fun s hs hss hsc => by
      have h1 : ι s * ι s = 1 := by rw [← hmul, hss, map_one]
      have h2 : ∀ x ∈ S, ι s * x = x * ι s := fun x hx => by
        obtain ⟨y, rfl, hy⟩ := hliftS hx
        rw [← hmul, ← hmul, hsc y hy]
      rcases h.center_inv (ι s) hs h1 h2 with e | e | e | e
      · left
        exact hι (by rw [e, map_one])
      · right; left
        exact hι (by rw [e, hu])
      · right; right; left
        exact hι (by rw [e, hd])
      · right; right; right
        exact hι (by rw [e, hmul, hu, hd])
    d_nonsq := fun s hs e => h.d_nonsq (ι s) hs (by rw [← hmul, e, hd])
    ud_sq := by
      obtain ⟨s, hs, e⟩ := h.ud_sq
      obtain ⟨y, rfl, hy⟩ := hliftS hs
      exact ⟨y, hy, hι (by rw [hmul, hmul, hu, hd]; exact e)⟩
    u_mem := mem_comap.2 (hu ▸ h.u_mem)
    u_central := fun k hk => hι (by rw [hmul, hmul, hu]; exact h.u_central _ hk)
    u_sq := hι (by rw [hmul, hu, h.u_sq, map_one])
    central_inv := fun z hz hzz hzc => by
      have h1 : ι z * ι z = 1 := by rw [← hmul, hzz, map_one]
      have h2 : ∀ y ∈ K, ι z * y = y * ι z := fun y hy => by
        obtain ⟨y', rfl, hy'⟩ := hlift hy
        rw [← hmul, ← hmul, hzc y' hy']
      rcases h.central_inv (ι z) hz h1 h2 with e | e
      · left
        exact hι (by rw [e, map_one])
      · right
        exact hι (by rw [e, hu]) }

end CFSG.EvenSporadicStandard.Solomon78
