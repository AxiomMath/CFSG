module

public import CFSG.GH74.Uniqueness.SU.SU8Burn
public import CFSG.Adapters.Involutions

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TB

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {G : Type} [Group G]

@[expose] def oc (X : Subgroup G) : Subgroup G := (CFSG.pPrimeCore 2 ↥X).map X.subtype

theorem mem_oc {X : Subgroup G} {x : G} :
    x ∈ oc X ↔ ∃ h : x ∈ X, (⟨x, h⟩ : ↥X) ∈ CFSG.pPrimeCore 2 ↥X := by
  unfold oc
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem oc_le (X : Subgroup G) : oc X ≤ X := by
  intro x hx
  exact (mem_oc.mp hx).1

variable [Finite G]

theorem odd_card_oc (X : Subgroup G) : Odd (Nat.card (oc X)) := by
  have h1 : Nat.card (oc X) = Nat.card (CFSG.pPrimeCore 2 ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := ↥X) (p := 2))

omit [Finite G] in
theorem conj_mem_oc {X : Subgroup G} {g x : G} (hg : g ∈ X) (hx : x ∈ oc X) :
    g * x * g⁻¹ ∈ oc X := by
  obtain ⟨hxX, hxc⟩ := mem_oc.mp hx
  refine mem_oc.mpr ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), ?_⟩
  have := (CFSG.pPrimeCore_normal (p := 2) (G := ↥X)).conj_mem _ hxc ⟨g, hg⟩
  exact this

omit [Finite G] in
theorem le_normalizer_oc (C : Subgroup G) : C ≤ normalizer ((oc C : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact conj_mem_oc hg hh
  · intro hh
    have := conj_mem_oc (inv_mem hg) hh
    simpa [mul_assoc] using this

omit [Finite G] in
theorem le_oc_of_normal_odd {X N : Subgroup G} (hNX : N ≤ X) (hN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ oc X := by
  intro x hx
  refine mem_oc.mpr ⟨hNX hx, ?_⟩
  have hnorm : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hN g g.2 n hn
    simpa [mul_assoc] using this
  have hcard : Nat.card (N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf X)) := by
    rw [hcard]; exact Nat.coprime_two_left.mpr hodd
  have hle : N.subgroupOf X ≤ CFSG.pPrimeCore 2 ↥X := le_sSup ⟨hnorm, hcop⟩
  exact hle (Subgroup.mem_subgroupOf.mpr hx)

theorem oddCore_eq_pPrimeCore (X : Type) [Group X] [Finite X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    exact le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  · have hn : (CFSG.pPrimeCore 2 X).Normal := CFSG.pPrimeCore_normal
    exact le_sSup ⟨hn, Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := X) (p := 2))⟩

theorem eq_oc_mul_centralizer_of_quaternion {X T : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hT : IsSylowIn X T) (hzT : z ∈ T)
    (hquat : ∃ e : ℕ, 1 ≤ e ∧ Nonempty (↥T ≃* QuaternionGroup (2 ^ e))) :
    ∀ g ∈ X, ∃ c ∈ X ⊓ centralizer ({z} : Set G), ∃ k ∈ oc X, g = c * k := by
  obtain ⟨e, he, ⟨φ⟩⟩ := hquat
  have hzX : z ∈ X := hT.1 hzT
  let P : Sylow 2 ↥X := SU8.Burn.sylowOf hT
  have hPq : Nonempty ((P : Subgroup ↥X) ≃* QuaternionGroup (2 ^ ((e + 2) - 2))) := by
    have hs : (e + 2) - 2 = e := by omega
    rw [hs]
    exact ⟨(Subgroup.subgroupOfEquivOfLe hT.1).trans φ⟩
  have hzmem : (⟨z, hzX⟩ : ↥X) ∈ (P : Subgroup ↥X) := by
    show (⟨z, hzX⟩ : ↥X) ∈ T.subgroupOf X
    exact Subgroup.mem_subgroupOf.mpr hzT
  have hzord : orderOf (⟨z, hzX⟩ : ↥X) = 2 := by
    rw [← hz]; exact (Subgroup.orderOf_mk z hzX)
  obtain ⟨-, hcen⟩ := CFSG.Adapters.brauer_suzuki (G := ↥X) (e + 2) (by omega) P hPq ⟨z, hzX⟩ hzmem hzord
  have hzz : (⟨z, hzX⟩ : ↥X) * ⟨z, hzX⟩ = 1 := by
    have := pow_orderOf_eq_one (⟨z, hzX⟩ : ↥X)
    rwa [hzord, sq] at this
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := CFSG.Adapters.eq_centralizer_mul_oddCore hzz hcen ⟨g, hg⟩
  rw [oddCore_eq_pPrimeCore] at hk
  refine ⟨c.1, mem_inf.mpr ⟨c.2, ?_⟩, k.1, mem_oc.mpr ⟨k.2, hk⟩, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    exact congrArg Subtype.val this
  · exact congrArg Subtype.val hgck

end CFSG.GH74.Uniqueness.SU.SU13.TB
