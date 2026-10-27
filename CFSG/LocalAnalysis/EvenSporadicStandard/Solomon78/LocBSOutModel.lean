module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSFuse

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

theorem center_trivial_of_simple {Y : Type*} [Group Y] {D : Subgroup Y} (hs : IsSimpleGroup D)
    (hnc : ∃ a b : D, a * b ≠ b * a) : ∀ d ∈ D, (∀ e ∈ D, d * e = e * d) → d = 1 := by
  intro d hd hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center D) with h | h
  · have : (⟨d, hd⟩ : D) ∈ center D := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hc g g.2).symm
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hb : b ∈ center D := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem center_trivial_of_equiv {G Y : Type*} [Group G] [Group Y] {K : Subgroup G}
    {D : Subgroup Y} (e : ↥K ≃* ↥D) (hs : IsSimpleGroup D) (hnc : ∃ a b : D, a * b ≠ b * a) :
    ∀ x ∈ K, (∀ k ∈ K, x * k = k * x) → x = 1 := by
  intro x hx hc
  have h1 : (e ⟨x, hx⟩ : Y) = 1 := by
    refine center_trivial_of_simple hs hnc _ (e ⟨x, hx⟩).2 fun d hd => ?_
    obtain ⟨k, hk⟩ := e.surjective ⟨d, hd⟩
    have hkc : (⟨x, hx⟩ : ↥K) * k = k * ⟨x, hx⟩ := Subtype.ext (hc k k.2)
    have h2 := congrArg e hkc
    rw [map_mul, map_mul, hk] at h2
    exact congrArg Subtype.val h2
  have h2 : e ⟨x, hx⟩ = 1 := Subtype.ext h1
  have h3 := e.injective (h2.trans (map_one e).symm)
  exact congrArg Subtype.val h3

structure OutRowModel {Y Y' : Type} [Group Y] [Group Y'] (LY E : Subgroup Y) (φ : ↥E →* Y')
    (D : Subgroup Y') (tY : Y) where
  quot : Quot2Data φ D
  A : Y
  B : Y
  z : Y
  l : Y
  t_mem : tY ∈ LY
  E_iff : ∀ y : Y, y ∈ E ↔ y ∈ LY ∧ y * tY = tY * y
  A_mem : A ∈ E
  B_mem : B ∈ E
  A_odd : Odd (orderOf (⟨A, A_mem⟩ : ↥E))
  B_odd : Odd (orderOf (⟨B, B_mem⟩ : ↥E))
  gen_card : Nat.card ↥(Subgroup.closure {φ ⟨A, A_mem⟩, φ ⟨B, B_mem⟩}) = Nat.card D
  z_mem : z ∈ Subgroup.closure {A, B}
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_two : ∀ hz : z ∈ E, φ ⟨z, hz⟩ ∈ D →
    twoAdic D ≤ twoAdic (D ⊓ centralizer ({φ ⟨z, hz⟩} : Set Y'))
  l_mem : l ∈ LY
  l_conj : l * tY * l⁻¹ = tY * z
  gen : LY ≤ Subgroup.closure {A, B, l * A * l⁻¹, l * B * l⁻¹}
  z_not_conj : ∀ x ∈ LY, x * tY * x⁻¹ ≠ z
  D_fuse : TwoCentralFused D

section Local

variable {Y Y' : Type} [Group Y] [Group Y'] {LY E : Subgroup Y} {φ : ↥E →* Y'}
  {D : Subgroup Y'} {tY : Y}

theorem OutRowModel.equiv_D [Finite ↥E] (M : OutRowModel LY E φ D tY) {G : Type} [Group G]
    {L K : Subgroup G} {u : G} (hu : u ∈ L) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (Ψ : ↥L →* Y) (hΨ : Function.Injective Ψ) (hΨL : ∀ x, Ψ x ∈ LY) (hΨu : Ψ ⟨u, hu⟩ = tY)
    (hKperf : Group.IsPerfect K) (hKcard : Nat.card K = Nat.card D) : Nonempty (↥K ≃* ↥D) := by
  have hq := M.quot
  have := hKperf
  let ΨK : ↥K →* Y := Ψ.comp (Subgroup.inclusion hKL)
  have hΨK : Function.Injective ΨK := hΨ.comp (Subgroup.inclusion_injective hKL)
  have hΨKu : ∀ k : ↥K, ΨK k * tY = tY * ΨK k := by
    intro k
    rw [← hΨu]
    show Ψ (Subgroup.inclusion hKL k) * Ψ ⟨u, hu⟩ = Ψ ⟨u, hu⟩ * Ψ (Subgroup.inclusion hKL k)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKu k k.2)
  let KP : Subgroup Y := ΨK.range
  have hKPE : KP ≤ E := by
    rintro _ ⟨k, rfl⟩
    exact (M.E_iff _).2 ⟨hΨL _, hΨKu k⟩
  let KE : Subgroup ↥E := KP.subgroupOf E
  let eKP : ↥K ≃* ↥KP := MonoidHom.ofInjective hΨK
  let eKE : ↥K ≃* ↥KE := eKP.trans (Subgroup.subgroupOfEquivOfLe hKPE).symm
  have hKEperf : Group.IsPerfect KE :=
    Group.IsPerfect.ofSurjective (f := eKE.toMonoidHom) eKE.surjective
  have hKEcard : Nat.card KE = Nat.card D := (Nat.card_congr eKE.toEquiv).symm.trans hKcard
  exact ⟨eKE.trans (hq.restrictEquiv hKEperf hKEcard)⟩

end Local

end CFSG.EvenSporadicStandard.Solomon78
