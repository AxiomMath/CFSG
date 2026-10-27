module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyPair
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.EvenSporadicStandard.TwoHS.SignS9

open Subgroup

variable {X : Type*} [Group X] {τ : X} {D S : Subgroup X}
  {eD : D ≃* DihedralGroup 4} {eS : S ≃* Equiv.Perm (Fin 5)}

theorem card_of_equiv_dihedral (eD : D ≃* DihedralGroup 4) : Nat.card D = 8 := by
  rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]

theorem card_of_equiv_perm_five (eS : S ≃* Equiv.Perm (Fin 5)) : Nat.card S = 120 := by
  rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem dihedral_center (g : DihedralGroup 4) (h : ∀ x : DihedralGroup 4, x * g = g * x) :
    g = 1 ∨ g = DihedralGroup.r 2 := by
  revert g
  decide

theorem tau_ne_one (h : LocalPair τ D S eD eS) : τ ≠ 1 := by
  obtain ⟨hτ, he⟩ := h.tau_mem
  rintro rfl
  have : eD ⟨1, hτ⟩ = 1 := by
    have : (⟨1, hτ⟩ : D) = 1 := rfl
    rw [this, map_one]
  rw [this] at he
  exact absurd he (by decide)

theorem mul_tau_of_mem_left (h : LocalPair τ D S eD eS) {d : X} (hd : d ∈ D) :
    d * τ = τ * d :=
  (h.cent d).2 ⟨d, hd, 1, S.one_mem, (mul_one d).symm⟩

theorem mul_tau_of_mem_right (h : LocalPair τ D S eD eS) {s : X} (hs : s ∈ S) :
    s * τ = τ * s :=
  (h.cent s).2 ⟨1, D.one_mem, s, hs, (one_mul s).symm⟩

theorem left_le_centralizer (h : LocalPair τ D S eD eS) : D ≤ centralizer {τ} := fun _ hd =>
  mem_centralizer_singleton_iff.2 (mul_tau_of_mem_left h hd)

theorem right_le_centralizer (h : LocalPair τ D S eD eS) : S ≤ centralizer {τ} := fun _ hs =>
  mem_centralizer_singleton_iff.2 (mul_tau_of_mem_right h hs)

theorem commute_subtype (h : LocalPair τ D S eD eS) (d : D) (s : S) :
    Commute (D.subtype d) (S.subtype s) :=
  h.comm d d.2 s s.2

theorem centralizer_eq_range (h : LocalPair τ D S eD eS) :
    centralizer {τ} = (D.subtype.noncommCoprod S.subtype (commute_subtype h)).range := by
  ext x
  rw [mem_centralizer_singleton_iff, MonoidHom.mem_range, h.cent]
  constructor
  · rintro ⟨d, hd, s, hs, rfl⟩
    exact ⟨(⟨d, hd⟩, ⟨s, hs⟩), rfl⟩
  · rintro ⟨⟨d, s⟩, rfl⟩
    exact ⟨d, d.2, s, s.2, rfl⟩

theorem card_centralizer (h : LocalPair τ D S eD eS) : Nat.card (centralizer {τ}) = 960 := by
  have hinj : Function.Injective (D.subtype.noncommCoprod S.subtype (commute_subtype h)) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨D.subtype_injective, S.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype, Subgroup.disjoint_def]
    exact fun hx hy => h.inf _ hx hy
  rw [centralizer_eq_range h, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_prod, card_of_equiv_dihedral eD, card_of_equiv_perm_five eS]

theorem conj_mem_left (h : LocalPair τ D S eD eS) {g : X} (hg : g * τ = τ * g) {d : X}
    (hd : d ∈ D) : g * d * g⁻¹ ∈ D := by
  obtain ⟨d₀, hd₀, s₀, hs₀, rfl⟩ := (h.cent g).1 hg
  have hc : s₀ * d = d * s₀ := (h.comm d hd s₀ hs₀).symm
  have : d₀ * s₀ * d * (d₀ * s₀)⁻¹ = d₀ * d * d₀⁻¹ :=
    calc d₀ * s₀ * d * (d₀ * s₀)⁻¹ = d₀ * (s₀ * d) * s₀⁻¹ * d₀⁻¹ := by group
      _ = d₀ * (d * s₀) * s₀⁻¹ * d₀⁻¹ := by rw [hc]
      _ = d₀ * d * d₀⁻¹ := by group
  rw [this]
  exact D.mul_mem (D.mul_mem hd₀ hd) (D.inv_mem hd₀)

theorem eq_one_or_eq_tau (h : LocalPair τ D S eD eS) {z : X} (hz : z ∈ D)
    (hc : ∀ d ∈ D, z * d = d * z) : z = 1 ∨ z = τ := by
  obtain ⟨hτ, he⟩ := h.tau_mem
  have hcomm : ∀ x : DihedralGroup 4, x * eD ⟨z, hz⟩ = eD ⟨z, hz⟩ * x := by
    intro x
    obtain ⟨d, rfl⟩ := eD.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc d d.2).symm
  rcases dihedral_center _ hcomm with h1 | h1
  · left
    have : (⟨z, hz⟩ : D) = 1 := eD.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨z, hz⟩ : D) = ⟨τ, hτ⟩ := eD.injective (by rw [h1, he])
    exact congrArg Subtype.val this

theorem localPair_map {Y : Type*} [Group Y] (h : LocalPair τ D S eD eS) (φ : X ≃* Y) :
    LocalPair (φ τ) (D.map φ.toMonoidHom) (S.map φ.toMonoidHom)
      ((D.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eD)
      ((S.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eS) where
  tau_sq := by rw [← map_mul, h.tau_sq, map_one]
  tau_mem := by
    obtain ⟨hτ, he⟩ := h.tau_mem
    refine ⟨⟨τ, hτ, rfl⟩, ?_⟩
    have : (D.equivMapOfInjective φ.toMonoidHom φ.injective).symm
        ⟨φ τ, ⟨τ, hτ, rfl⟩⟩ = ⟨τ, hτ⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, this, he]
  comm := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h.comm d hd s hs]
  inf := by
    rintro _ ⟨d, hd, rfl⟩ ⟨s, hs, hsd⟩
    have : s = d := φ.injective hsd
    subst this
    simp only [h.inf s hd hs, map_one]
  cent := by
    intro y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, φ.injective.eq_iff, h.cent x]
    constructor
    · rintro ⟨d, hd, s, hs, rfl⟩
      exact ⟨φ d, ⟨d, hd, rfl⟩, φ s, ⟨s, hs, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, _, ⟨s, hs, rfl⟩, hx⟩
      exact ⟨d, hd, s, hs, φ.injective (by simpa using hx)⟩

end CFSG.EvenSporadicStandard.TwoHS.SignS9
