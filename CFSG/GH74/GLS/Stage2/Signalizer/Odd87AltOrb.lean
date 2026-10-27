module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb

open Equiv Equiv.Perm Subgroup

@[expose] def Orb {α : Type*} (X : Subgroup (Perm α)) (a : α) : Set α := {b | ∃ x ∈ X, x a = b}

section Basic

variable {α : Type*} {X : Subgroup (Perm α)} {a b : α}

theorem mem_Orb_self (X : Subgroup (Perm α)) (a : α) : a ∈ Orb X a :=
  ⟨1, X.one_mem, rfl⟩

theorem Orb_eq_of_mem (h : b ∈ Orb X a) : Orb X b = Orb X a := by
  obtain ⟨x, hx, rfl⟩ := h
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y * x, X.mul_mem hy hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y * x⁻¹, X.mul_mem hy (X.inv_mem hx), by simp⟩

theorem Orb_eq_of_mem_inter {c : α} (hca : c ∈ Orb X a) (hcb : c ∈ Orb X b) : Orb X a = Orb X b :=
  (Orb_eq_of_mem hca).symm.trans (Orb_eq_of_mem hcb)

theorem Orb_eq_orbit (X : Subgroup (Perm α)) (a : α) : Orb X a = MulAction.orbit ↥X a := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem image_Orb {g : Perm α} (hg : g ∈ normalizer (X : Set (Perm α))) (a : α) :
    g '' Orb X a = Orb X (g a) := by
  ext c
  constructor
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g * x * g⁻¹, (mem_normalizer_iff.mp hg x).mp hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : g⁻¹ * y * g ∈ X := by
      simpa using (mem_normalizer_iff.mp (inv_mem hg) y).mp hy
    exact ⟨(g⁻¹ * y * g) a, ⟨g⁻¹ * y * g, hy', rfl⟩, by simp⟩

theorem image_Orb_eq_self {g : Perm α} (hg : g ∈ normalizer (X : Set (Perm α))) {c : α}
    (hc : c ∈ Orb X a) (hgc : g c ∈ Orb X a) : g '' Orb X a = Orb X a := by
  rw [image_Orb hg a]
  have h1 : g c ∈ Orb X (g a) := by
    rw [← image_Orb hg a]
    exact ⟨c, hc, rfl⟩
  exact Orb_eq_of_mem_inter h1 hgc

end Basic

section Involution

variable {β : Type*}

theorem exists_fixed_of_odd {S : Set β} (hS : S.Finite) {σ : β → β} (hσ : ∀ b, σ (σ b) = b)
    (hmem : ∀ b ∈ S, σ b ∈ S) (hodd : Odd S.ncard) : ∃ b ∈ S, σ b = b := by
  classical
  have : Finite ↥S := hS.to_subtype
  have : Fintype ↥S := Fintype.ofFinite ↥S
  let f : Function.End ↥S := fun x => ⟨σ x.1, hmem x.1 x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show σ (σ x.1) = x.1
    exact hσ x.1
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥S) (f := f) (p := 2) (n := 1) hf
    (hp := ⟨Nat.prime_two⟩)
  have hcard : Fintype.card ↥S = S.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hodd' : Fintype.card ↥S % 2 = 1 := by rw [hcard]; exact Nat.odd_iff.mp hodd
  have hfix : Fintype.card (Function.fixedPoints f) ≠ 0 := by
    intro h0
    have := hmod
    rw [h0] at this
    unfold Nat.ModEq at this
    omega
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hfix)
  refine ⟨x.1, x.2, ?_⟩
  have hx' : f x = x := hx
  exact congrArg Subtype.val hx'

theorem even_ncard_of_fixedpointfree {S : Set β} (hS : S.Finite) {σ : β → β}
    (hσ : ∀ b, σ (σ b) = b) (hmem : ∀ b ∈ S, σ b ∈ S) (hfree : ∀ b ∈ S, σ b ≠ b) :
    Even S.ncard := by
  by_contra hne
  obtain ⟨b, hb, hfix⟩ := exists_fixed_of_odd hS hσ hmem (Nat.not_even_iff_odd.mp hne)
  exact hfree b hb hfix

end Involution

section PGroup

variable {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime] {X : Subgroup (Perm α)}

theorem ncard_Orb_pow (hX : IsPGroup p ↥X) (a : α) : ∃ n : ℕ, (Orb X a).ncard = p ^ n := by
  obtain ⟨n, hn⟩ := hX.card_orbit (α := α) a
  refine ⟨n, ?_⟩
  rw [Orb_eq_orbit, ← Nat.card_coe_set_eq]
  exact hn

theorem three_le_ncard_Orb (hp : p ≠ 2) (hX : IsPGroup p ↥X) {a : α} {x : Perm α} (hx : x ∈ X)
    (hxa : x a ≠ a) : 3 ≤ (Orb X a).ncard := by
  obtain ⟨n, hn⟩ := ncard_Orb_pow hX a
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exfalso
    rw [pow_zero, Set.ncard_eq_one] at hn
    obtain ⟨c, hc⟩ := hn
    have h1 : a ∈ Orb X a := mem_Orb_self X a
    have h2 : x a ∈ Orb X a := ⟨x, hx, rfl⟩
    rw [hc] at h1 h2
    exact hxa ((Set.mem_singleton_iff.mp h2).trans (Set.mem_singleton_iff.mp h1).symm)
  · rw [hn]
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hpos

theorem ncard_fibre_pow (hX : IsPGroup p ↥X) {b₀ b : α} (hb : b ∈ Orb X b₀) :
    ∃ k : ℕ, {g : Perm α | g ∈ X ∧ g b₀ = b}.ncard = p ^ k := by
  obtain ⟨x₁, hx₁, hx₁b⟩ := hb
  let S : Subgroup (Perm α) := X ⊓ MulAction.stabilizer (Perm α) b₀
  have hS : IsPGroup p ↥S := hX.to_inf_left
  have hmemS : ∀ s, s ∈ S ↔ s ∈ X ∧ s b₀ = b₀ := fun s => by
    simp [S, MulAction.mem_stabilizer_iff]
  have hEq : {g : Perm α | g ∈ X ∧ g b₀ = b} = (fun s => x₁ * s) '' (S : Set (Perm α)) := by
    ext g
    constructor
    · rintro ⟨hgX, hgb⟩
      refine ⟨x₁⁻¹ * g, (hmemS _).mpr ⟨X.mul_mem (X.inv_mem hx₁) hgX, ?_⟩, by simp⟩
      rw [Perm.mul_apply, hgb, ← hx₁b]
      simp
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨hsX, hsb⟩ := (hmemS s).mp hs
      exact ⟨X.mul_mem hx₁ hsX, by rw [Perm.mul_apply, hsb, hx₁b]⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  refine ⟨k, ?_⟩
  rw [hEq, Set.ncard_image_of_injective _ (mul_right_injective x₁), ← Nat.card_coe_set_eq]
  exact hk

theorem ncard_fixed_Orb (hp : p ≠ 2) (hX : IsPGroup p ↥X) {u : Perm α} (hu : u * u = 1)
    (hun : u ∈ normalizer (X : Set (Perm α))) {a : α} (hua : u a ∈ Orb X a) :
    ∃ j : ℕ, {b | b ∈ Orb X a ∧ u b = b}.ncard = p ^ j := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hu' : ∀ b, u (u b) = b := fun b => by
    simpa using congrArg (fun g : Perm α => g b) hu
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hmapO : ∀ b ∈ Orb X a, u b ∈ Orb X a := fun b hb => by
    rw [← image_Orb_eq_self hun (mem_Orb_self X a) hua]
    exact Set.mem_image_of_mem u hb
  obtain ⟨m, hm⟩ := ncard_Orb_pow hX a
  have hOodd : Odd (Orb X a).ncard := by
    rw [hm]
    exact hpodd.pow
  obtain ⟨b₀, hb₀, hub₀⟩ := exists_fixed_of_odd (Set.toFinite _) hu' hmapO hOodd
  have hOrb : Orb X b₀ = Orb X a := Orb_eq_of_mem hb₀
  let C : Subgroup (Perm α) := X ⊓ Subgroup.centralizer ({u} : Set (Perm α))
  have hC : IsPGroup p ↥C := hX.to_inf_left
  have hF : {b | b ∈ Orb X a ∧ u b = b} = Orb C b₀ := by
    ext b
    constructor
    · rintro ⟨hbO, hub⟩
      have hbO' : b ∈ Orb X b₀ := by
        rw [hOrb]
        exact hbO
      obtain ⟨k, hk⟩ := ncard_fibre_pow hX hbO'
      have hTodd : Odd {g : Perm α | g ∈ X ∧ g b₀ = b}.ncard := by
        rw [hk]
        exact hpodd.pow
      have hσ : ∀ g : Perm α, u * (u * g * u) * u = g := fun g => by
        calc u * (u * g * u) * u = (u * u) * g * (u * u) := by group
          _ = g := by rw [hu]; group
      have hmem : ∀ g ∈ {g : Perm α | g ∈ X ∧ g b₀ = b},
          u * g * u ∈ {g : Perm α | g ∈ X ∧ g b₀ = b} := by
        rintro g ⟨hgX, hgb⟩
        refine ⟨?_, ?_⟩
        · have := (mem_normalizer_iff.mp hun g).mp hgX
          rwa [hui] at this
        · simp [Perm.mul_apply, hub₀, hgb, hub]
      obtain ⟨g, ⟨hgX, hgb⟩, hgfix⟩ := exists_fixed_of_odd (Set.toFinite _) hσ hmem hTodd
      have hcomm : g * u = u * g := by
        calc g * u = (u * g * u) * u := by rw [hgfix]
          _ = u * g * (u * u) := by group
          _ = u * g := by rw [hu]; group
      exact ⟨g, ⟨hgX, mem_centralizer_singleton_iff.mpr hcomm⟩, hgb⟩
    · rintro ⟨c, ⟨hcX, hcu⟩, rfl⟩
      have hcu' : c * u = u * c := mem_centralizer_singleton_iff.mp hcu
      refine ⟨?_, ?_⟩
      · rw [← hOrb]
        exact ⟨c, hcX, rfl⟩
      · calc u (c b₀) = (u * c) b₀ := rfl
          _ = (c * u) b₀ := by rw [hcu']
          _ = c (u b₀) := rfl
          _ = c b₀ := by rw [hub₀]
  obtain ⟨j, hj⟩ := ncard_Orb_pow hC b₀
  exact ⟨j, by rw [hF]; exact hj⟩

end PGroup

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb
