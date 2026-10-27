module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwistData

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist

open Subgroup

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {B : Subgroup G} {g : G}
    (h : ∀ y ∈ B, g * y * g⁻¹ ∈ B) (h' : ∀ y ∈ B, g⁻¹ * y * g ∈ B) :
    g ∈ normalizer (B : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have := h' _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem mem_normalizer_conj {G : Type*} [Group G] {A B : Subgroup G} {u ω : G}
    (hu : ∀ x ∈ A, u * x * u⁻¹ ∈ B) (hu' : ∀ y ∈ B, u⁻¹ * y * u ∈ A)
    (hω : ω ∈ normalizer (A : Set G)) : u * ω * u⁻¹ ∈ normalizer (B : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have e : u * ω * u⁻¹ * y * (u * ω * u⁻¹)⁻¹ = u * (ω * (u⁻¹ * y * u) * ω⁻¹) * u⁻¹ := by
    group
  rw [e]
  constructor
  · intro hy
    exact hu _ ((mem_normalizer_iff.mp hω _).mp (hu' y hy))
  · intro hy
    have h2 : ω * (u⁻¹ * y * u) * ω⁻¹ ∈ A := by
      have := hu' _ hy
      rwa [show u⁻¹ * (u * (ω * (u⁻¹ * y * u) * ω⁻¹) * u⁻¹) * u = ω * (u⁻¹ * y * u) * ω⁻¹ by
        group] at this
    have := hu _ ((mem_normalizer_iff.mp hω _).mpr h2)
    rwa [show u * (u⁻¹ * y * u) * u⁻¹ = y by group] at this

namespace Data

variable {G : Type*} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2] {m : ℕ}
  (d : Data G k m)

theorem S_conj_X₁ {s : G} (hs : s ∈ d.S) {x : G} (hx : x ∈ d.X₁) : s * x * s⁻¹ ∈ d.X₁ := by
  rw [show s * x * s⁻¹ = (s * x * s⁻¹ * x⁻¹) * x by group]
  exact mul_mem (d.F_le₁ (d.comm_mem_F s hs x (d.X₁_le hx))) hx

theorem S_conj_X₂ {s : G} (hs : s ∈ d.S) {x : G} (hx : x ∈ d.X₂) : s * x * s⁻¹ ∈ d.X₂ := by
  rw [show s * x * s⁻¹ = (s * x * s⁻¹ * x⁻¹) * x by group]
  exact mul_mem (d.F_le₂ (d.comm_mem_F s hs x (d.X₂_le hx))) hx

theorem S_mem_normalizer_X₁ {s : G} (hs : s ∈ d.S) : s ∈ normalizer (d.X₁ : Set G) :=
  mem_normalizer_of_conj_mem (fun _ hy => d.S_conj_X₁ hs hy) (fun y hy => by
    simpa using d.S_conj_X₁ (inv_mem hs) hy)

theorem S_mem_normalizer_X₂ {s : G} (hs : s ∈ d.S) : s ∈ normalizer (d.X₂ : Set G) :=
  mem_normalizer_of_conj_mem (fun _ hy => d.S_conj_X₂ hs hy) (fun y hy => by
    simpa using d.S_conj_X₂ (inv_mem hs) hy)

theorem X₁_le_normalizer_F : d.X₁ ≤ normalizer (d.F : Set G) := fun x hx =>
  d.mem_normalizer_F (le_normalizer (d.X₁_le hx))

theorem X₂_le_normalizer_F : d.X₂ ≤ normalizer (d.F : Set G) := fun x hx =>
  d.mem_normalizer_F (le_normalizer (d.X₂_le hx))

theorem X₁_conj_eq {f : G} (hf : f ∈ d.X₁) {y : G} (hy : y ∈ d.X₁) : f * y * f⁻¹ = y := by
  rw [d.X₁_ab f hf y hy, mul_inv_cancel_right]

theorem F_le_normalizer_Z : d.F ≤ normalizer (d.Z : Set G) := fun f hf =>
  mem_normalizer_of_conj_mem
    (fun y hy => by rw [d.X₁_conj_eq (d.F_le₁ hf) (d.Z_le_X₁ hy)]; exact hy)
    (fun y hy => by
      have h := d.X₁_conj_eq (inv_mem (d.F_le₁ hf)) (d.Z_le_X₁ hy)
      rw [inv_inv] at h
      rw [h]
      exact hy)

theorem omega_mem_normalizer_X₂ {ω : G} (hωN : ω ∈ d.N)
    (hωS : ω ∈ normalizer (d.S : Set G)) (hω3 : ω * ω * ω = 1) :
    ω ∈ normalizer (d.X₂ : Set G) :=
  mem_normalizer_of_cube hω3 (d.conj_mem_of_normalizes d.X₁_le d.X₂_le d.S_eq d.X₁_sq d.X₂_sq
    d.F_le₁ d.F_le₂ d.X₁_inf_X₂ (fun _ hy hyF _ hs hc => d.centralizer_X₂ hy hyF hs hc) hωS
    (d.N_le_norm hωN))

theorem omega₂_mem_normalizer_X₂ {ω : G} (hω : ω ∈ normalizer (d.X₁ : Set G)) :
    d.u * ω * d.u⁻¹ ∈ normalizer (d.X₂ : Set G) :=
  mem_normalizer_conj d.u_X₁ (fun _ hy => d.conj_inv_u_X₁ hy) hω

theorem omega₂_mem_normalizer_S {ω : G} (hω : ω ∈ normalizer (d.S : Set G)) :
    d.u * ω * d.u⁻¹ ∈ normalizer (d.S : Set G) :=
  mul_mem (mul_mem d.u_norm hω) (inv_mem d.u_norm)

theorem omega₂_cube {ω : G} (hω3 : ω * ω * ω = 1) :
    (d.u * ω * d.u⁻¹) * (d.u * ω * d.u⁻¹) * (d.u * ω * d.u⁻¹) = 1 := by
  rw [show (d.u * ω * d.u⁻¹) * (d.u * ω * d.u⁻¹) * (d.u * ω * d.u⁻¹) =
    d.u * (ω * ω * ω) * d.u⁻¹ by group, hω3]
  group

theorem omega₂_mem_normalizer_X₁ {ω : G} (hωN : ω ∈ d.N)
    (hωS : ω ∈ normalizer (d.S : Set G)) (hω3 : ω * ω * ω = 1) :
    d.u * ω * d.u⁻¹ ∈ normalizer (d.X₁ : Set G) :=
  mem_normalizer_of_cube (d.omega₂_cube hω3) (d.conj_mem_of_normalizes d.X₂_le d.X₁_le d.S_eq'
    d.X₂_sq d.X₁_sq d.F_le₂ d.F_le₁ (fun x h2 h1 => d.X₁_inf_X₂ x h1 h2)
    (fun _ hy hyF _ hs hc => d.centralizer_X₁ hy hyF hs hc) (d.omega₂_mem_normalizer_S hωS)
    (d.omega₂_mem_normalizer_X₂ (d.N_le_norm hωN)))

def Z₂ : Subgroup G := d.Z.map (MulAut.conj d.u).toMonoidHom

theorem mem_Z₂ {z : G} : z ∈ d.Z₂ ↔ ∃ z' ∈ d.Z, z = d.u * z' * d.u⁻¹ := by
  simp only [Z₂, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z', hz', rfl⟩
  · rintro ⟨z', hz', rfl⟩
    exact ⟨z', hz', rfl⟩

theorem Z₂_le_F : d.Z₂ ≤ d.F := fun z hz => by
  obtain ⟨z', hz', rfl⟩ := d.mem_Z₂.mp hz
  exact d.conj_mem_F d.u_norm (d.Z_le_F hz')

theorem card_Z₂ : Nat.card d.Z₂ = 2 ^ m := by
  rw [Z₂, card_map_of_injective (MulAut.conj d.u).injective, d.card_Z]

theorem Z_inf_Z₂ : d.Z ⊓ d.Z₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro z hz
  obtain ⟨hz1, hz2⟩ := mem_inf.mp hz
  obtain ⟨z', hz', rfl⟩ := d.mem_Z₂.mp hz2
  refine mem_bot.mpr (d.CC _ (d.Z_le_F hz1) (fun n hn => d.Z_central hz1 hn) fun n hn => ?_)
  calc d.u * n * d.u⁻¹ * (d.u * z' * d.u⁻¹) = d.u * (n * z') * d.u⁻¹ := by group
    _ = d.u * (z' * n) * d.u⁻¹ := by rw [d.Z_central hz' hn]
    _ = d.u * z' * d.u⁻¹ * (d.u * n * d.u⁻¹) := by group

theorem Z_sup_Z₂ : d.Z ⊔ d.Z₂ = d.F := by
  have hnorm : d.Z ≤ normalizer (d.Z₂ : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem
      (fun y hy => by
        rw [d.X₁_conj_eq (d.Z_le_X₁ hz) ((d.F_le₁ (d.Z₂_le_F hy)))]; exact hy)
      (fun y hy => by
        have h := d.X₁_conj_eq (inv_mem (d.Z_le_X₁ hz)) ((d.F_le₁ (d.Z₂_le_F hy)))
        rw [inv_inv] at h
        rw [h]; exact hy)
  have h := card_sup_mul_card_inf' hnorm
  rw [d.Z_inf_Z₂, card_bot, mul_one, d.card_Z, d.card_Z₂] at h
  refine eq_of_le_of_card_ge (sup_le d.Z_le_F d.Z₂_le_F) ?_
  rw [d.card_F, h]
  exact le_of_eq (by ring)

theorem exists_mul_Z₂ {f : G} (hf : f ∈ d.F) : ∃ z ∈ d.Z, ∃ z₂ ∈ d.Z₂, f = z * z₂ := by
  have hnorm : d.Z₂ ≤ normalizer (d.Z : Set G) := fun z hz =>
    mem_normalizer_of_conj_mem
      (fun y hy => by
        rw [d.X₁_conj_eq (d.F_le₁ (d.Z₂_le_F hz)) (d.Z_le_X₁ hy)]; exact hy)
      (fun y hy => by
        have h := d.X₁_conj_eq (inv_mem (d.F_le₁ (d.Z₂_le_F hz))) (d.Z_le_X₁ hy)
        rw [inv_inv] at h
        rw [h]; exact hy)
  rw [← d.Z_sup_Z₂, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hnorm] at hf
  obtain ⟨z, hz, z₂, hz₂, rfl⟩ := hf
  exact ⟨z, hz, z₂, hz₂, rfl⟩

theorem omega₂_triv_F {ω : G} (hωN : ω ∈ d.N) (hωS : ω ∈ normalizer (d.S : Set G))
    (hω3 : ω * ω * ω = 1) {f : G} (hf : f ∈ d.F) :
    (d.u * ω * d.u⁻¹) * f * (d.u * ω * d.u⁻¹)⁻¹ * f⁻¹ ∈ d.Z := by
  obtain ⟨z, hz, z₂, hz₂, rfl⟩ := d.exists_mul_Z₂ hf
  obtain ⟨z', hz', rfl⟩ := d.mem_Z₂.mp hz₂
  have hZ : (d.u * ω * d.u⁻¹) * z * (d.u * ω * d.u⁻¹)⁻¹ ∈ d.Z :=
    (mem_normalizer_iff.mp (d.mem_normalizer_Z (d.omega₂_mem_normalizer_X₁ hωN hωS hω3)) z).mp hz
  have hc : ω * z' = z' * ω := d.Z_central hz' hωN
  have hz₂c : (d.u * ω * d.u⁻¹) * (d.u * z' * d.u⁻¹) * (d.u * ω * d.u⁻¹)⁻¹ =
      d.u * z' * d.u⁻¹ := by
    calc (d.u * ω * d.u⁻¹) * (d.u * z' * d.u⁻¹) * (d.u * ω * d.u⁻¹)⁻¹
        = d.u * ((ω * z') * ω⁻¹) * d.u⁻¹ := by group
      _ = d.u * ((z' * ω) * ω⁻¹) * d.u⁻¹ := by rw [hc]
      _ = d.u * z' * d.u⁻¹ := by group
  have e : (d.u * ω * d.u⁻¹) * (z * (d.u * z' * d.u⁻¹)) * (d.u * ω * d.u⁻¹)⁻¹ *
        (z * (d.u * z' * d.u⁻¹))⁻¹ =
      ((d.u * ω * d.u⁻¹) * z * (d.u * ω * d.u⁻¹)⁻¹) * z⁻¹ := by
    calc (d.u * ω * d.u⁻¹) * (z * (d.u * z' * d.u⁻¹)) * (d.u * ω * d.u⁻¹)⁻¹ *
          (z * (d.u * z' * d.u⁻¹))⁻¹
        = ((d.u * ω * d.u⁻¹) * z * (d.u * ω * d.u⁻¹)⁻¹) *
          ((d.u * ω * d.u⁻¹) * (d.u * z' * d.u⁻¹) * (d.u * ω * d.u⁻¹)⁻¹) *
          (d.u * z' * d.u⁻¹)⁻¹ * z⁻¹ := by group
      _ = ((d.u * ω * d.u⁻¹) * z * (d.u * ω * d.u⁻¹)⁻¹) * z⁻¹ := by rw [hz₂c]; group
  rw [e]
  exact mul_mem hZ (inv_mem hz)

theorem comm_triv_aux {ω ω₂ f a b c : G} (ha : a = ω⁻¹ * f * ω) (hb : b = ω₂⁻¹ * a * ω₂)
    (hc : c = ω * b * ω⁻¹) :
    (ω₂ * ω * ω₂⁻¹ * ω⁻¹) * f * (ω₂ * ω * ω₂⁻¹ * ω⁻¹)⁻¹ * f⁻¹ =
      (ω₂ * c * ω₂⁻¹ * c⁻¹) * (ω * (b * a⁻¹) * ω⁻¹) := by
  subst hc hb ha
  group

theorem commutator_omega_mem_S {ω : G} (hωN : ω ∈ d.N) (hωS : ω ∈ normalizer (d.S : Set G))
    (hω3 : ω * ω * ω = 1) :
    (d.u * ω * d.u⁻¹) * ω * (d.u * ω * d.u⁻¹)⁻¹ * ω⁻¹ ∈ d.S := by
  have hω₂X₁ := d.omega₂_mem_normalizer_X₁ hωN hωS hω3
  have hω₂S := d.omega₂_mem_normalizer_S hωS
  have hgN : (d.u * ω * d.u⁻¹) * ω * (d.u * ω * d.u⁻¹)⁻¹ * ω⁻¹ ∈ d.N :=
    mul_mem (d.N_conj _ hω₂X₁ ω hωN) (inv_mem hωN)
  refine d.module_facts.2.2.1 _ hgN fun f hf => ?_
  have hωF := d.mem_normalizer_F hωS
  have hω₂F := d.mem_normalizer_F hω₂S
  have ha : ω⁻¹ * f * ω ∈ d.F := (mem_normalizer_iff''.mp hωF f).mp hf
  have hb : (d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹) ∈ d.F :=
    (mem_normalizer_iff''.mp hω₂F _).mp ha
  have hc : ω * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹)) * ω⁻¹ ∈ d.F :=
    (mem_normalizer_iff.mp hωF _).mp hb
  have T1 := d.omega₂_triv_F hωN hωS hω3 hb
  have T2 := d.omega₂_triv_F hωN hωS hω3 hc
  rw [comm_triv_aux (a := ω⁻¹ * f * ω) (b := (d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) *
    (d.u * ω * d.u⁻¹)) (c := ω * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹)) *
      ω⁻¹) rfl rfl rfl]
  refine mul_mem T2 ?_
  have T1' : (ω⁻¹ * f * ω) * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹))⁻¹ ∈
      d.Z := by
    rwa [show (d.u * ω * d.u⁻¹) * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹)) *
      (d.u * ω * d.u⁻¹)⁻¹ * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹))⁻¹ =
      (ω⁻¹ * f * ω) * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹))⁻¹ by group]
      at T1
  have := (mem_normalizer_iff.mp (d.mem_normalizer_Z (d.N_le_norm hωN)) _).mp (inv_mem T1')
  rwa [show ω * ((ω⁻¹ * f * ω) * ((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹))⁻¹)⁻¹ *
    ω⁻¹ = ω * (((d.u * ω * d.u⁻¹)⁻¹ * (ω⁻¹ * f * ω) * (d.u * ω * d.u⁻¹)) * (ω⁻¹ * f * ω)⁻¹) *
    ω⁻¹ by group] at this

end Data

end CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialTwist
