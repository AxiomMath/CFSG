module

public import CFSG.GH74.Uniqueness.Lemma33b

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Prop35

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem mem_sup_zpowers_of_involution {D : Subgroup X} {t : X} (ht : t * t = 1)
    (hnorm : ∀ x ∈ D, t * x * t⁻¹ ∈ D) {u : X} (hu : u ∈ D ⊔ Subgroup.zpowers t) :
    u ∈ D ∨ u * t ∈ D := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have k1 : ∀ w ∈ D, t⁻¹ * w * t ∈ D := fun w hw => by
    have := hnorm w hw
    rw [hti] at this ⊢
    exact this
  have k2 : ∀ w ∈ D, t⁻¹ * w * t⁻¹ ∈ D := fun w hw => by
    have := hnorm w hw
    rw [hti] at this ⊢
    exact this
  have k3 : ∀ w ∈ D, t * w * t ∈ D := fun w hw => by
    have := hnorm w hw
    rw [hti] at this
    exact this
  let S : Subgroup X :=
    { carrier := {x | x ∈ D ∨ x * t ∈ D}
      one_mem' := Or.inl D.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (D.mul_mem hx hy)
        · refine Or.inr ?_
          have : x * y * t = x * (y * t) := by group
          rw [this]
          exact D.mul_mem hx hy
        · refine Or.inr ?_
          have : x * y * t = (x * t) * (t⁻¹ * y * t) := by group
          rw [this]
          exact D.mul_mem hx (k1 y hy)
        · refine Or.inl ?_
          have : x * y = (x * t) * (t⁻¹ * (y * t) * t⁻¹) := by group
          rw [this]
          exact D.mul_mem hx (k2 _ hy)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (D.inv_mem hx)
        · refine Or.inr ?_
          have : x⁻¹ * t = t * (x * t)⁻¹ * t := by group
          change x⁻¹ * t ∈ D
          rw [this]
          exact k3 _ (D.inv_mem hx) }
  have hDS : D ≤ S := fun x hx => Or.inl hx
  have htS : Subgroup.zpowers t ≤ S :=
    (Subgroup.zpowers_le).mpr (Or.inr (by rw [ht]; exact D.one_mem))
  exact sup_le hDS htS hu

omit [Finite X] in
theorem mul_mul_inv_mem_inf_conjugate {t : X} (ht : t * t = 1) {x : X}
    (hx : x ∈ M ⊓ conjugate M t) : t * x * t⁻¹ ∈ M ⊓ conjugate M t := by
  rw [Subgroup.mem_inf, mem_conjugate_iff] at hx ⊢
  refine ⟨hx.2, ?_⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht, hti, ht]; group
  rw [this]
  exact hx.1

theorem IsProductDisconnected.isZStarIn_inf_conjugate_sup (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M) :
    IsZStarIn ((M ⊓ conjugate M t) ⊔ Subgroup.zpowers t) t := by
  set D := M ⊓ conjugate M t
  set W := D ⊔ Subgroup.zpowers t
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have hnorm : ∀ x ∈ D, t * x * t⁻¹ ∈ D := fun x hx => mul_mul_inv_mem_inf_conjugate ht2 hx
  have htW : t ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hiso : ∀ u ∈ Z, u ∈ W → u * t = t * u → u = t := by
    intro u hu huW hcomm
    rcases mem_sup_zpowers_of_involution ht2 hnorm huW with huD | hutD
    · exfalso
      have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
      exact htM (h.centralizer_le_of_mem hu huM
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm))
    · have hutM : u * t ∈ M := (Subgroup.mem_inf.mp hutD).1
      have hodd := h.odd_orderOf_mul hZ ht htM hu (Or.inr hutM)
      have hu2 := hZ.mul_self_eq_one hu
      have hsq : (u * t) * (u * t) = 1 := by
        calc (u * t) * (u * t) = u * (t * u) * t := by group
          _ = u * (u * t) * t := by rw [hcomm]
          _ = (u * u) * (t * t) := by group
          _ = 1 := by rw [hu2, ht2, one_mul]
      have hord : orderOf (u * t) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have h1 : orderOf (u * t) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h2
        · exact h1
        · rw [h2] at hodd
          exact absurd hodd (by decide)
      have hut1 : u * t = 1 := orderOf_eq_one_iff.mp h1
      rw [eq_inv_of_mul_eq_one_left hut1]
      exact inv_eq_of_mul_eq_one_right ht2
  have : Fintype W := Fintype.ofFinite W
  let t' : W := ⟨t, htW⟩
  have ht'1 : t' ≠ 1 := by
    intro h1
    have := hZ.1 t ht
    have h2 : t = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at this
    exact absurd this (by norm_num)
  have ht'2 : t' * t' = 1 := Subtype.ext ht2
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar W t' ht'1 ht'2 (fun g hg => by
    apply Subtype.ext
    have hu : ((g : X) * t * (g : X)⁻¹) ∈ Z := by
      have := hZ.2 t ht (g : X)⁻¹
      rwa [inv_inv] at this
    have huW : (g : X) * t * (g : X)⁻¹ ∈ W :=
      W.mul_mem (W.mul_mem g.2 htW) (W.inv_mem g.2)
    have hc : ((g : X) * t * (g : X)⁻¹) * t = t * ((g : X) * t * (g : X)⁻¹) :=
      congrArg Subtype.val hg
    exact hiso _ hu huW hc)
  have hsub : (N.map W.subtype).subgroupOf W = N :=
    Subgroup.comap_map_eq_self_of_injective W.subtype_injective N
  refine ⟨htW, N.map W.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hNn
  · rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact hNodd
  · intro m hm
    exact Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * t' * ⟨m, hm⟩⁻¹ * t'⁻¹, hN ⟨m, hm⟩, rfl⟩

end Prop35

end CFSG.GH74.Uniqueness
