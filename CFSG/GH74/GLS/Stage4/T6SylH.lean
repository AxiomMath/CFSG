module

public import CFSG.GH74.GLS.Stage4.T6SylP
public import CFSG.GH74.GLS.Stage4.T6SylG
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

@[expose] def T6Omega1 (N : T2N3 G) (u : G) : Prop :=
  ∀ x ∈ N.H, x * x = 1 → x = 1 ∨ x = N.z ∨ x = u ∨ x = N.z * u

theorem H_card (h : T6Ctx N u p) : Nat.card ↥N.H = (N.q₁ - 1) * (N.q₂ - 1) := by
  have hloc := h.sec5.loc
  have hc : ∀ a ∈ N.H ⊓ N.K₁, ∀ b ∈ N.H ⊓ N.K₂, a * b = b * a := fun a ha b hb =>
    hloc.K_comm a ha.2 b hb.2
  have hinf : (N.H ⊓ N.K₁) ⊓ (N.H ⊓ N.K₂) = Subgroup.zpowers N.z := by
    apply le_antisymm
    · intro x hx
      exact hloc.K_inter ⟨hx.1.2, hx.2.2⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨hloc.z_mem_H, hloc.z_mem_K₁⟩, ⟨hloc.z_mem_H, hloc.z_mem_K₂⟩⟩
  have h2 : Nat.card ↥(Subgroup.zpowers N.z) = 2 := by rw [Nat.card_zpowers, hloc.z_ord]
  have hform := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (N.H ⊓ N.K₁) (N.H ⊓ N.K₂) hc).1
  rw [hinf, h2, hloc.card_H_K₁, hloc.card_H_K₂] at hform
  have hle : (N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂) ≤ N.H := sup_le inf_le_left inf_le_left
  have hrel := Subgroup.relIndex_mul_card ((N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂)) N.H
  rw [hloc.H_idx, inf_eq_left.2 hle] at hrel
  omega

omit [Finite G] in
@[expose] def twoPart (H : Subgroup G) (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}
  mul_mem' := by
    rintro a b ⟨haH, k, hk⟩ ⟨hbH, l, hl⟩
    refine ⟨H.mul_mem haH hbH, k + l, ?_⟩
    have hcomm : Commute a b := hc a haH b hbH
    rw [hcomm.mul_pow]
    have e1 : a ^ (2 ^ (k + l)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    have e2 : b ^ (2 ^ (k + l)) = 1 := by rw [add_comm, pow_add, pow_mul, hl, one_pow]
    rw [e1, e2, one_mul]
  one_mem' := ⟨H.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro a ⟨haH, k, hk⟩
    exact ⟨H.inv_mem haH, k, by rw [inv_pow, hk, inv_one]⟩

omit [Finite G] in
theorem twoPart_isPGroup (H : Subgroup G) (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    IsPGroup 2 ↥(twoPart H hc) := by
  intro x
  obtain ⟨k, hk⟩ := x.2.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem card_twoPart_ge (H : Subgroup G) (hc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    2 ^ (Nat.card ↥H).factorization 2 ≤ Nat.card ↥(twoPart H hc) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  have hS : (S : Subgroup ↥H).map H.subtype ≤ twoPart H hc := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by simpa using congrArg Subtype.val hk'⟩
  have h1 := Subgroup.card_le_of_le hS
  rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity S] at h1
  exact h1

theorem F_cent_zu (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) : f * (N.z * u) = (N.z * u) * f := by
  calc f * (N.z * u) = (f * N.z) * u := by group
    _ = (N.z * f) * u := by rw [F_cent_z h hf]
    _ = N.z * (f * u) := by group
    _ = N.z * (u * f) := by rw [F_cent_u h hf]
    _ = (N.z * u) * f := by group

omit [Finite G] in
theorem conj_eq_of_comm {f t : G} (h : f * t = t * f) : f * t * f⁻¹ = t := by
  rw [h]; group

theorem twoPart_norm_F (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) :
    ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, f * t * f⁻¹ ∈ twoPart N.H h.sec5.loc.H_comm := by
  rintro t ⟨htH, k, hk⟩
  refine ⟨(Subgroup.mem_normalizer_iff.1 (h.sec5.F5.F_normH hf) t).1 htH, k, ?_⟩
  rw [conj_pow, hk]
  group

theorem twoPart_cent_F (h : T6Ctx N u p) (hΩ : T6Omega1 N u) {f : G} (hf : f ∈ N.F) :
    ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, f * t * f⁻¹ = t := by
  refine t6_cent_of_cent_invols (T := twoPart N.H h.sec5.loc.H_comm) ?_ (fun t ht => ht.2)
    (twoPart_norm_F h hf) (h.sec5.F5.F_odd f hf) ?_
  · intro a ha b hb
    exact h.sec5.loc.H_comm a ha.1 b hb.1
  · intro t ht ht2
    rcases hΩ t ht.1 ht2 with rfl | rfl | rfl | rfl
    · group
    · exact conj_eq_of_comm (F_cent_z h hf)
    · exact conj_eq_of_comm (F_cent_u h hf)
    · exact conj_eq_of_comm (F_cent_zu h hf)

theorem U_le_twoPart (h : T6Ctx N u p) : t2U N.z u ≤ twoPart N.H h.sec5.loc.H_comm := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  intro g hg
  have hzT : N.z ∈ twoPart N.H h.sec5.loc.H_comm :=
    ⟨h.sec5.loc.z_mem_H, 1, by rw [pow_one, pow_two]; exact hz2⟩
  have huT : u ∈ twoPart N.H h.sec5.loc.H_comm :=
    ⟨h.sec5.loc.u_mem_H, 1, by rw [pow_one, pow_two]; exact hu2⟩
  rcases U_cases h hg with rfl | rfl | rfl | rfl
  · exact (twoPart N.H h.sec5.loc.H_comm).one_mem
  · exact hzT
  · exact huT
  · exact (twoPart N.H h.sec5.loc.H_comm).mul_mem hzT huT

theorem twoPart_norm_Pst (h : T6Ctx N u p) (hΩ : T6Omega1 N u) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    {t : G} (ht : t ∈ twoPart N.H h.sec5.loc.H_comm) :
    t ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  refine t6_norm_sup (t6_norm_sup (fun r hr => R₂_norm N p (H_le_M₂ h ht.1) hr)
    (fun x hx => h.sec5.loc.H_norm_X₁ t ht.1 x hx)) (fun f hf => ?_)
  have := twoPart_cent_F h hΩ (hP₀F hf) t ht
  have h2 : t * f = f * t := by
    calc t * f = (f * t * f⁻¹) * f := by rw [this]
      _ = f * t := by group
  have : t * f * t⁻¹ = f := by rw [h2]; group
  rw [this]; exact hf

end CFSG.GH74.GLS.Stage4.Rest.T6
