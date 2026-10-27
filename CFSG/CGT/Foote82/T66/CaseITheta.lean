module

public import CFSG.CGT.Foote82.T66.CaseIAut
public import CFSG.CGT.Foote82.T66.CaseIBasic
public import CFSG.CGT.Foote82.T66.CaseIHeart

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem Hyp.heartFor (h : Hyp G L z v H₁ m ψ) :
    ∃ β : ↥(commSpace (HH G L v) ⊤) →+ altHeart (m + 6 + 2),
      HeartFor H₁ (m + 6 + 2) ψ.toMonoidHom (HH G L v) β := by
  obtain ⟨β, hs, hk, he⟩ := h.data.heart
  refine ⟨β, ⟨h.H_le_H₁, fun x => ?_, hs, hk, fun x w w' hw y hy => he x w w' hw y hy⟩⟩
  rw [← pe_psi x]
  exact h.mem_H_iff (ψ x)

theorem commSpace_conj_eq (x c : GLV V) :
    commSpace (Subgroup.zpowers (x * c * x⁻¹)) ⊤ =
      (commSpace (Subgroup.zpowers c) ⊤).map (x : V →ₗ[ZMod 2] V) := by
  apply le_antisymm
  · intro w hw
    refine ⟨x⁻¹ w, ?_, x.apply_symm_apply w⟩
    exact mem_commSpace_conj_inv hw
  · rintro _ ⟨w, hw, rfl⟩
    exact mem_commSpace_conj hw

theorem finrank_conj (x c : GLV V) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (x * c * x⁻¹)) ⊤) =
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) := by
  rw [commSpace_conj_eq]
  exact LinearEquiv.finrank_map_eq (x : V ≃ₗ[ZMod 2] V) _

@[expose] noncomputable def jL (ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))) :
    alternatingGroup (Fin (m + 6)) →* GLV V :=
  (pe ψ).comp ((iota2 (m + 6)).comp (alternatingGroup (Fin (m + 6))).subtype)

theorem jL_apply (a : alternatingGroup (Fin (m + 6))) :
    jL ψ a = pe ψ (iota2 (m + 6) (a : Perm (Fin (m + 6)))) := rfl

theorem jL_injective : Function.Injective (jL ψ) := fun a b hab =>
  Subtype.ext (iota2_injective _ (pe_injective hab))

theorem Hyp.range_jL (h : Hyp G L z v H₁ m ψ) : (jL ψ).range = L := by
  rw [h.L_eq, jL, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
    ← altOn_eq_map_iota2]

theorem Hyp.jL_mem (h : Hyp G L z v H₁ m ψ) (a : alternatingGroup (Fin (m + 6))) : jL ψ a ∈ L := by
  rw [← h.range_jL]; exact ⟨a, rfl⟩

theorem psi_jL (a : alternatingGroup (Fin (m + 6))) :
    ψ ⟨jL ψ a, pe_mem _⟩ = iota2 (m + 6) (a : Perm (Fin (m + 6))) := psi_pe _

theorem Hyp.finrank_jL_le_two (h : Hyp G L z v H₁ m ψ) {a : alternatingGroup (Fin (m + 6))}
    (ha : (a : Perm (Fin (m + 6))).IsThreeCycle) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (jL ψ a)) ⊤) ≤ 2 := by
  obtain ⟨β, hβ⟩ := h.heartFor
  refine finrank_commSpace_le_two hβ ψ.injective (pe_mem _) (h.L_le_H (h.jL_mem a)) ?_
  show (ψ ⟨jL ψ a, pe_mem _⟩).IsThreeCycle
  rw [psi_jL]
  rw [← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, cycleType_iota2,
    Equiv.Perm.sum_cycleType, card_support_eq_three_iff]
  exact ha

theorem Hyp.four_le_finrank_jL (h : Hyp G L z v H₁ m ψ) {a : alternatingGroup (Fin (m + 6))}
    (h3 : orderOf (a : Perm (Fin (m + 6))) = 3) (hn : ¬ (a : Perm (Fin (m + 6))).IsThreeCycle) :
    4 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (jL ψ a)) ⊤) := by
  obtain ⟨β, hβ⟩ := h.heartFor
  set σ : Perm (Fin (m + 6 + 2)) := iota2 (m + 6) (a : Perm (Fin (m + 6))) with hσ
  have hσ3 : orderOf σ = 3 := by
    rw [hσ, orderOf_injective (iota2 (m + 6)) (iota2_injective _), h3]
  have hσn : ¬ σ.IsThreeCycle := by
    rw [hσ, ← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, cycleType_iota2,
      Equiv.Perm.sum_cycleType, card_support_eq_three_iff]
    exact hn
  have hσ1 : σ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hσ3; exact absurd hσ3 (by norm_num)
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra hc; push Not at hc; exact hσ1 (Perm.ext hc)
  obtain ⟨d, hd, hdp, hdq, hdr⟩ := exists_two_orbits_of_orderOf_eq_three hσ3 hσn hp
  have hpow : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  have e : ψ.toMonoidHom ⟨jL ψ a, pe_mem _⟩ = σ := psi_jL a
  refine four_le_finrank hβ (pe_mem _) (h.L_le_H (h.jL_mem a)) (by rw [e]; exact hpow)
    (p := p) (d := d) (by rw [e]; exact hp) (by rw [e]; exact hd) hdp (by rw [e]; exact hdq)
    (by rw [e]; exact hdr)

theorem Hyp.L_le_N (h : Hyp G L z v H₁ m ψ) : L ≤ NN G L :=
  fun l hl => ⟨h.H_le_G (h.L_le_H hl), Subgroup.mem_normalizer_iff.2 fun x =>
    ⟨fun hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), fun hx => by
      have := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
      simpa [mul_assoc] using this⟩⟩

theorem Hyp.isThreeCycle_of_conj (h : Hyp G L z v H₁ m ψ) {x : GLV V}
    (hx : x ∈ NN G L) {a b : alternatingGroup (Fin (m + 6))}
    (ha : (a : Perm (Fin (m + 6))).IsThreeCycle) (hab : x * jL ψ a * x⁻¹ = jL ψ b) :
    (b : Perm (Fin (m + 6))).IsThreeCycle := by
  by_contra hb
  have h1 := h.finrank_jL_le_two ha
  have hord : orderOf (b : Perm (Fin (m + 6))) = 3 := by
    have e1 : orderOf (jL ψ b) = orderOf (jL ψ a) := by
      rw [← hab, show x * jL ψ a * x⁻¹ = (MulAut.conj x).toMonoidHom (jL ψ a) from rfl,
        orderOf_injective _ (MulAut.conj x).injective]
    rw [orderOf_injective _ jL_injective, orderOf_injective _ jL_injective] at e1
    rw [Subgroup.orderOf_coe, e1, ← Subgroup.orderOf_coe, ha.orderOf]
  have h2 := h.four_le_finrank_jL hord hb
  rw [← hab, finrank_conj] at h2
  omega

theorem a6c012_isThreeCycle :
    ((CFSG.ComponentClassification.RankTwoAlt.a6c012 : alternatingGroup (Fin 6)) :
      Perm (Fin 6)).IsThreeCycle := by
  rw [← card_support_eq_three_iff]
  decide

theorem Hyp.exists_thetaL (h : Hyp G L z v H₁ m ψ) :
    ∃ θ : ↥(NN G L) →* Perm (Fin (m + 6)),
      (∀ (x : ↥(NN G L)) a,
        (x : GLV V) * jL ψ a * (x : GLV V)⁻¹ = jL ψ (CaseIAut.conjA (θ x) a)) ∧
      (∀ x : ↥(NN G L), θ x = 1 ↔ ∀ a, (x : GLV V) * jL ψ a = jL ψ a * x) ∧
      (∀ (x : ↥(NN G L)) (σ : Perm (Fin (m + 6))),
        (x : GLV V) = pe ψ (iota2 (m + 6) σ) → θ x = σ) := by
  have hnorm : ∀ x ∈ NN G L, x ∈ Subgroup.normalizer ((jL ψ).range : Set (GLV V)) := by
    intro x hx
    rw [h.range_jL]; exact hx.2
  have hperm : ∀ x ∈ NN G L, ∃ σ : Perm (Fin (m + 6)),
      ∀ a, x * jL ψ a * x⁻¹ = jL ψ (CaseIAut.conjA σ a) := by
    intro x hx
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      exact CaseIAut.exists_perm_conj_of_six (jL ψ) jL_injective (hnorm x hx)
        fun b hb => h.isThreeCycle_of_conj hx a6c012_isThreeCycle hb
    · exact CaseIAut.exists_perm_conj_of_ge_seven (Or.inr (by omega)) (jL ψ) jL_injective
        (hnorm x hx)
  obtain ⟨θ, hθ⟩ := CaseIAut.exists_theta (m := m + 6) (by omega) (jL ψ) jL_injective (NN G L)
    hperm
  refine ⟨θ, hθ, CaseIAut.theta_eq_one_iff (by omega) _ jL_injective hθ, fun x σ hx => ?_⟩
  refine CaseIAut.theta_eq (by omega) _ jL_injective hθ x fun a => ?_
  rw [hx, jL_apply, jL_apply, CaseIAut.coe_conjA, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, ← map_mul, ← map_mul]

end CaseIAux

end CFSG.CGT.Foote82
