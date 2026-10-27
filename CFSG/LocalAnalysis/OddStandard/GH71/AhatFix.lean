module

public import CFSG.LocalAnalysis.OddStandard.GH71.AhatPerm
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.Solomon75.AhatData

theorem conj_eq_inv_of_fpf {G : Type*} [Group G] {Q : Subgroup G} [Finite Q] {w : G}
    (hw : w * w = 1) (hN : ∀ q ∈ Q, w * q * w⁻¹ ∈ Q)
    (hfix : ∀ q ∈ Q, w * q * w⁻¹ = q → q = 1) : ∀ q ∈ Q, w * q * w⁻¹ = q⁻¹ := by
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  let ψ : Q → Q := fun m => ⟨(m : G)⁻¹ * (w * m * w⁻¹), mul_mem (inv_mem m.2) (hN _ m.2)⟩
  have hψ : Function.Injective ψ := by
    intro m m' h
    have h' : (m : G)⁻¹ * (w * m * w⁻¹) = (m' : G)⁻¹ * (w * m' * w⁻¹) := congrArg Subtype.val h
    have hB : w * (m' : G) * w⁻¹ = m' * ((m : G)⁻¹ * (w * m * w⁻¹)) := by rw [h']; group
    have hd : w * ((m' : G) * (m : G)⁻¹) * w⁻¹ = (m' : G) * (m : G)⁻¹ := by
      calc w * ((m' : G) * (m : G)⁻¹) * w⁻¹ = (w * m' * w⁻¹) * (w * m * w⁻¹)⁻¹ := by group
        _ = m' * ((m : G)⁻¹ * (w * m * w⁻¹)) * (w * m * w⁻¹)⁻¹ := by rw [hB]
        _ = (m' : G) * (m : G)⁻¹ := by group
    have h1 := hfix _ (mul_mem m'.2 (inv_mem m.2)) hd
    exact (Subtype.ext (mul_inv_eq_one.1 h1)).symm
  intro q hq
  obtain ⟨n, hn⟩ := (Finite.injective_iff_surjective.1 hψ) ⟨q, hq⟩
  have hn' : (n : G)⁻¹ * (w * n * w⁻¹) = q := congrArg Subtype.val hn
  have hww : w⁻¹ * w⁻¹ = 1 := by rw [← mul_inv_rev, hw, inv_one]
  rw [← hn']
  calc w * ((n : G)⁻¹ * (w * n * w⁻¹)) * w⁻¹ = w * (n : G)⁻¹ * w * n * (w⁻¹ * w⁻¹) := by group
    _ = w * (n : G)⁻¹ * w * n := by rw [hww, mul_one]
    _ = w * (n : G)⁻¹ * w⁻¹ * n := by rw [hw']
    _ = ((n : G)⁻¹ * (w * n * w⁻¹))⁻¹ := by group

@[expose] def fixS (H : Subgroup (Perm (Fin 11))) : Set (Fin 11) := {x | ∀ q ∈ H, q x = x}

theorem mem_fixS {H : Subgroup (Perm (Fin 11))} {x : Fin 11} :
    x ∈ fixS H ↔ ∀ q ∈ H, q x = x := Iff.rfl

theorem fixS_apply {H : Subgroup (Perm (Fin 11))} {p : Perm (Fin 11)}
    (hN : ∀ q ∈ H, p⁻¹ * q * p ∈ H) {x : Fin 11} (hx : x ∈ fixS H) : p x ∈ fixS H := by
  intro q hq
  have h := congrArg p (hx _ (hN q hq))
  simpa using h

theorem card_fixS_modEq {H : Subgroup (Perm (Fin 11))} (hH : IsPGroup 3 H) :
    Nat.card (fixS H) ≡ 2 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hH.card_modEq_card_fixedPoints (Fin 11)
  have e : MulAction.fixedPoints H (Fin 11) = fixS H := by
    ext x
    rw [MulAction.mem_fixedPoints, mem_fixS]
    exact ⟨fun hx q hq => hx ⟨q, hq⟩, fun hx q => hx q q.2⟩
  rw [e, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h.symm.trans (by decide)

theorem shape {F : Set (Fin 11)} (hxo : ∀ k : Fin 8, ∀ x ∈ F, xo k x ∈ F)
    (hg : ∀ x ∈ F, g1 x ∈ F) :
    (∀ x : Fin 11, x.val < 8 → (x ∈ F ↔ (0 : Fin 11) ∈ F)) ∧
      ((9 : Fin 11) ∈ F ↔ (8 : Fin 11) ∈ F) := by
  refine ⟨fun x hx => ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := hxo ⟨x.val, hx⟩ x h
    have e : xo ⟨x.val, hx⟩ x = 0 := xo_self ⟨x.val, hx⟩
    rwa [e] at this
  · have := hxo ⟨x.val, hx⟩ 0 h
    have e : xo ⟨x.val, hx⟩ 0 = x := xo_zero ⟨x.val, hx⟩
    rwa [e] at this
  · have := hg 9 h
    rwa [show g1 9 = 8 by decide] at this
  · have := hg 8 h
    rwa [show g1 8 = 9 by decide] at this

theorem card_eq_of_iff {F : Set (Fin 11)} (P : Fin 11 → Prop) [DecidablePred P]
    (h : ∀ x, x ∈ F ↔ P x) : Nat.card F = (Finset.univ.filter P).card := by
  have e : F = ↑(Finset.univ.filter P) := by
    ext x
    simp [h]
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end CFSG.OddStandard.GH71.AhatB
