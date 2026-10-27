module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Co2Three

theorem card_centralizer_conj_inf {G : Type*} [Group G] {P : Subgroup G} {q : G} (hq : q ∈ P)
    (X : Set G) :
    Nat.card ↥(Subgroup.centralizer ((fun x => q * x * q⁻¹) '' X) ⊓ P) =
      Nat.card ↥(Subgroup.centralizer X ⊓ P) := by
  refine Nat.card_congr ((MulAut.conj q⁻¹).toEquiv.subtypeEquiv fun c => ?_)
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.forall_mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, P.mul_mem (P.mul_mem (P.inv_mem hq) h2) hq⟩
    have e := h1 hx
    calc x * (q⁻¹ * c * q) = q⁻¹ * (q * x * q⁻¹ * c) * q := by group
      _ = q⁻¹ * (c * (q * x * q⁻¹)) * q := by rw [e]
      _ = q⁻¹ * c * q * x := by group
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · have e := h1 x hx
      calc q * x * q⁻¹ * c = q * (x * (q⁻¹ * c * q)) * q⁻¹ := by group
        _ = q * (q⁻¹ * c * q * x) * q⁻¹ := by rw [e]
        _ = c * (q * x * q⁻¹) := by group
    · have e : q * (q⁻¹ * c * q) * q⁻¹ = c := by group
      rw [← e]
      exact P.mul_mem (P.mul_mem hq h2) (P.inv_mem hq)

theorem card_centralizer_map_conj_inf {G : Type*} [Group G] {P : Subgroup G} {q : G}
    (hq : q ∈ P) (B : Subgroup G) :
    Nat.card ↥(Subgroup.centralizer ((B.map (MulAut.conj q).toMonoidHom : Subgroup G) : Set G) ⊓
      P) = Nat.card ↥(Subgroup.centralizer (B : Set G) ⊓ P) := by
  rw [Subgroup.coe_map]
  exact card_centralizer_conj_inf hq _

end CFSG.KC.Co2Three

end
