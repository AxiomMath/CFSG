module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13R

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem innAutE_comm {a b : MulAut ↥E} (ha : a ∈ innAutE E) (hb : b ∈ innAutE E) :
    a * b = b * a := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨e', rfl⟩ := hb
  refine MulEquiv.ext fun f => ?_
  apply Subtype.ext
  show (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹ =
    (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹
  rcases c.h.E_comm e e.2 e' e'.2 with h1 | h1
  · calc (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹
        = ((e : G) * e') * f * ((e : G) * e')⁻¹ := by group
      _ = ((e' : G) * e) * f * ((e' : G) * e)⁻¹ := by rw [h1]
      _ = (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹ := by group
  · have ht : ∀ g ∈ E, g * t = t * g := c.h.t_comm_E
    have hft : (f : G) * t = t * f := ht f f.2
    have hee : ((e' : G) * e) * t = t * ((e' : G) * e) := ht _ (mul_mem e'.2 e.2)
    calc (e : G) * ((e' : G) * f * (e' : G)⁻¹) * (e : G)⁻¹
        = ((e : G) * e') * f * ((e : G) * e')⁻¹ := by group
      _ = (t * ((e' : G) * e)) * f * (t * ((e' : G) * e))⁻¹ := by rw [h1]
      _ = ((e' : G) * e) * (t * f * t⁻¹) * ((e' : G) * e)⁻¹ := by
          have : t * ((e' : G) * e) = ((e' : G) * e) * t := hee.symm
          rw [this]
          group
      _ = ((e' : G) * e) * f * ((e' : G) * e)⁻¹ := by
          have : t * f * t⁻¹ = f := by rw [← hft]; group
          rw [this]
      _ = (e' : G) * ((e : G) * f * (e : G)⁻¹) * (e' : G)⁻¹ := by group

theorem Qs_inf_KR_le : c.Qs ⊓ c.KR ≤ c.Zs := by
  refine c.kl (Y := c.Qs ⊓ c.KR) ((c.Qs_pgroup).to_le inf_le_left) inf_le_right
    (le_inf c.Zs_le_Qs c.Zs_le_KR) ?_
  intro y hy
  exact ⟨c.z_conj_Qs hy.1, c.z_conj_KR hy.2⟩

theorem comm_Qs_mem_Zs {q q' : G} (hq : q ∈ c.Qs) (hq' : q' ∈ c.Qs) :
    q * q' * q⁻¹ * q'⁻¹ ∈ c.Zs := by
  have hQN := c.Qs_le_N1
  have hc : q * q' * q⁻¹ * q'⁻¹ ∈ c.Qs :=
    mul_mem (mul_mem (mul_mem hq hq') (inv_mem hq)) (inv_mem hq')
  refine c.Qs_inf_KR_le ⟨hc, c.mem_KR.2 ⟨hQN hc, ?_⟩⟩
  obtain ⟨e₁, e₂, h1⟩ := c.rho_Qs_mem hq
  obtain ⟨f₁, f₂, h2⟩ := c.rho_Qs_mem hq'
  have e : (⟨q * q' * q⁻¹ * q'⁻¹, hQN hc⟩ : ↥c.N1) =
      ⟨q, hQN hq⟩ * ⟨q', hQN hq'⟩ * ⟨q, hQN hq⟩⁻¹ * ⟨q', hQN hq'⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h1, h2]
  have c1 := c.innAutE_comm (a := MulAut.conj e₁) (b := MulAut.conj f₁) ⟨e₁, rfl⟩ ⟨f₁, rfl⟩
  have c2 := c.innAutE_comm (a := MulAut.conj e₂) (b := MulAut.conj f₂) ⟨e₂, rfl⟩ ⟨f₂, rfl⟩
  refine Prod.ext ?_ ?_
  · show MulAut.conj e₁ * MulAut.conj f₁ * (MulAut.conj e₁)⁻¹ * (MulAut.conj f₁)⁻¹ = 1
    rw [c1]
    group
  · show MulAut.conj e₂ * MulAut.conj f₂ * (MulAut.conj e₂)⁻¹ * (MulAut.conj f₂)⁻¹ = 1
    rw [c2]
    group

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
