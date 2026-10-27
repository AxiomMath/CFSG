module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Img

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

theorem B_le_normE : B ≤ normalizer (E : Set G) := fun _ hb => c.W_le_normE (c.h.B_le_W hb)

@[expose] noncomputable def kappa : ↥B →* MulAut ↥E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion c.B_le_normE)

theorem kappa_coe (b : ↥B) (e : ↥E) : ((c.kappa b e : ↥E) : G) = b * e * (b : G)⁻¹ := rfl

theorem kappa_eq_convN (b : ↥B) : c.kappa b = convN ⟨(b : G), c.B_le_normE b.2⟩ := rfl

theorem rho_B (b : ↥B) : c.rho ⟨(b : G), c.B_le_N1 b.2⟩ = (c.kappa b, c.kappa b) := by
  have hbz : (b : G) * z = z * b := c.h.BS b b.2 z c.h.zS
  have := c.rho_conv ⟨(b : G), c.B_le_N1 b.2⟩ hbz (c.B_le_normE b.2)
  exact this

theorem eq_one_of_kappa_mem_inn {b : ↥B} (hb : c.kappa b ∈ innAutE E) : b = 1 := by
  obtain ⟨e₀, he₀⟩ := hb
  have hcomm : ∀ e ∈ E, ((e₀ : G)⁻¹ * b) * e = e * ((e₀ : G)⁻¹ * b) := by
    intro e he
    have h1 := congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) he₀
    simp only [MulAut.conj_apply, kappa_coe, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (e₀ : G)⁻¹ * b * e = (e₀ : G)⁻¹ * (b * e * (b : G)⁻¹) * b := by group
      _ = (e₀ : G)⁻¹ * (e₀ * e * (e₀ : G)⁻¹) * b := by rw [← h1]
      _ = e * ((e₀ : G)⁻¹ * b) := by group
  have hL : (e₀ : G)⁻¹ * b ∈ L := mul_mem (inv_mem (c.h.wf.E_le e₀.2)) (c.h.ob.B_le b.2)
  have hbE : (b : G) ∈ E := by
    rcases c.h.wf.cent _ hL hcomm with h1 | h1
    · have : (b : G) = e₀ := by
        calc (b : G) = e₀ * ((e₀ : G)⁻¹ * b) := by group
          _ = e₀ := by rw [h1, mul_one]
      rw [this]; exact e₀.2
    · have : (b : G) = e₀ * t := by
        calc (b : G) = e₀ * ((e₀ : G)⁻¹ * b) := by group
          _ = e₀ * t := by rw [h1]
      rw [this]; exact mul_mem e₀.2 c.h.t_mem_E
  exact Subtype.ext (c.h.E_inf_B hbE b.2)

theorem kappa_injective : Function.Injective c.kappa := by
  rw [injective_iff_map_eq_one]
  intro b hb
  exact c.eq_one_of_kappa_mem_inn (hb ▸ (innAutE E).one_mem)

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ

theorem pi_kappa_injective : Function.Injective (π.comp c.kappa) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  exact c.eq_one_of_kappa_mem_inn ((hπ.ker _).1 hb)

omit hπ in
theorem pi_kappa_mem (b : ↥B) : π (c.kappa b) ∈ alternatingGroup (Fin 5) := by
  obtain ⟨eB⟩ := c.h.ob.B_iso
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥B := MulEquiv.isSimpleGroup eB
  let χ : ↥B →* ℤˣ := Equiv.Perm.sign.comp (π.comp c.kappa)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal χ.ker with h1 | h1
  · exfalso
    have hinj : Function.Injective χ := (MonoidHom.ker_eq_bot_iff χ).1 h1
    have h60 : Nat.card ↥B = 60 := c.h.B_card
    have : Nat.card ↥B ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ hinj
    rw [h60, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
    omega
  · have : χ b = 1 := by
      have hb : b ∈ χ.ker := by rw [h1]; exact mem_top b
      exact hb
    exact Equiv.Perm.mem_alternatingGroup.2 this

theorem exists_pi_kappa {s : Equiv.Perm (Fin 5)} (hs : s ∈ alternatingGroup (Fin 5)) :
    ∃ b : ↥B, π (c.kappa b) = s := by
  have hle : (π.comp c.kappa).range ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨b, rfl⟩
    exact c.pi_kappa_mem (π := π) b
  have hcard : Nat.card (alternatingGroup (Fin 5)) ≤ Nat.card (π.comp c.kappa).range := by
    rw [Nat.card_congr (MonoidHom.ofInjective (c.pi_kappa_injective hπ)).toEquiv.symm,
      c.h.B_card]
    have := nat_card_alternatingGroup (α := Fin 5)
    rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hs' : s ∈ (π.comp c.kappa).range := by rw [heq]; exact hs
  obtain ⟨b, hb⟩ := hs'
  exact ⟨b, hb⟩

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
