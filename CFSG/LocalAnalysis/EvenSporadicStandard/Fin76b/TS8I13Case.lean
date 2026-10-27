module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Pi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Dich5

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

theorem sigma_mem_N1 : σ ∈ c.N1 :=
  c.mem_N1.2 ⟨c.M_le_Nc (OHyp69.sigma_mem_M c.hσ), c.hσ.fix_alpha⟩

theorem rho_sigma :
    c.rho ⟨σ, c.sigma_mem_N1⟩ = (convN ⟨σ, c.hσ.norm_E⟩, convN ⟨σ, c.hσ.norm_E⟩) :=
  c.rho_conv ⟨σ, c.sigma_mem_N1⟩ c.hσ.comm_z c.hσ.norm_E

variable {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)

include hπ in
theorem pi_sigma_odd : π (convN ⟨σ, c.hσ.norm_E⟩) ∉ alternatingGroup (Fin 5) := by
  intro hodd
  obtain ⟨b, hb⟩ := c.exists_pi_kappa hπ hodd
  have hker : convN (⟨σ, c.hσ.norm_E⟩ : normalizer (E : Set G)) * (c.kappa b)⁻¹ ∈ innAutE E :=
    (hπ.ker _).1 (by rw [map_mul, map_inv, hb, mul_inv_cancel])
  obtain ⟨e, he⟩ := hker
  have hinv : ∀ ℓ : normalizer (E : Set G), convN ℓ⁻¹ = (convN ℓ)⁻¹ :=
    fun ℓ => map_inv E.normalizerMonoidHom ℓ
  have he' : MulAut.conj e = convN ((⟨σ, c.hσ.norm_E⟩ : normalizer (E : Set G)) *
      (⟨(b : G), c.B_le_normE b.2⟩ : normalizer (E : Set G))⁻¹) := by
    rw [convN_mul, hinv, ← c.kappa_eq_convN b]
    exact he
  have hrel : ∀ x : G, ∀ hx : x ∈ E,
      (e : G) * x * (e : G)⁻¹ = σ * (b : G)⁻¹ * x * (σ * (b : G)⁻¹)⁻¹ := by
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥E => ((φ ⟨x, hx⟩ : ↥E) : G)) he'
    exact h1
  have hkE : (e : G)⁻¹ * (σ * (b : G)⁻¹) ∈ centralizer (E : Set G) := by
    refine mem_centralizer_iff.2 fun x hx => ?_
    calc x * ((e : G)⁻¹ * (σ * (b : G)⁻¹))
        = (e : G)⁻¹ * ((e : G) * x * (e : G)⁻¹) * (σ * (b : G)⁻¹) := by group
      _ = (e : G)⁻¹ * (σ * (b : G)⁻¹ * x * (σ * (b : G)⁻¹)⁻¹) * (σ * (b : G)⁻¹) := by
          rw [hrel x hx]
      _ = (e : G)⁻¹ * (σ * (b : G)⁻¹) * x := by group
  have hez : (e : G)⁻¹ * z = z * (e : G)⁻¹ :=
    c.h.oe.cfg.z_comm_of_mem_A (c.h.oe.E_le_L (inv_mem e.2))
  have hbzi : (b : G)⁻¹ * z = z * (b : G)⁻¹ := by
    have hbz : (b : G) * z = z * (b : G) := c.h.BS b b.2 z c.h.zS
    calc (b : G)⁻¹ * z = (b : G)⁻¹ * (z * (b : G)) * (b : G)⁻¹ := by group
      _ = (b : G)⁻¹ * ((b : G) * z) * (b : G)⁻¹ := by rw [hbz]
      _ = z * (b : G)⁻¹ := by group
  have hkz : (e : G)⁻¹ * (σ * (b : G)⁻¹) * z = z * ((e : G)⁻¹ * (σ * (b : G)⁻¹)) := by
    calc (e : G)⁻¹ * (σ * (b : G)⁻¹) * z = (e : G)⁻¹ * (σ * ((b : G)⁻¹ * z)) := by group
      _ = (e : G)⁻¹ * (σ * (z * (b : G)⁻¹)) := by rw [hbzi]
      _ = (e : G)⁻¹ * ((σ * z) * (b : G)⁻¹) := by group
      _ = (e : G)⁻¹ * ((z * σ) * (b : G)⁻¹) := by rw [c.hσ.comm_z]
      _ = ((e : G)⁻¹ * z) * (σ * (b : G)⁻¹) := by group
      _ = (z * (e : G)⁻¹) * (σ * (b : G)⁻¹) := by rw [hez]
      _ = z * ((e : G)⁻¹ * (σ * (b : G)⁻¹)) := by group
  have hk' : (e : G)⁻¹ * (σ * (b : G)⁻¹) ∈ L ⊔ zpowers z := by
    rcases c.hM.centZ _ hkE hkz with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact one_mem _
    · exact mem_sup_right (mem_zpowers z)
    · exact mem_sup_left c.h.oe.cfg.t_mem_A
    · exact mul_mem (mem_sup_left c.h.oe.cfg.t_mem_A) (mem_sup_right (mem_zpowers z))
  apply c.hσ.not_mem
  have hσeq : σ = (e : G) * ((e : G)⁻¹ * (σ * (b : G)⁻¹)) * (b : G) := by group
  rw [hσeq]
  exact mul_mem (mul_mem (mem_sup_left (c.h.oe.E_le_L e.2)) hk') (mem_sup_left (c.h.ob.B_le b.2))

include hπ in
theorem rho_range_trichotomy :
    (∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ π a = π b) ∨
    (∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Perm.sign (π a) = Perm.sign (π b)) ∨
    (∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range) := by
  have hneg : ∀ u v : ℤˣ, u ≠ 1 → v ≠ 1 → u * v⁻¹ = 1 := by
    intro u v hu hv
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl
    · exact absurd rfl hu
    · exact absurd rfl hu
    · exact absurd rfl hv
    · decide
  refine trichotomy π c.rho.range ?_ ?_
  ·
    intro a b ha hb
    obtain ⟨e₁, he₁⟩ := (hπ.ker _).1 ha
    obtain ⟨e₂, he₂⟩ := (hπ.ker _).1 hb
    obtain ⟨q, hq, hρ⟩ := c.exists_rho_Qs e₁ e₂
    exact ⟨⟨q, c.Qs_le_N1 hq⟩, by rw [hρ, he₁, he₂]⟩
  ·
    intro s
    by_cases hs : s ∈ alternatingGroup (Fin 5)
    · obtain ⟨b, hb⟩ := c.exists_pi_kappa hπ hs
      exact ⟨c.kappa b, hb, ⟨⟨(b : G), c.B_le_N1 b.2⟩, c.rho_B b⟩⟩
    ·
      have hσ' : π (convN ⟨σ, c.hσ.norm_E⟩) ∉ alternatingGroup (Fin 5) := c.pi_sigma_odd hπ
      have hs' : s * (π (convN ⟨σ, c.hσ.norm_E⟩))⁻¹ ∈ alternatingGroup (Fin 5) := by
        rw [Perm.mem_alternatingGroup] at hs hσ' ⊢
        rw [map_mul, map_inv]
        exact hneg _ _ hs hσ'
      obtain ⟨b, hb⟩ := c.exists_pi_kappa hπ hs'
      refine ⟨c.kappa b * convN ⟨σ, c.hσ.norm_E⟩, ?_, ?_⟩
      · rw [map_mul, hb, inv_mul_cancel_right]
      · refine ⟨(⟨(b : G), c.B_le_N1 b.2⟩ : ↥c.N1) * (⟨σ, c.sigma_mem_N1⟩ : ↥c.N1), ?_⟩
        rw [map_mul, c.rho_B b, c.rho_sigma, Prod.mk_mul_mk]

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
