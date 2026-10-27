module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PairAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Wr

variable (σ : Equiv.Perm (Fin 5))

@[expose] def xW : Wr2 (Equiv.Perm (Fin 5)) := base σ σ * tau

theorem xW_sq (hσ : σ * σ = 1) : xW σ * xW σ = 1 := by
  rw [xW, base_mul_tau_sq, hσ, base_one]

theorem xW_comm_tau_mul : xW σ = tau * base σ σ := by
  rw [xW, tau_mul_base]

abbrev GW : Subgroup (Wr2 (Equiv.Perm (Fin 5))) := centralizer ({xW σ} : Set _)

theorem base_mem_GW_iff {p q : Equiv.Perm (Fin 5)} (hσ : σ * σ = 1) :
    base p q ∈ GW σ ↔ q = σ * p * σ⁻¹ := by
  have hi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  show base p q ∈ centralizer ({base σ σ * tau} : Set (Wr2 (Equiv.Perm (Fin 5)))) ↔ _
  rw [mem_centralizer_base_mul_tau_iff]
  constructor
  · rintro ⟨h1, -⟩
    have : q⁻¹ = σ⁻¹ * p⁻¹ * σ := by
      calc q⁻¹ = (p * σ)⁻¹ * (p * σ * q⁻¹) := by group
        _ = (p * σ)⁻¹ * σ := by rw [h1]
        _ = σ⁻¹ * p⁻¹ * σ := by group
    have h2 : q = (σ⁻¹ * p⁻¹ * σ)⁻¹ := by rw [← this]; simp
    rw [h2, hi]
    simp only [mul_inv_rev, inv_inv, hi, mul_assoc]
  · intro h
    subst h
    rw [hi]
    refine ⟨?_, ?_⟩
    · calc p * σ * (σ * p * σ)⁻¹ = σ⁻¹ := by group
        _ = σ := hi
    · calc σ * p * σ * σ * p⁻¹ = σ * p * (σ * σ) * p⁻¹ := by group
        _ = σ := by rw [hσ]; group

@[expose] def nuW (hσ : σ * σ = 1) : Equiv.Perm (Fin 5) →* GW σ where
  toFun a := ⟨base a (σ * a * σ⁻¹), (base_mem_GW_iff σ hσ).2 rfl⟩
  map_one' := by
    refine Subtype.ext ?_
    change base 1 (σ * 1 * σ⁻¹) = 1
    simp [base_one]
  map_mul' a b := by
    refine Subtype.ext ?_
    change base (a * b) (σ * (a * b) * σ⁻¹) = base a (σ * a * σ⁻¹) * base b (σ * b * σ⁻¹)
    have e : σ * (a * b) * σ⁻¹ = σ * a * σ⁻¹ * (σ * b * σ⁻¹) := by group
    rw [base_mul_base, e]

theorem nuW_injective (hσ : σ * σ = 1) : Function.Injective (nuW σ hσ) := by
  intro a b h
  have := congrArg Subtype.val h
  exact (base_injective.1 this).1

@[expose] def zW : GW σ := ⟨xW σ, mem_centralizer_singleton_iff.2 rfl⟩

theorem zW_central (g : GW σ) : g * zW σ = zW σ * g :=
  Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

theorem zW_sq (hσ : σ * σ = 1) : zW σ * zW σ = 1 := Subtype.ext (xW_sq σ hσ)

theorem zW_not_mem_range (hσ : σ * σ = 1) : zW σ ∉ (nuW σ hσ).range := by
  rintro ⟨a, ha⟩
  have h := congrArg Subtype.val ha
  change base a (σ * a * σ⁻¹) = base σ σ * tau at h
  exact base_ne_base_mul_tau _ _ _ _ h

theorem zW_cov (hσ : σ * σ = 1) (g : GW σ) :
    g ∈ (nuW σ hσ).range ∨ zW σ * g ∈ (nuW σ hσ).range := by
  rcases eq_base_or_eq_base_mul_tau (g : Wr2 (Equiv.Perm (Fin 5))) with ⟨p, q, hg⟩ | ⟨p, q, hg⟩
  · left
    have hmem : base p q ∈ GW σ := hg ▸ g.2
    refine ⟨p, Subtype.ext ?_⟩
    change base p (σ * p * σ⁻¹) = g
    rw [hg, (base_mem_GW_iff σ hσ).1 hmem]
  · right
    have hprod : (zW σ * g : GW σ).1 = base (σ * q) (σ * p) := by
      change xW σ * (g : Wr2 (Equiv.Perm (Fin 5))) = _
      rw [xW, hg, base_mul_tau_mul_base_mul_tau]
    have hmem : base (σ * q) (σ * p) ∈ GW σ := hprod ▸ (zW σ * g).2
    refine ⟨σ * q, Subtype.ext ?_⟩
    have h := (base_mem_GW_iff σ hσ).1 hmem
    change base (σ * q) (σ * (σ * q) * σ⁻¹) = (zW σ * g : GW σ).1
    rw [hprod, h]

@[expose] noncomputable def kapW (hσ : σ * σ = 1) : GW σ →* Equiv.Perm (Fin 5) :=
  (((MonoidHom.ofInjective (nuW_injective σ hσ)).symm :
    ↥(nuW σ hσ).range ≃* Equiv.Perm (Fin 5)).toMonoidHom).comp
    (retraction (zW_central σ) (zW_sq σ hσ) (nuW σ hσ).range (zW_cov σ hσ))

theorem kapW_nuW (hσ : σ * σ = 1) (a : Equiv.Perm (Fin 5)) : kapW σ hσ (nuW σ hσ a) = a := by
  have hmem : nuW σ hσ a ∈ (nuW σ hσ).range := ⟨a, rfl⟩
  have h : retraction (zW_central σ) (zW_sq σ hσ) (nuW σ hσ).range (zW_cov σ hσ) (nuW σ hσ a) =
      ⟨nuW σ hσ a, hmem⟩ :=
    Subtype.ext (retraction_of_mem _ _ _ _ hmem)
  rw [kapW, MonoidHom.comp_apply, h]
  apply (nuW_injective σ hσ)
  have := MulEquiv.apply_symm_apply (MonoidHom.ofInjective (nuW_injective σ hσ))
    (⟨nuW σ hσ a, hmem⟩ : ↥(nuW σ hσ).range)
  exact congrArg Subtype.val this

theorem kapW_eq_one_iff (hσ : σ * σ = 1) (g : GW σ) :
    kapW σ hσ g = 1 ↔ g = 1 ∨ g = zW σ := by
  rw [← retraction_eq_one_iff (zW_central σ) (zW_sq σ hσ) (nuW σ hσ).range
    (zW_not_mem_range σ hσ) (zW_cov σ hσ)]
  rw [kapW, MonoidHom.comp_apply]
  constructor
  · intro h
    exact (MulEquiv.map_eq_one_iff _).1 h
  · intro h
    rw [h]
    exact map_one _

theorem sgnProd_xW (hσ : σ * σ = 1) : sgnProd (xW σ) = 1 := by
  rw [xW, map_mul, sgnProd_base, sgnProd_tau, mul_one, ← map_mul, hσ, map_one]

theorem sgnProd_GW (hσ : σ * σ = 1) (w : GW σ) : sgnProd (w : Wr2 (Equiv.Perm (Fin 5))) = 1 := by
  have hν : ∀ a, sgnProd ((nuW σ hσ a : GW σ) : Wr2 (Equiv.Perm (Fin 5))) = 1 := by
    intro a
    change sgnProd (base a (σ * a * σ⁻¹)) = 1
    rw [sgnProd_base, map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign σ), mul_assoc,
      mul_inv_cancel, mul_one, ← sq, Int.units_pow_two]
  rcases zW_cov σ hσ w with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha]; exact hν a
  · have h1 : sgnProd (((zW σ * w : GW σ)) : Wr2 (Equiv.Perm (Fin 5))) = 1 := by
      rw [← ha]; exact hν a
    have h2 : sgnProd (((zW σ * w : GW σ)) : Wr2 (Equiv.Perm (Fin 5))) =
        sgnProd (xW σ) * sgnProd (w : Wr2 (Equiv.Perm (Fin 5))) := by
      change sgnProd (xW σ * (w : Wr2 (Equiv.Perm (Fin 5)))) = _
      rw [map_mul]
    rw [h2, sgnProd_xW σ hσ, one_mul] at h1
    exact h1

end Wr

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
