module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

universe u v

@[expose] def duadStab (i j : Fin 24) : Subgroup ↥AutPerm :=
  ((AutPerm ⊓ stab i) ⊓ stab j).subgroupOf AutPerm

theorem mem_duadStab_iff {i j : Fin 24} {σ : ↥AutPerm} :
    σ ∈ duadStab i j ↔ (σ : Equiv.Perm (Fin 24)) i = i ∧ (σ : Equiv.Perm (Fin 24)) j = j := by
  simp only [duadStab, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_stab_iff]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨σ.2, h.1⟩, h.2⟩⟩

theorem t0_eq_kappa_pairVec : CocodeModelPair.t0 = cocodeCoords.κ (pairVec 1 3) := by
  change toW 11 32 = Multiplicative.ofAdd (ccE (Multiplicative.toAdd (pairVec 1 3)))
  rw [toAdd_pairVec 1 3 (by decide), ccE_bvec]
  have h : actM ccECols (pairMask ((1 : Fin 24) : ℕ) ((3 : Fin 24) : ℕ)) = 32 := by decide
  rw [h]
  rfl

theorem rho11_kappa_pairVec (σ : ↥AutPerm) (x y : Fin 24) :
    rho11 AutPerm le_rfl σ (cocodeCoords.κ (pairVec x y)) =
      cocodeCoords.κ (pairVec ((σ : Equiv.Perm (Fin 24)) x) ((σ : Equiv.Perm (Fin 24)) y)) := by
  rw [← permAct_pairVec]
  exact (cocodeCoords.κ_permAct_rho AutPerm
    (fun _ hσ => preserves_cocode hσ) σ (pairVec_mem_coreMod x y)).symm

namespace CocodeExtension

variable {N : Type u} [Group N] {E : Subgroup N} {e : ↥E ≃* W11}
  (h : CocodeExtension N E e)

@[expose] noncomputable def Bduad (i j : Fin 24) : Subgroup N :=
  (duadStab i j).comap h.π

theorem mem_Bduad_iff {i j : Fin 24} {n : N} :
    n ∈ h.Bduad i j ↔ ((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j :=
  mem_duadStab_iff

theorem le_Bduad (i j : Fin 24) : E ≤ h.Bduad i j := fun x hx => by
  rw [Bduad, Subgroup.mem_comap, h.π_eq_one_iff.2 hx]
  exact (duadStab i j).one_mem

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
