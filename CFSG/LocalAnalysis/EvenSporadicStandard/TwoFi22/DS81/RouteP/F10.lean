module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.T0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)

universe u

theorem rho11_kappa_pairVec_of_mem_duadStabPlus {i j : Fin 24} {σ : ↥AutPerm}
    (hσ : σ ∈ duadStabPlus i j) :
    rho11 AutPerm le_rfl σ (cocodeCoords.κ (pairVec i j)) = cocodeCoords.κ (pairVec i j) := by
  rw [rho11_kappa_pairVec]
  rcases mem_duadStabPlus_iff.1 hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
  · rw [h0, h1, pairVec, pairVec, mul_comm]

namespace CocodeExtension

variable {N : Type u} [Group N] {E : Subgroup N} {e : ↥E ≃* W11} (h : CocodeExtension N E e)

@[expose] noncomputable def Bhat (i j : Fin 24) : Subgroup N :=
  (duadStabPlus i j).comap h.π

theorem mem_Bhat_iff {i j : Fin 24} {n : N} :
    n ∈ h.Bhat i j ↔
      ((((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
          ((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j) ∨
        (((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = j ∧
          ((h.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = i)) :=
  Iff.rfl

theorem Bduad_le_Bhat (i j : Fin 24) :
    h.Bduad i j ≤ h.Bhat i j := fun _ hn => Or.inl (h.mem_Bduad_iff.1 hn)

theorem conj_eq_of_mem_Bhat {i j : Fin 24} {x : ↥E}
    (hx : e x = cocodeCoords.κ (pairVec i j)) {n : N} (hn : n ∈ h.Bhat i j) :
    n * x * n⁻¹ = x := by
  have h1 := h.π_apply_e n x
  rw [hx, rho11_kappa_pairVec_of_mem_duadStabPlus hn, ← hx] at h1
  have h2 := congrArg Subtype.val (e.injective h1).symm
  rw [h.coe_conjE] at h2
  exact h2

theorem exists_conj_of_aut_Bduad
    {i j : Fin 24} (hij : i ≠ j) (γ : ↥(h.Bduad i j) ≃* ↥(h.Bduad i j)) :
    ∃ c ∈ h.Bhat i j, ∀ b : ↥(h.Bduad i j),
      ((γ b : ↥(h.Bduad i j)) : N) = c * (b : N) * c⁻¹ := by
  obtain ⟨c, hc, hγ⟩ := h.toExtData.exists_conj_of_aut_duad hij (fun _ => h.mem_Bduad_iff) γ
  exact ⟨c, hc, hγ⟩

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
