module

public import CFSG.CGT.Foote82.T66.CaseITheta
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.CaseIU

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem isAltHeartFor_of_heartFor {X X' : Subgroup (GLV V)} {N : ℕ} {ρ : ↥X →* Perm (Fin N)}
    {β : ↥(commSpace X' ⊤) →+ altHeart N} (hβ : HeartFor X N ρ X' β) (hN : 3 ≤ N)
    (hirr : IsIrr X' ⊤) (φ : ↥X' ≃* alternatingGroup (Fin N))
    (hφ : ∀ e : ↥X', ρ ⟨e, hβ.le e.2⟩ = ((φ e : alternatingGroup (Fin N)) : Perm (Fin N))) :
    IsAltHeartFor X' N := by
  have hinvC : Invariant X' (commSpace X' ⊤) := invariant_commSpace
    (fun k' hk' k hk => X'.mul_mem (X'.mul_mem hk' hk) (X'.inv_mem hk')) (invariant_top X')
  have hC : commSpace X' ⊤ = ⊤ := by
    rcases hirr.2.2 _ hinvC bot_le le_top with h0 | h1
    · exfalso
      haveI := altHeart_nontrivial (n := N) hN
      obtain ⟨a, ha⟩ := exists_ne (0 : altHeart N)
      obtain ⟨w, rfl⟩ := hβ.surj a
      apply ha
      have hw : (w : V) = 0 := (Submodule.mem_bot _).1 (h0.le w.2)
      rw [show w = 0 from Subtype.ext hw, map_zero]
    · exact h1
  have hinvF : Invariant X' (fixedSpace X') := fun x hx w hw => by
    rw [hw x hx]; exact hw
  have hF : fixedSpace X' = ⊥ := by
    rcases hirr.2.2 _ hinvF bot_le le_top with h0 | h1
    · exact h0
    · exfalso
      have h2 : commSpace X' ⊤ = ⊥ := by
        rw [eq_bot_iff]
        refine commSpace_le_iff.2 fun k hk u _ => ?_
        have : u ∈ fixedSpace X' := by rw [h1]; trivial
        rw [this k hk, sub_self]
        exact Submodule.zero_mem _
      rw [h2] at hC
      exact hirr.2.1.ne hC
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hk : w ∈ β.ker := hw
    rw [hβ.ker] at hk
    have h1 : (w : V) ∈ fixedSpace X' := hk
    rw [hF] at h1
    exact Subtype.ext ((Submodule.mem_bot _).1 h1)
  let eV : V ≃+ ↥(commSpace X' ⊤) := (LinearEquiv.ofTop _ hC).symm.toAddEquiv
  let eβ : ↥(commSpace X' ⊤) ≃+ altHeart N :=
    { Equiv.ofBijective β ⟨hinj, hβ.surj⟩ with map_add' := β.map_add }
  have heV : ∀ w : V, ((eV w : ↥(commSpace X' ⊤)) : V) = w := fun w => by
    show ((LinearEquiv.ofTop _ hC).symm w : V) = w
    rw [LinearEquiv.ofTop_symm_apply]
  refine ⟨φ, eV.trans eβ, fun e w x hx => ?_⟩
  have h2 := hβ.equiv ⟨e, hβ.le e.2⟩ (eV w) (eV ((e : GLV V) w)) (by rw [heV, heV]) x hx
  show β (eV ((e : GLV V) w)) = _
  rw [h2, hφ]

theorem Hyp.isAltHeartFor_H (h : Hyp G L z v H₁ m ψ) (hirr : IsIrr (HH G L v) ⊤) :
    IsAltHeartFor (HH G L v) (m + 6 + 2) := by
  obtain ⟨β, hβ⟩ := h.heartFor
  let φ : ↥(HH G L v) ≃* alternatingGroup (Fin (m + 6 + 2)) :=
    ((MonoidHom.ofInjective (jH_injective (ψ := ψ))).trans
      (MulEquiv.subgroupCongr h.range_jH)).symm
  have hφ : ∀ e : ↥(HH G L v), jH ψ (φ e) = e := fun e => by
    have := MulEquiv.apply_symm_apply ((MonoidHom.ofInjective (jH_injective (ψ := ψ))).trans
      (MulEquiv.subgroupCongr h.range_jH)) e
    exact congrArg Subtype.val this
  refine isAltHeartFor_of_heartFor hβ (by omega) hirr φ fun e => ?_
  have h1 : (⟨e, hβ.le e.2⟩ : ↥H₁) = ⟨jH ψ (φ e), pe_mem _⟩ := Subtype.ext (hφ e).symm
  rw [h1]
  exact psi_pe _

end CaseIAux

end CFSG.CGT.Foote82
