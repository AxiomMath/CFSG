module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Bookkeeping
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Shape

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {m n : ℕ}

theorem natShape_of_natVia {X : Type} [CommGroup X] {K : Subgroup (MulAut X)}
    {κ : ↥K →* Perm (Fin m)} {G : Type*} [Group G] (r : G →* ↥K) (α : G →* Perm (Fin m))
    (hr : ∀ g, κ (r g) = α g) (hα : ∀ g, α g ∈ alternatingGroup (Fin m))
    (h : NatVia κ (commV K)) : NatShape (K.subtype.comp r) α := by
  obtain ⟨π, hπ, hker, heq⟩ := h
  refine ⟨commV K ⊓ fixV (altPre κ), commV K, inf_le_left, fun g v hv => ?_, fun g v => ?_, π,
    hπ, hker, fun g u v huv => ?_⟩
  · exact hv.2 _ (coe_mem_altPre_iff.2 (by rw [hr]; exact hα g))
  · exact mul_inv_mem_commV (r g).2 v
  · rw [heq (r g) u v huv, hr]

section Rho

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin n)}

@[expose] noncomputable def altRho (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) : alternatingGroup (Fin n) →* MulAut V :=
  (altPre ψ).subtype.comp (altPreEquiv hψ hA).symm.toMonoidHom

theorem altRho_eq (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    {h : ↥H} {σ : alternatingGroup (Fin n)} (hh : ψ h = σ) : altRho hψ hA σ = h := by
  have hL : (h : MulAut V) ∈ altPre ψ := coe_mem_altPre_iff.2 (hh ▸ σ.2)
  have he : altPreEquiv hψ hA ⟨h, hL⟩ = σ := Subtype.ext (by rw [coe_altPreEquiv]; exact hh)
  change (((altPreEquiv hψ hA).symm σ : ↥(altPre ψ)) : MulAut V) = h
  rw [← he, MulEquiv.symm_apply_apply]

theorem altRho_mem (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (σ : alternatingGroup (Fin n)) : altRho hψ hA σ ∈ H :=
  altPre_le ((altPreEquiv hψ hA).symm σ).2

theorem apply_altRho (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (σ : alternatingGroup (Fin n)) : ψ ⟨altRho hψ hA σ, altRho_mem hψ hA σ⟩ = σ := by
  have h := congrArg Subtype.val ((altPreEquiv hψ hA).apply_symm_apply σ)
  rw [coe_altPreEquiv] at h
  exact h

theorem altRho_injective (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range) :
    Function.Injective (altRho hψ hA) :=
  (altPre ψ).subtype_injective.comp (altPreEquiv hψ hA).symm.injective

theorem natShape_altRho_comp_altLift (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {K : Subgroup (MulAut V)} (κ : ↥K →* Perm (Fin m))
    (ι : Fin m ↪ Fin n)
    (hlift : ∀ σ : alternatingGroup (Fin m), ∃ k : ↥K, κ k = σ ∧
      ∃ hk : (k : MulAut V) ∈ H, ψ ⟨k, hk⟩ = altLift ι σ)
    (h : NatVia κ (commV K)) :
    NatShape ((altRho hψ hA).comp (altLift ι)) (alternatingGroup (Fin m)).subtype := by
  choose k hk hkH hψk using hlift
  have hρ : ∀ σ, altRho hψ hA (altLift ι σ) = (k σ : MulAut V) := fun σ =>
    altRho_eq hψ hA (h := ⟨k σ, hkH σ⟩) (hψk σ)
  have hmem : ∀ σ, ((altRho hψ hA).comp (altLift ι)) σ ∈ K := fun σ => by
    rw [MonoidHom.comp_apply, hρ]
    exact (k σ).2
  have hr : ∀ σ, κ (((altRho hψ hA).comp (altLift ι)).codRestrict K hmem σ) =
      (alternatingGroup (Fin m)).subtype σ := fun σ => by
    have : ((altRho hψ hA).comp (altLift ι)).codRestrict K hmem σ = k σ := Subtype.ext (hρ σ)
    rw [this, hk]
    rfl
  exact natShape_of_natVia _ (alternatingGroup (Fin m)).subtype hr (fun σ => σ.2) h

theorem natVia_commV_of_natShape (hn : 7 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range)
    (h : NatShape (altRho hψ hA) (alternatingGroup (Fin n)).subtype) : NatVia ψ (commV H) := by
  have h1 := h.comp (altPreEquiv hψ hA).toMonoidHom
  have e1 : (altRho hψ hA).comp (altPreEquiv hψ hA).toMonoidHom = (altPre ψ).subtype :=
    MonoidHom.ext fun l => by
      change (((altPreEquiv hψ hA).symm (altPreEquiv hψ hA l) : ↥(altPre ψ)) : MulAut V) = l
      rw [MulEquiv.symm_apply_apply]
  have e2 : (alternatingGroup (Fin n)).subtype.comp (altPreEquiv hψ hA).toMonoidHom =
      (alternatingGroup (Fin n)).subtype.comp (altPreHom ψ) :=
    MonoidHom.ext fun _ => rfl
  rw [e1, e2] at h1
  exact (natVia_commV_of_isAltNaturalSection hn hψ hA (isAltNaturalSection_of_natShape (by omega)
    (altPre ψ) (altPreHom ψ) (altPreHom_surjective hA) h1)).2

end Rho

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
