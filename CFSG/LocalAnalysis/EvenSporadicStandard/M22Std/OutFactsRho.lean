module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabGroup
public import CFSG.Monster.B.TwoA.Fischer.M22Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Fischer CFSG.Monster.Code
  CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.Blueprint.NativeSporadic

attribute [local instance] restAction

@[expose] noncomputable def restEquiv : Fin 22 ≃ Rest :=
  Equiv.ofBijective (fun i => ⟨jCat i, jCat_ne i⟩)
    ⟨fun i j h => jCat_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨i, hi⟩ := exists_jCat x.1 x.2.1 x.2.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[expose] noncomputable def sigHom : Ppair →* Equiv.Perm (Fin 22) :=
  (restEquiv.symm.permCongrHom : Equiv.Perm Rest ≃* Equiv.Perm (Fin 22)).toMonoidHom.comp
    (MulAction.toPermHom Ppair Rest)

theorem jCat_sigHom (p : Ppair) (i : Fin 22) :
    jCat (sigHom p i) = ((p : AutPerm) : Equiv.Perm (Fin 24)) (jCat i) := by
  have h : restEquiv (sigHom p i) = p • restEquiv i := by
    show restEquiv (restEquiv.symm (p • restEquiv i)) = _
    simp
  exact congrArg Subtype.val h

theorem sigHom_injective : Function.Injective sigHom := by
  intro p q h
  have h1 : (MulAction.toPermHom Ppair Rest) p = (MulAction.toPermHom Ppair Rest) q :=
    restEquiv.symm.permCongrHom.injective h
  exact MulAction.toPerm_injective (α := Ppair) (β := Rest) h1

theorem innerImage_top_eq_inner (Y : Type*) [Group Y] :
    innerImage Y ⊤ = CFSG.ComponentClassification.OuterAutomorphisms.inner Y :=
  Subgroup.map_top _

section Action


theorem coe_P0inEquiv_symm (y : Carrier .M22) :
    ((((P0inEquiv.symm y : P0in) : Ppair) : AutPerm) : Equiv.Perm (Fin 24)) =
      psiHom (toPerm y) :=
  coe_m22EquivP0 y

theorem toPerm_autEmbed (p : Ppair) (y : Carrier .M22) :
    toPerm (autEmbed p y) = sigHom p * toPerm y * (sigHom p)⁻¹ := by
  set z : Carrier .M22 := autEmbed p y with hz
  have h1 : P0inEquiv.symm z = MulAut.conjNormal (H := P0in) p (P0inEquiv.symm y) := by
    have : z = P0inEquiv (MulAut.conjNormal (H := P0in) p (P0inEquiv.symm y)) := rfl
    rw [this, MulEquiv.symm_apply_apply]
  have h2 : psiHom (toPerm z) = ((p : AutPerm) : Equiv.Perm (Fin 24)) * psiHom (toPerm y) *
      ((p : AutPerm) : Equiv.Perm (Fin 24))⁻¹ := by
    rw [← coe_P0inEquiv_symm, h1, ← coe_P0inEquiv_symm]
    simp [MulAut.conjNormal_apply]
  have hinv : ∀ i : Fin 22, ((p : AutPerm) : Equiv.Perm (Fin 24))⁻¹ (jCat i) =
      jCat ((sigHom p)⁻¹ i) := fun i => by
    have := jCat_sigHom p⁻¹ i
    rw [map_inv] at this
    exact this.symm
  refine Equiv.ext fun i => jCat_injective ?_
  have h3 := congrArg (fun f : Equiv.Perm (Fin 24) => f (jCat i)) h2
  simp only [Equiv.Perm.coe_mul, Function.comp_apply] at h3
  rw [← psiHom_jCat, h3, hinv, psiHom_jCat, ← jCat_sigHom]
  rfl

theorem toPerm_inj : Function.Injective toPerm := Subtype.val_injective

theorem sigHom_P0inEquiv_symm (y : Carrier .M22) :
    sigHom (P0inEquiv.symm y : Ppair) = toPerm y := by
  refine Equiv.ext fun i => jCat_injective ?_
  rw [jCat_sigHom, coe_P0inEquiv_symm, psiHom_jCat]

end Action

section Rho


theorem autEmbed_bijective :
    Function.Bijective (autEmbed : Ppair →* MulAut (Carrier .M22)) :=
  catalog_M22_full_automorphism_order.2.2.2.1

@[expose] noncomputable def autEquiv : Ppair ≃* MulAut (Carrier .M22) :=
  MulEquiv.ofBijective autEmbed autEmbed_bijective

@[expose] noncomputable def rho : MulAut (Carrier .M22) →* Equiv.Perm (Fin 22) :=
  sigHom.comp autEquiv.symm.toMonoidHom

theorem rho_autEmbed (p : Ppair) : rho (autEmbed p) = sigHom p := by
  have : autEquiv.symm (autEmbed p) = p := autEquiv.symm_apply_apply p
  exact congrArg sigHom this

theorem rho_injective : Function.Injective rho := by
  intro α β h
  have h1 := sigHom_injective h
  exact autEquiv.symm.injective h1

theorem toPerm_apply_rho (α : MulAut (Carrier .M22)) (y : Carrier .M22) :
    toPerm (α y) = rho α * toPerm y * (rho α)⁻¹ := by
  obtain ⟨p, rfl⟩ := autEmbed_bijective.2 α
  rw [rho_autEmbed]
  exact toPerm_autEmbed p y

theorem rho_conj (y : Carrier .M22) : rho (MulAut.conj y) = toPerm y := by
  have h : MulAut.conj y = autEmbed (P0inEquiv.symm y : Ppair) := by
    rw [autEmbed_coe_P0in]
    exact congrArg MulAut.conj (P0inEquiv.apply_symm_apply y).symm
  rw [h, rho_autEmbed, sigHom_P0inEquiv_symm]

theorem autEmbed_mem_innerImage_iff (p : Ppair) :
    autEmbed p ∈ innerImage (Carrier .M22) ⊤ ↔
      ((p : AutPerm) : Equiv.Perm (Fin 24)) 0 = 0 ∧
        ((p : AutPerm) : Equiv.Perm (Fin 24)) 1 = 1 := by
  have key : ∀ q : Ppair, autEmbed q ∈ P0in.map autEmbed ↔ q ∈ P0in := fun q =>
    Subgroup.mem_map_iff_mem autEmbed_bijective.1
  have hmap : P0in.map autEmbed =
      CFSG.ComponentClassification.OuterAutomorphisms.inner (CFSG.Blueprint.NativeSporadic.M22) :=
    catalog_M22_full_automorphism_order.2.2.2.2
  have h1 : autEmbed p ∈ innerImage (Carrier .M22) ⊤ ↔ p ∈ P0in := by
    rw [innerImage_top_eq_inner]
    rw [hmap] at key
    exact key p
  rw [h1, P0in, Subgroup.mem_subgroupOf, mem_P0_iff]

theorem index_innerImage_top : (innerImage (Carrier .M22) ⊤).index = 2 := by
  rw [innerImage_top_eq_inner]
  exact catalog_M22_full_automorphism_order.2.1

end Rho



end CFSG.EvenSporadicStandard.M22Std
