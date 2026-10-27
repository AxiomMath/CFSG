module

public import CFSG.ClassicalInvolution.Q3.TL3T36

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinDisc

namespace AE5

section Gen

variable {H : Type} [Group H]

theorem psi_center (ψ : MulAut H) {c : H} (hc : c ∈ Subgroup.center H) :
    ψ c ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro w
  apply ψ.symm.injective
  rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
  exact hc (ψ.symm w)

end Gen

section Ext

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

@[expose] noncomputable def inducedHomExt (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) :
    ↥(TL4.aeModel 5) →* ↥(TL4.aeModel 5) :=
  (QuotientGroup.lift I.toModel.ker (I.toModel.comp ψ.toMonoidHom) (by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, I.ker_toModel]
    rw [I.ker_toModel] at hx
    exact I.center_le_ker (by norm_num) (psi_center ψ (I.ker_le hx)))).comp
    (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm.toMonoidHom

theorem inducedHomExt_apply (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) (x : ↥(pSpan P)) :
    inducedHomExt I ψ (I.toModel x) = I.toModel (ψ x) := by
  simp only [inducedHomExt, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : (QuotientGroup.quotientKerEquivOfSurjective I.toModel I.toModel_surjective).symm
      (I.toModel x) = (x : ↥(pSpan P) ⧸ I.toModel.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this, QuotientGroup.lift_mk]
  rfl

theorem inducedHomExt_injective (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) :
    Function.Injective (inducedHomExt I ψ) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  obtain ⟨x, rfl⟩ := I.toModel_surjective m
  rw [inducedHomExt_apply] at hm
  have hk : ψ x ∈ I.φ.ker := by rw [← I.ker_toModel]; exact hm
  have hc := psi_center ψ.symm (I.ker_le hk)
  rw [MulEquiv.symm_apply_apply] at hc
  have hx := I.center_le_ker (by norm_num) hc
  rw [← I.ker_toModel] at hx
  exact hx

@[expose] noncomputable def inducedAutExt (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) :
    MulAut ↥(TL4.aeModel 5) :=
  MulEquiv.ofBijective (inducedHomExt I ψ)
    ⟨inducedHomExt_injective I ψ, Finite.injective_iff_surjective.mp (inducedHomExt_injective I ψ)⟩

theorem inducedAutExt_apply (I : AEIdent P 5) (ψ : MulAut ↥(pSpan P)) (x : ↥(pSpan P)) :
    inducedAutExt I ψ (I.toModel x) = I.toModel (ψ x) :=
  inducedHomExt_apply I ψ x

theorem fixed_of_cent (hgen : pSpan P = ⊤)
    (htrans : ∀ M ∈ P, ∀ N ∈ P, ∃ g : G, conjSub g M = N) {J : Subgroup G} (hJ : J ∈ P)
    (ψ : ↥(pSpan P) →* ↥(pSpan P))
    (hcent : ∀ g : ↥(pSpan P), g⁻¹ * ψ g ∈ Subgroup.center ↥(pSpan P))
    (hfix : ∀ y : ↥(pSpan P), (y : G) ∈ J → ψ y = y) : ∀ y, ψ y = y := by
  have hmem : ∀ M ∈ P, ∀ y (hy : y ∈ pSpan P), y ∈ M → ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
    intro M hM y hy hyM
    obtain ⟨g, hg⟩ := htrans J hJ M hM
    have hgP : g ∈ pSpan P := by rw [hgen]; exact Subgroup.mem_top g
    have hj : g⁻¹ * y * g ∈ J := by
      have : y ∈ conjSub g J := hg ▸ hyM
      exact mem_conjSub_iff.mp this
    set g' : ↥(pSpan P) := ⟨g, hgP⟩ with hg'
    set j' : ↥(pSpan P) := ⟨g⁻¹ * y * g, (pSpan P).mul_mem ((pSpan P).mul_mem
      ((pSpan P).inv_mem hgP) hy) hgP⟩ with hj'
    have hyeq : (⟨y, hy⟩ : ↥(pSpan P)) = g' * j' * g'⁻¹ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg', hj']
      group)
    have hψj : ψ j' = j' := hfix j' hj
    obtain ⟨κ, hκ⟩ : ∃ κ ∈ Subgroup.center ↥(pSpan P), ψ g' = g' * κ :=
      ⟨g'⁻¹ * ψ g', hcent g', by group⟩
    have hκc := Subgroup.mem_center_iff.mp hκ.1
    rw [hyeq, map_mul, map_mul, map_inv, hψj, hκ.2]
    have e : g' * κ * j' * (g' * κ)⁻¹ = g' * j' * g'⁻¹ := by
      calc g' * κ * j' * (g' * κ)⁻¹ = g' * (κ * j' * κ⁻¹) * g'⁻¹ := by group
        _ = g' * j' * g'⁻¹ := by rw [← hκc j', mul_inv_cancel_right]
    exact e
  intro y
  set S : Subgroup G := (MonoidHom.eqLocus ψ (MonoidHom.id _)).map (pSpan P).subtype with hS
  have hle : pSpan P ≤ S := pSpan_le fun M hM y hyM =>
    ⟨⟨y, le_pSpan hM hyM⟩, hmem M hM y (le_pSpan hM hyM) hyM, rfl⟩
  obtain ⟨s, hs, hsy⟩ := hle y.2
  have : s = y := Subtype.ext hsy
  rw [← this]
  exact hs

end Ext

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
