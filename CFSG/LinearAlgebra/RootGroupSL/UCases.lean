module

public import CFSG.LinearAlgebra.RootGroupSL.UCasesStep
public import CFSG.LinearAlgebra.RootGroupSL.NormOneGen
public import CFSG.LinearAlgebra.RootGroupSL.UCasesIrr

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open UCasesStep

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem eq_datumU1_or_eq_datumU2_std (hd : 2 ≤ Module.finrank k E)
    (U : Subgroup (SpecialLinearGroup k (DSpace E X)))
    (hQ0 : datumQ0 (stdIota k E X) (stdPi k E X) ≤ U) (hUQ : U ≤ QK k E X) (hne : U ≠ QK k E X)
    (hN : Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ≤
      Subgroup.normalizer (U : Set (SpecialLinearGroup k (DSpace E X))))
    (hnc : ¬ QK k E X ≤ Subgroup.centralizer (U : Set (SpecialLinearGroup k (DSpace E X)))) :
    U = datumU1 (stdIota k E X) ∨ U = datumU2 (stdPi k E X) := by
  classical
  haveI hfinE : Module.Finite k E := by
    rw [Module.finite_def, Submodule.fg_def]
    exact ⟨Set.univ, Set.finite_univ, Submodule.span_univ⟩
  obtain ⟨ν, hνnorm, hνne, hνgen⟩ := exists_norm_one_generator (k := k) (E := E) hd
  let M₁ : AddSubgroup (X →ₗ[k] E) :=
    { carrier := {φ | uSL φ 0 0 ∈ U}
      add_mem' := by
        intro φ φ' hφ hφ'
        have h := U.mul_mem hφ hφ'
        rw [uSL_mul] at h
        simpa using h
      zero_mem' := by simpa [uSL_zero] using U.one_mem
      neg_mem' := by
        intro φ hφ
        have hneg : (-φ : X →ₗ[k] E) = φ := by ext x; exact neg_eq_self_mod k (φ x)
        rwa [hneg] }
  let M₂ : AddSubgroup (E →ₗ[k] X) :=
    { carrier := {χ | uSL 0 χ 0 ∈ U}
      add_mem' := by
        intro χ χ' hχ hχ'
        have h := U.mul_mem hχ hχ'
        rw [uSL_mul] at h
        simpa using h
      zero_mem' := by simpa [uSL_zero] using U.one_mem
      neg_mem' := by
        intro χ hχ
        have hneg : (-χ : E →ₗ[k] X) = χ := by ext x; exact neg_eq_self_mod k (χ x)
        rwa [hneg] }
  have hconj : ∀ {B : SpecialLinearGroup k (DSpace E X)},
      B ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) →
      ∀ {u : SpecialLinearGroup k (DSpace E X)}, u ∈ U → B * u * B⁻¹ ∈ U := by
    intro B hB u hu
    exact (Subgroup.mem_normalizer_iff.mp (hN hB) u).mp hu
  have hM1E : ∀ (s : E) (φ : X →ₗ[k] E), φ ∈ M₁ → LinearMap.mulLeft k s ∘ₗ φ ∈ M₁ := by
    apply stable_mulLeft_of_generator hνgen M₁
    intro φ hφ
    have hB := blockSL_mulLeft_one_one_mem_normalizer (X := X) ν hνnorm
    have hφU : uSL φ 0 0 ∈ U := hφ
    have hmem := hconj hB hφU
    rw [blockSL_mulLeft_one_one_conj ν hνnorm φ 0 0] at hmem
    have hmem' : uSL (LinearMap.mulLeft k (ν : E) ∘ₗ φ) 0 0 ∈ U := by
      simpa [LinearMap.comp_zero] using hmem
    exact hmem'
  have hM2E : ∀ (s : E) (χ : E →ₗ[k] X), χ ∈ M₂ →
      χ ∘ₗ LinearMap.mulLeft k s ∈ M₂ := by
    apply stable_comp_mulLeft_of_generator (ν := ν⁻¹) (M := M₂)
    · intro L hL
      apply hνgen L
      have h : (ν : E) = (((ν⁻¹ : Eˣ) : E))⁻¹ := by
        rw [Units.val_inv_eq_inv_val, inv_inv]
      rw [h]
      exact L.inv_mem hL
    · intro χ hχ
      have hB := blockSL_one_one_mulLeft_mem_normalizer (X := X) ν hνnorm
      have hmem := hconj hB hχ
      rw [blockSL_one_one_mulLeft_conj ν hνnorm 0 χ 0] at hmem
      exact hmem
  have hphi : ∀ {u : SpecialLinearGroup k (DSpace E X)}, u ∈ U →
      ∀ (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E), u = uSL φ χ ψ → φ ∈ M₁ := by
    intro u hu φ χ ψ hu_eq
    have hB := blockSL_mulLeft_one_one_mem_normalizer (X := X) ν hνnorm
    have hTu := hconj hB hu
    have hw : (blockSL (mulLeftEquiv k ν) 1 1
        (by rw [det_mulLeftEquiv_eq_one ν hνnorm]; simp) * u *
        (blockSL (mulLeftEquiv k ν) 1 1
          (by rw [det_mulLeftEquiv_eq_one ν hνnorm]; simp))⁻¹) * u⁻¹ ∈ U :=
      U.mul_mem hTu (U.inv_mem hu)
    obtain ⟨ψ', hψ'⟩ := commutator_mulLeft ν hνnorm φ χ ψ
    rw [hu_eq, hψ'] at hw
    have hz : uSL 0 0 ψ' ∈ U := hQ0 (mem_datumQ0_std_iff.mpr ⟨ψ', rfl⟩)
    have hmem : LinearMap.mulLeft k ((ν : E) + 1) ∘ₗ φ ∈ M₁ := by
      have h := U.mul_mem hw hz
      rw [uSL_mul] at h
      have h' : uSL (LinearMap.mulLeft k ((ν : E) + 1) ∘ₗ φ) 0 0 ∈ U := by
        simpa [add_self_eq_zero_mod k] using h
      exact h'
    have hν1 : (ν : E) + 1 ≠ 0 := by
      intro h
      apply hνne
      have h1 : (ν : E) = 1 := by
        have h' : (ν : E) = -(1 : E) := by
          rw [← add_eq_zero_iff_eq_neg]
          exact h
        rwa [neg_eq_self_mod k (1 : E)] at h'
      exact Units.ext h1
    have hcancel : LinearMap.mulLeft k ((ν : E) + 1)⁻¹ ∘ₗ
        (LinearMap.mulLeft k ((ν : E) + 1) ∘ₗ φ) = φ := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hν1, one_mul]
    have hstep := hM1E ((ν : E) + 1)⁻¹ (LinearMap.mulLeft k ((ν : E) + 1) ∘ₗ φ) hmem
    rwa [hcancel] at hstep
  have hchi : ∀ {u : SpecialLinearGroup k (DSpace E X)}, u ∈ U →
      ∀ (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E), u = uSL φ χ ψ → χ ∈ M₂ := by
    intro u hu φ χ ψ hu_eq
    have hB := blockSL_one_one_mulLeft_mem_normalizer (X := X) ν hνnorm
    have hTu := hconj hB hu
    have hw : (blockSL 1 1 (mulLeftEquiv k ν)
        (by rw [det_mulLeftEquiv_eq_one ν hνnorm]; simp) * u *
        (blockSL 1 1 (mulLeftEquiv k ν)
          (by rw [det_mulLeftEquiv_eq_one ν hνnorm]; simp))⁻¹) * u⁻¹ ∈ U :=
      U.mul_mem hTu (U.inv_mem hu)
    obtain ⟨ψ', hψ'⟩ := commutator_one_one_mulLeft ν hνnorm φ χ ψ
    rw [hu_eq, hψ'] at hw
    have hz : uSL 0 0 ψ' ∈ U := hQ0 (mem_datumQ0_std_iff.mpr ⟨ψ', rfl⟩)
    have hmem : χ ∘ₗ LinearMap.mulLeft k (((ν⁻¹ : Eˣ) : E) + 1) ∈ M₂ := by
      have h := U.mul_mem hw hz
      rw [uSL_mul] at h
      have h' : uSL 0 (χ ∘ₗ LinearMap.mulLeft k (((ν⁻¹ : Eˣ) : E) + 1)) 0 ∈ U := by
        simpa [add_self_eq_zero_mod k] using h
      exact h'
    have hν1 : ((ν⁻¹ : Eˣ) : E) + 1 ≠ 0 := by
      intro h
      apply hνne
      have h1 : ((ν⁻¹ : Eˣ) : E) = 1 := by
        have h' : ((ν⁻¹ : Eˣ) : E) = -(1 : E) := by
          rw [← add_eq_zero_iff_eq_neg]
          exact h
        rwa [neg_eq_self_mod k (1 : E)] at h'
      have h2 : (ν⁻¹ : Eˣ) = 1 := Units.ext h1
      have h3 : (ν⁻¹ : Eˣ)⁻¹ = (1 : Eˣ)⁻¹ := congrArg Inv.inv h2
      simpa using h3
    have hcancel : (χ ∘ₗ LinearMap.mulLeft k (((ν⁻¹ : Eˣ) : E) + 1)) ∘ₗ
        LinearMap.mulLeft k (((ν⁻¹ : Eˣ) : E) + 1)⁻¹ = χ := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hν1, one_mul]
    have hstep := hM2E (((ν⁻¹ : Eˣ) : E) + 1)⁻¹
      (χ ∘ₗ LinearMap.mulLeft k (((ν⁻¹ : Eˣ) : E) + 1)) hmem
    rwa [hcancel] at hstep
  have hM1 : M₁ = ⊥ ∨ M₁ = ⊤ := eq_bot_or_eq_top_of_stable_hom_to M₁ hM1E
    (fun g φ hφ => by
      have hB := blockSL_one_g_one_mem_normalizer (E := E) (X := X) (g⁻¹)
      have hφU : uSL φ 0 0 ∈ U := hφ
      have hmem := hconj hB hφU
      rw [blockSL_one_g_one_conj (g⁻¹) φ 0 0] at hmem
      have hsymm : (((g⁻¹ : SpecialLinearGroup k X) : X ≃ₗ[k] X).symm : X →ₗ[k] X) =
          (g : X ≃ₗ[k] X).toLinearMap := by
        rw [SpecialLinearGroup.coe_inv]
        rfl
      rw [hsymm] at hmem
      have hmem' : uSL (φ ∘ₗ (g : X ≃ₗ[k] X).toLinearMap) 0 0 ∈ U := by
        simpa [LinearMap.comp_zero] using hmem
      show uSL (φ ∘ₗ (g : X ≃ₗ[k] X).toLinearMap) 0 0 ∈ U
      exact hmem')
  have hM2 : M₂ = ⊥ ∨ M₂ = ⊤ := eq_bot_or_eq_top_of_stable_hom_from M₂ hM2E
    (fun g χ hχ => by
      have hB := blockSL_one_g_one_mem_normalizer (E := E) (X := X) g
      have hχU : uSL 0 χ 0 ∈ U := hχ
      have hmem := hconj hB hχU
      rw [blockSL_one_g_one_conj g 0 χ 0] at hmem
      have hmem' : uSL 0 ((g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ) 0 ∈ U := by
        simpa [LinearMap.zero_comp, LinearMap.comp_zero] using hmem
      show uSL 0 ((g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ) 0 ∈ U
      exact hmem')
  rcases hM1 with hM1bot | hM1top
  · rcases hM2 with hM2bot | hM2top
    ·
      exfalso
      apply hnc
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨φ, χ, ψ, hu_eq⟩ := exists_uSL_of_mem_QK (hUQ hu)
      have hφ0 : φ = 0 := by
        have : φ ∈ M₁ := hphi hu φ χ ψ hu_eq
        simpa [hM1bot] using this
      have hχ0 : χ = 0 := by
        have : χ ∈ M₂ := hchi hu φ χ ψ hu_eq
        simpa [hM2bot] using this
      obtain ⟨φ', χ', ψ', hq_eq⟩ := exists_uSL_of_mem_QK hq
      rw [hu_eq, hφ0, hχ0, hq_eq, uSL_mul, uSL_mul]
      simp only [add_zero, zero_add, LinearMap.comp_zero, LinearMap.zero_comp]
      rw [add_comm ψ ψ']
    ·
      right
      apply le_antisymm
      · intro u hu
        obtain ⟨φ, χ, ψ, hu_eq⟩ := exists_uSL_of_mem_QK (hUQ hu)
        have hφ0 : φ = 0 := by
          have : φ ∈ M₁ := hphi hu φ χ ψ hu_eq
          simpa [hM1bot] using this
        rw [hu_eq, hφ0]
        exact mem_datumU2_std_iff.mpr ⟨χ, ψ, rfl⟩
      · intro g hg
        obtain ⟨χ, ψ, hg_eq⟩ := mem_datumU2_std_iff.mp hg
        have hχ : uSL 0 χ 0 ∈ U := by
          have : χ ∈ M₂ := by rw [hM2top]; trivial
          exact this
        have hψ : uSL 0 0 ψ ∈ U := hQ0 (mem_datumQ0_std_iff.mpr ⟨ψ, rfl⟩)
        rw [hg_eq, ← uSL_mul_chi_psi]
        exact U.mul_mem hχ hψ
  · rcases hM2 with hM2bot | hM2top
    ·
      left
      apply le_antisymm
      · intro u hu
        obtain ⟨φ, χ, ψ, hu_eq⟩ := exists_uSL_of_mem_QK (hUQ hu)
        have hχ0 : χ = 0 := by
          have : χ ∈ M₂ := hchi hu φ χ ψ hu_eq
          simpa [hM2bot] using this
        rw [hu_eq, hχ0]
        exact mem_datumU1_std_iff.mpr ⟨φ, ψ, rfl⟩
      · intro g hg
        obtain ⟨φ, ψ, hg_eq⟩ := mem_datumU1_std_iff.mp hg
        have hφ : uSL φ 0 0 ∈ U := by
          have : φ ∈ M₁ := by rw [hM1top]; trivial
          exact this
        have hψ : uSL 0 0 ψ ∈ U := hQ0 (mem_datumQ0_std_iff.mpr ⟨ψ, rfl⟩)
        rw [hg_eq, ← uSL_mul_phi_psi]
        exact U.mul_mem hφ hψ
    ·
      exfalso
      apply hne
      apply le_antisymm hUQ
      intro q hq
      obtain ⟨φ, χ, ψ, hq_eq⟩ := exists_uSL_of_mem_QK hq
      have hφ : uSL φ 0 0 ∈ U := by
        have : φ ∈ M₁ := by rw [hM1top]; trivial
        exact this
      have hχ : uSL 0 χ 0 ∈ U := by
        have : χ ∈ M₂ := by rw [hM2top]; trivial
        exact this
      have hψ : uSL 0 0 (ψ + φ ∘ₗ χ) ∈ U :=
        hQ0 (mem_datumQ0_std_iff.mpr ⟨ψ + φ ∘ₗ χ, rfl⟩)
      rw [hq_eq, ← uSL_factor]
      exact U.mul_mem (U.mul_mem hφ hχ) hψ

end CFSG.LinearAlgebra.RootGroupSL
