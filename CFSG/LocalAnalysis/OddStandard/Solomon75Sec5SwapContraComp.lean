module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapCentral
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Contra

variable {X : Type} [Group X] [Finite X]

theorem swap_contra_comp {C P : Subgroup X} {t : X} (ht2 : t * t = 1) (hP : IsPCompIn 2 C P)
    (hP' : IsPCompIn 2 C (P.map (MulAut.conj t).toMonoidHom))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P)
    (hZ : IsPGroup 2 ↥(center ↥((P.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)))))
    (hZ' : IsPGroup 2 ↥(center ↥(((P.map (MulAut.conj t).toMonoidHom).subgroupOf C).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥C)))))
    {OO W₂ : Subgroup X} (hOO : Odd (Nat.card OO))
    (hΛOO : P ⊔ P.map (MulAut.conj t).toMonoidHom ≤ normalizer (OO : Set X))
    (hW₂ : IsPGroup 2 ↥W₂) (hW₂OO : W₂ ≤ normalizer (OO : Set X))
    (hV : ∀ x ∈ P ⊔ P.map (MulAut.conj t).toMonoidHom, ⁅x, t⁆ ∈ OO ⊔ W₂) : False := by
  classical
  set P' : Subgroup X := P.map (MulAut.conj t).toMonoidHom with hP'def
  set Λ : Subgroup X := P ⊔ P' with hΛ
  have hPC : P ≤ C := hP.1
  have hP'C : P' ≤ C := hP'.1
  have hΛC : Λ ≤ C := sup_le hPC hP'C
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set K₁ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (P.subgroupOf C).map π with hK₁
  set K₂ : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := (P'.subgroupOf C).map π with hK₂
  have hK₁c : IsComponent K₁ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hP.2
    show IsComponent ((P.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₂c : IsComponent K₂ := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hP'.2
    show IsComponent ((P'.subgroupOf C).map π)
    rw [hKeq]
    exact hK
  have hK₁₂ : K₁ ≠ K₂ := by
    intro heq
    apply hne
    have h1 := eq_of_map_pPrimeCore_eq hP'.2 hP.2 heq.symm
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hP'C, inf_of_le_left hPC] at h1
    exact h1
  have hcomm₁₂ : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b := fun a ha b hb =>
    commute_of_ne hK₁c hK₂c hK₁₂ ha hb
  have hZ₁ : IsPGroup 2 ↥(center ↥K₁) := hZ
  have hZ₂ : IsPGroup 2 ↥(center ↥K₂) := hZ'
  have hKE₁ : (P.subgroupOf C).map π = K₁ := rfl
  have hKE₂ : (P'.subgroupOf C).map π = K₂ := rfl
  let ψ₀ : ↥Λ →* ↥C ⧸ pPrimeCore 2 ↥C := π.comp (Subgroup.inclusion hΛC)
  have hΛsub : Λ.subgroupOf C = P.subgroupOf C ⊔ P'.subgroupOf C :=
    Subgroup.subgroupOf_sup hPC hP'C
  have hψ₀ : ∀ y : ↥Λ, ψ₀ y ∈ K₁ ⊔ K₂ := by
    intro y
    have h1 : (⟨(y : X), hΛC y.2⟩ : ↥C) ∈ Λ.subgroupOf C := y.2
    rw [hΛsub] at h1
    have h2 := Subgroup.mem_map_of_mem π h1
    rwa [Subgroup.map_sup, hKE₁, hKE₂] at h2
  let ψ : ↥Λ →* ↥(K₁ ⊔ K₂) := ψ₀.codRestrict (K₁ ⊔ K₂) hψ₀
  have hrange : K₁ ⊔ K₂ ≤ ψ₀.range := by
    refine sup_le ?_ ?_
    · rw [← hKE₁]
      rintro _ ⟨ec, hec, rfl⟩
      exact ⟨⟨(ec : X), Subgroup.mem_sup_left (show (ec : X) ∈ P from hec)⟩, rfl⟩
    · rw [← hKE₂]
      rintro _ ⟨ec, hec, rfl⟩
      exact ⟨⟨(ec : X), Subgroup.mem_sup_right (show (ec : X) ∈ P' from hec)⟩, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy⟩ := hrange hq
    exact ⟨y, Subtype.ext hy⟩
  have hQ : ∀ M₀ : Subgroup ↥(K₁ ⊔ K₂), M₀.Normal → Odd (Nat.card M₀) → M₀ = ⊥ := by
    intro M₀ hM₀ hodd
    have hb := odd_normal_eq_bot_sup hK₁c.1 hZ₁ hK₂c.1 hZ₂ hcomm₁₂
      (M := M₀.map (K₁ ⊔ K₂).subtype) (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (by
        rintro q hq _ ⟨m, hm, rfl⟩
        exact ⟨⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹, hM₀.conj_mem m hm ⟨q, hq⟩, rfl⟩)
      (by rwa [Subgroup.card_map_of_injective (K₁ ⊔ K₂).subtype_injective])
    exact (Subgroup.map_eq_bot_iff_of_injective M₀ (K₁ ⊔ K₂).subtype_injective).1 hb
  have hwΛ : ∀ x ∈ Λ, t * x * t⁻¹ ∈ Λ := by
    have hsinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h1 : P ≤ Λ.comap (MulAut.conj t).toMonoidHom := fun x hx =>
      Subgroup.mem_sup_right ⟨x, hx, rfl⟩
    have h2 : P' ≤ Λ.comap (MulAut.conj t).toMonoidHom := by
      rintro _ ⟨e, he, rfl⟩
      show t * (t * e * t⁻¹) * t⁻¹ ∈ Λ
      have : t * (t * e * t⁻¹) * t⁻¹ = e := by
        calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t * t)⁻¹ := by group
          _ = e := by rw [ht2]; simp
      rw [this]
      exact Subgroup.mem_sup_left he
    intro x hx
    exact (sup_le h1 h2 : Λ ≤ Λ.comap (MulAut.conj t).toMonoidHom) hx
  obtain ⟨R, hRn, hRp, hRmem⟩ :=
    commutator_image_normal_two (X := X) ψ hψs hwΛ hOO hΛOO hW₂ hW₂OO hQ hV
  set R' : Subgroup (↥C ⧸ pPrimeCore 2 ↥C) := R.map (K₁ ⊔ K₂).subtype with hR'
  have hRQ : R' ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRn' : ∀ q ∈ K₁ ⊔ K₂, ∀ ρ ∈ R', q * ρ * q⁻¹ ∈ R' := by
    rintro q hq _ ⟨ρ, hρ, rfl⟩
    exact ⟨⟨q, hq⟩ * ρ * ⟨q, hq⟩⁻¹, hRn.conj_mem ρ hρ ⟨q, hq⟩, rfl⟩
  have hRp' : IsPGroup 2 ↥R' :=
    hRp.of_equiv (Subgroup.equivMapOfInjective R (K₁ ⊔ K₂).subtype (K₁ ⊔ K₂).subtype_injective)
  have hmem : ∀ k ∈ K₁, ∃ k' ∈ K₂, k * k'⁻¹ ∈ R' := by
    intro k hk
    rw [← hKE₁] at hk
    obtain ⟨ec, hec, rfl⟩ := hk
    have heE : (ec : X) ∈ P := hec
    have hse : t * (ec : X) * t⁻¹ ∈ P' := ⟨ec, heE, rfl⟩
    have hseC : t * (ec : X) * t⁻¹ ∈ C := hP'C hse
    refine ⟨π ⟨t * (ec : X) * t⁻¹, hseC⟩, ?_, ?_⟩
    · rw [← hKE₂]
      exact ⟨⟨_, hseC⟩, hse, rfl⟩
    · have hxΛ : (ec : X) ∈ Λ := Subgroup.mem_sup_left heE
      have hcΛ : ⁅(ec : X), t⁆ ∈ Λ := by
        have e : ⁅(ec : X), t⁆ = (ec : X) * (t * (ec : X)⁻¹ * t⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Λ.mul_mem hxΛ (hwΛ _ (Λ.inv_mem hxΛ))
      refine ⟨ψ ⟨⁅(ec : X), t⁆, hcΛ⟩, hRmem ⟨(ec : X), hxΛ⟩ hcΛ, ?_⟩
      change ψ₀ ⟨⁅(ec : X), t⁆, hcΛ⟩ = _
      have hC1 : (⟨⁅(ec : X), t⁆, hΛC hcΛ⟩ : ↥C) = ec * (⟨t * (ec : X) * t⁻¹, hseC⟩ : ↥C)⁻¹ := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      change π ⟨⁅(ec : X), t⁆, hΛC hcΛ⟩ = _
      rw [hC1, map_mul, map_inv]
  exact swap_central_contra hK₁c.1 hcomm₁₂ hRQ hRn' hRp' hmem

end Contra

end CFSG.OddStandard.Solomon75
