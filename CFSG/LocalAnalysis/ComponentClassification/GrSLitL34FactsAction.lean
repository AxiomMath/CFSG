
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem conj_mem_of_mem_normalizer {J : Subgroup G} {x : G} (hx : x ∈ normalizer (J : Set G))
    {j : G} (hj : j ∈ J) : x⁻¹ * j * x ∈ J := by
  have h := (mem_normalizer_iff.mp (inv_mem hx) j).mp hj
  rwa [inv_inv] at h

@[expose] def conjJ (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) : ↥J ≃* ↥J where
  toFun j := ⟨x⁻¹ * j * x, conj_mem_of_mem_normalizer hx j.2⟩
  invFun j := ⟨x * j * x⁻¹, (mem_normalizer_iff.mp hx j).mp j.2⟩
  left_inv j := Subtype.ext (by simp [mul_assoc])
  right_inv j := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjJ (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) (j : ↥J) :
    ((conjJ J hx j : ↥J) : G) = x⁻¹ * j * x := rfl

theorem map_conjJ_pPrimeCore (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) :
    (pPrimeCore 2 ↥J).map (conjJ J hx).toMonoidHom = pPrimeCore 2 ↥J := by
  have hc : (pPrimeCore 2 ↥J).Characteristic := pPrimeCore_characteristic
  have h := hc.fixed (conjJ J hx).symm
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : (conjJ J hx).symm ((conjJ J hx) z) ∈ pPrimeCore 2 ↥J := by
      rw [MulEquiv.symm_apply_apply]; exact hz
    rw [← h]
    exact hz'
  · intro y hy
    refine ⟨(conjJ J hx).symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [← h] at hy
    exact hy

@[expose] noncomputable def betaHat (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) :
    Jhat J ≃* Jhat J :=
  QuotientGroup.congr (pPrimeCore 2 ↥J) (pPrimeCore 2 ↥J) (conjJ J hx)
    (map_conjJ_pPrimeCore J hx)

theorem betaHat_jq (J : Subgroup G) {x : G} (hx : x ∈ normalizer (J : Set G)) (j : ↥J) :
    betaHat J hx (jq J j) = jq J (conjJ J hx j) := rfl

theorem exists_realization {E : Type*} [Group E]
    (q : E →* Equiv.Perm (Fin 42)) (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (β : E ≃* E) (hβ : ∀ e, β e ∈ q.ker ↔ e ∈ q.ker) :
    ∃ r ∈ R, ∀ e, q (β e) = r * q e * r⁻¹ := by
  choose f hf using fun s : S => hqsurj s s.2
  have hwd : ∀ e e', q e = q e' → q (β e) = q (β e') := by
    intro e e' h
    have hk : e⁻¹ * e' ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hk' := (hβ _).2 hk
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at hk'
    exact hk'
  let θf : S → S := fun s => ⟨q (β (f s)), hqS _⟩
  have hθ : ∀ e, ((θf ⟨q e, hqS e⟩ : S) : Equiv.Perm (Fin 42)) = q (β e) := fun e =>
    hwd _ _ (hf ⟨q e, hqS e⟩)
  have hθmul : ∀ a b : S, θf (a * b) = θf a * θf b := by
    intro a b
    apply Subtype.ext
    show q (β (f (a * b))) = q (β (f a)) * q (β (f b))
    rw [← map_mul, ← map_mul]
    apply hwd
    rw [map_mul, hf, hf, hf]
    rfl
  have hθinj : Function.Injective θf := by
    intro a b hab
    have h1 : q (β (f a)) = q (β (f b)) := congrArg Subtype.val hab
    have hk : β ((f a)⁻¹ * f b) ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h1, inv_mul_cancel]
    have hk' := (hβ _).1 hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, hf, hf] at hk'
    exact Subtype.ext hk'
  have : Finite S := inferInstance
  have hθbij : Function.Bijective θf := ⟨hθinj, Finite.injective_iff_surjective.mp hθinj⟩
  let θ : S ≃* S := MulEquiv.ofBijective (MonoidHom.mk' θf hθmul) hθbij
  obtain ⟨eR, heR, -⟩ := full_automorphism_action
  refine ⟨(eR.symm θ : R), (eR.symm θ).2, fun e => ?_⟩
  have h := heR (eR.symm θ) ⟨q e, hqS e⟩
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : ((θ ⟨q e, hqS e⟩ : S) : Equiv.Perm (Fin 42)) = q (β e) := hθ e
  rw [← h2, h]
  simp

end CFSG.ComponentClassification.GrSLit.L34Facts
