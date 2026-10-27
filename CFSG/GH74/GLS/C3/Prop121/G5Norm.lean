module

public import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.ABGLocalTools

@[expose] def conjHom {S : Type*} [Group S] (c : Perm (Fin 9)) (ψ : S →* Perm (Fin 9)) :
    S →* Perm (Fin 9) :=
  (MulAut.conj c).toMonoidHom.comp ψ

theorem conjHom_apply {S : Type*} [Group S] (c : Perm (Fin 9)) (ψ : S →* Perm (Fin 9)) (s : S) :
    conjHom c ψ s = c * ψ s * c⁻¹ := rfl

theorem conjHom_injective {S : Type*} [Group S] (c : Perm (Fin 9)) {ψ : S →* Perm (Fin 9)}
    (h : Function.Injective ψ) : Function.Injective (conjHom c ψ) := by
  intro s t hst
  apply h
  have := hst
  simp only [conjHom_apply, mul_left_inj, mul_right_inj] at this
  exact this

theorem numMoved_conjHom {S : Type*} [Group S] (c : Perm (Fin 9)) (ψ : S →* Perm (Fin 9)) (s : S) :
    numMoved (conjHom c ψ s) = numMoved (ψ s) := numMoved_conj _ _

theorem normalize {S : Type*} [Group S]
    (φ : S →* alternatingGroup (Fin 9)) (hinj : Function.Injective φ)
    (hsyl : IsSylowOf 2 φ.range ⊤) (x x' : S) (hne : x ≠ x') (hsq : x * x = 1)
    (hnm : numMoved ((φ x : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 4)
    (hcl : ∀ s : S, (s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x') ∧
      (s * x' * s⁻¹ = x ∨ s * x' * s⁻¹ = x')) :
    ∃ ψ : S →* Perm (Fin 9), Function.Injective ψ ∧
      (∀ s, numMoved (ψ s) = numMoved ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9))) ∧
      (∀ s, ψ s ∈ S0) ∧ (∀ p ∈ S0, ∃ s, ψ s = p) ∧ ψ x = emb 5 f1 := by
  obtain ⟨k, -, hk⟩ := hsyl.exists_mem_conj isSylowOf_S0A
  let ψ₁ : S →* Perm (Fin 9) := conjHom (k : Perm (Fin 9)) ((alternatingGroup (Fin 9)).subtype.comp φ)
  have hψ₁ : ∀ s, ψ₁ s = (k : Perm (Fin 9)) * (φ s : Perm (Fin 9)) * (k : Perm (Fin 9))⁻¹ :=
    fun s => rfl
  have h1inj : Function.Injective ψ₁ := by
    apply conjHom_injective
    intro s t hst
    exact hinj (Subtype.ext hst)
  have h1nm : ∀ s, numMoved (ψ₁ s) = numMoved ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
    fun s => numMoved_conj _ _
  have h1mem : ∀ s, ψ₁ s ∈ S0 := by
    intro s
    have : (k * φ s * k⁻¹ : alternatingGroup (Fin 9)) ∈ S0A := by
      rw [hk]
      have e : k⁻¹ * (k * φ s * k⁻¹) * k = φ s := by group
      rw [e]
      exact ⟨s, rfl⟩
    exact this
  have h1surj : ∀ p ∈ S0, ∃ s, ψ₁ s = p := by
    intro p hp
    have hz : (⟨p, S0_le_alt hp⟩ : alternatingGroup (Fin 9)) ∈ S0A := mem_S0A.2 hp
    rw [hk] at hz
    obtain ⟨s, hs⟩ := hz
    refine ⟨s, ?_⟩
    have : (k : Perm (Fin 9)) * (φ s : Perm (Fin 9)) * (k : Perm (Fin 9))⁻¹ = p := by
      rw [hs]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact this
  have hy : ψ₁ x ∈ S0 := h1mem x
  have hy' : ψ₁ x' ∈ S0 := h1mem x'
  have hyne : ψ₁ x ≠ ψ₁ x' := fun h => hne (h1inj h)
  have hysq : ψ₁ x * ψ₁ x = 1 := by rw [← map_mul, hsq, map_one]
  have hynm : numMoved (ψ₁ x) = 4 := by rw [h1nm]; exact hnm
  have hycl : ∀ s' ∈ S0, (s' * ψ₁ x * s'⁻¹ = ψ₁ x ∨ s' * ψ₁ x * s'⁻¹ = ψ₁ x') ∧
      (s' * ψ₁ x' * s'⁻¹ = ψ₁ x ∨ s' * ψ₁ x' * s'⁻¹ = ψ₁ x') := by
    intro s' hs'
    obtain ⟨s, rfl⟩ := h1surj s' hs'
    have e1 : ψ₁ s * ψ₁ x * (ψ₁ s)⁻¹ = ψ₁ (s * x * s⁻¹) := by simp [map_mul, map_inv]
    have e2 : ψ₁ s * ψ₁ x' * (ψ₁ s)⁻¹ = ψ₁ (s * x' * s⁻¹) := by simp [map_mul, map_inv]
    rw [e1, e2]
    obtain ⟨h1, h2⟩ := hcl s
    refine ⟨?_, ?_⟩
    · rcases h1 with h | h
      · exact Or.inl (congrArg ψ₁ h)
      · exact Or.inr (congrArg ψ₁ h)
    · rcases h2 with h | h
      · exact Or.inl (congrArg ψ₁ h)
      · exact Or.inr (congrArg ψ₁ h)
  rcases class_two hy hy' hyne hysq hynm hycl with h | h
  · exact ⟨ψ₁, h1inj, h1nm, h1mem, h1surj, h⟩
  · refine ⟨conjHom (a0perm 5) ψ₁, conjHom_injective _ h1inj, ?_, ?_, ?_, ?_⟩
    · intro s
      rw [numMoved_conjHom, h1nm]
    · intro s
      rw [conjHom_apply]
      exact mul_mem (mul_mem a0_mem_S0 (h1mem s)) (inv_mem a0_mem_S0)
    · intro p hp
      have hp' : (a0perm 5)⁻¹ * p * a0perm 5 ∈ S0 :=
        mul_mem (mul_mem (inv_mem a0_mem_S0) hp) a0_mem_S0
      obtain ⟨s, hs⟩ := h1surj _ hp'
      refine ⟨s, ?_⟩
      rw [conjHom_apply, hs]
      group
    · rw [conjHom_apply, h, a0_e1]

end CFSG.GH74.GLS.C3.Prop121
