module

public import CFSG.LargeExtraspecial.GLRSplitConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

namespace Levi

variable (Λ : Levi C)

@[expose] def Normalizes (σ : G) : Prop := ∀ l ∈ Λ.L, σ * l * σ⁻¹ ∈ Λ.L

variable {Λ}

theorem Normalizes.mem_normalizer {σ : G} (h : Λ.Normalizes σ) :
    σ ∈ normalizer (Λ.L : Set G) :=
  mem_normalizer_of_forall_conj_mem h

theorem Normalizes.inv_conj_mem {σ : G} (h : Λ.Normalizes σ) {l : G} (hl : l ∈ Λ.L) :
    σ⁻¹ * l * σ ∈ Λ.L := by
  have := (normalizer (Λ.L : Set G)).inv_mem h.mem_normalizer
  have := (mem_normalizer_iff.mp this l).mp hl
  rwa [inv_inv] at this

theorem Normalizes.mul {σ τ : G} (hσ : Λ.Normalizes σ) (hτ : Λ.Normalizes τ) :
    Λ.Normalizes (σ * τ) := fun l hl => by
  have := hσ _ (hτ l hl)
  rwa [show σ * (τ * l * τ⁻¹) * σ⁻¹ = σ * τ * l * (σ * τ)⁻¹ by group] at this

theorem normalizes_of_mem {l : G} (hl : l ∈ Λ.L) : Λ.Normalizes l := fun _ hl' =>
  Λ.L.mul_mem (Λ.L.mul_mem hl hl') (Λ.L.inv_mem hl)

variable (Λ)

theorem eq_one_or_z_of_commute {q : G} (hq : q ∈ S.QG) (h : ∀ l ∈ Λ.L, q * l = l * q) :
    q = 1 ∨ q = S.z := by
  refine (S.cl_eq_zero_iff hq).mp (C.eq_zero_of_forall_Xbar fun x hx => ?_)
  obtain ⟨l, hl⟩ := Λ.toXbar_bijective.2 ⟨x, hx⟩
  have hx' : x = S.ρ ⟨l, Λ.L_le_M l.2⟩ := by rw [← toXbar_coe, hl]
  rw [hx', ← Config.cl_conj (Λ.L_le_M l.2) hq]
  congr 1
  rw [← h l l.2, mul_inv_cancel_right]

theorem exists_eq_of_normalizes {x : G} (hx : x ∈ C.X) (hxL : Λ.Normalizes x) :
    ∃ l ∈ Λ.L, x = l ∨ x = S.z * l := by
  obtain ⟨q, hq, l, hl, rfl⟩ := Λ.exists_mul_eq x hx
  refine ⟨l, hl, ?_⟩
  have hqL : ∀ l' ∈ Λ.L, q * l' = l' * q := by
    intro l' hl'
    have h1 : q * l' * q⁻¹ ∈ Λ.L := by
      have := hxL _ (Λ.normalizes_of_mem (Λ.L.inv_mem hl) l' hl')
      have e : q * l * (l⁻¹ * l' * l⁻¹⁻¹) * (q * l)⁻¹ = q * l' * q⁻¹ := by group
      rwa [e] at this
    have h2 : q * l' * q⁻¹ * l'⁻¹ ∈ S.QG := by
      have := S.QG.mul_mem hq (S.conj_mem_QG (Λ.L_le_M hl') (S.QG.inv_mem hq))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Λ.eq_one_of_mem_QG _ (Λ.L.mul_mem h1 (Λ.L.inv_mem hl')) h2
    calc q * l' = q * l' * q⁻¹ * l'⁻¹ * (l' * q) := by group
      _ = l' * q := by rw [h3, one_mul]
  rcases Λ.eq_one_or_z_of_commute hq hqL with rfl | rfl
  · exact Or.inl (one_mul l)
  · exact Or.inr rfl

theorem exists_normalizes_mul {y : G} (hyM : y ∈ S.M) : ∃ q ∈ S.QG, Λ.Normalizes (q * y) := by
  let L₁ : Subgroup G := Λ.L.comap (MulAut.conj y⁻¹).toMonoidHom
  have hmem : ∀ g, g ∈ L₁ ↔ y⁻¹ * g * y ∈ Λ.L := fun g => by simp [L₁]
  have hconj : ∀ g, y * (y⁻¹ * g * y) * y⁻¹ = g := fun g => by group
  have hL₁X : L₁ ≤ C.X := fun g hg => by
    have := C.conj_mem_X hyM (Λ.L_le_X ((hmem g).mp hg))
    rwa [hconj] at this
  have hL₁Q : ∀ l ∈ L₁, l ∈ S.QG → l = 1 := fun g hg hgQ => by
    have h1 := Λ.eq_one_of_mem_QG _ ((hmem g).mp hg)
      (by simpa using S.conj_mem_QG (S.M.inv_mem hyM) hgQ)
    rw [← hconj g, h1, mul_one, mul_inv_cancel]
  have hL₁ : ∀ x ∈ C.X, ∃ q ∈ S.QG, ∃ l ∈ L₁, q * l = x := by
    intro x hx
    have hx' : y⁻¹ * x * y ∈ C.X := by
      simpa using C.conj_mem_X (S.M.inv_mem hyM) hx
    obtain ⟨q, hq, l, hl, hql⟩ := Λ.exists_mul_eq _ hx'
    refine ⟨y * q * y⁻¹, S.conj_mem_QG hyM hq, y * l * y⁻¹, (hmem _).mpr ?_, ?_⟩
    · simpa [mul_assoc] using hl
    · calc y * q * y⁻¹ * (y * l * y⁻¹) = y * (q * l) * y⁻¹ := by group
        _ = x := by rw [hql]; group
  obtain ⟨q, hq, hqL⟩ := Λ.exists_conj_mem hL₁X hL₁Q hL₁
  refine ⟨q, hq, fun l hl => ?_⟩
  have h1 : y * l * y⁻¹ ∈ L₁ := (hmem _).mpr (by simpa [mul_assoc] using hl)
  have := hqL _ h1
  rwa [show q * (y * l * y⁻¹) * q⁻¹ = q * y * l * (q * y)⁻¹ by group] at this

theorem exists_sigma : ∃ σ ∈ S.M, σ ∉ C.X ∧ Λ.Normalizes σ := by
  obtain ⟨σ₀, hσ₀M, hσ₀X⟩ := C.exists_not_mem_X
  obtain ⟨q, hq, hqL⟩ := Λ.exists_normalizes_mul hσ₀M
  refine ⟨q * σ₀, S.M.mul_mem (S.QG_le_M hq) hσ₀M, fun h => hσ₀X ?_, hqL⟩
  have := C.X.mul_mem (C.X.inv_mem (C.QG_le_X hq)) h
  rwa [inv_mul_cancel_left] at this

theorem Normalizes.inv {σ : G} (h : Λ.Normalizes σ) : Λ.Normalizes σ⁻¹ := fun l hl => by
  rw [inv_inv]
  exact h.inv_conj_mem hl

end Levi

end CFSG.LargeExtraspecial.GLR
