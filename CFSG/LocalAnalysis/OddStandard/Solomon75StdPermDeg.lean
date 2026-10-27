module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermBound

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS

section Doubling

variable {N : Type*}

@[expose] def dblRoot (ζ : Perm N) (hζ : ζ * ζ = 1) : Perm (N × Fin 2) where
  toFun p := if p.2 = 0 then (p.1, 1) else (ζ p.1, 0)
  invFun p := if p.2 = 1 then (p.1, 0) else (ζ p.1, 1)
  left_inv := by
    rintro ⟨x, i⟩
    fin_cases i
    · simp
    · have : ζ (ζ x) = x := by simpa using congrArg (fun e : Perm N => e x) hζ
      simp [this]
  right_inv := by
    rintro ⟨x, i⟩
    fin_cases i
    · have : ζ (ζ x) = x := by simpa using congrArg (fun e : Perm N => e x) hζ
      simp [this]
    · simp

@[expose] def dblSq (ζ : Perm N) : Perm (N × Fin 2) := Equiv.prodCongr ζ (Equiv.refl (Fin 2))

theorem dblRoot_sq (ζ : Perm N) (hζ : ζ * ζ = 1) : dblRoot ζ hζ ^ 2 = dblSq ζ := by
  refine Equiv.ext fun p => ?_
  obtain ⟨x, i⟩ := p
  fin_cases i <;> simp [pow_two, Perm.mul_apply, dblRoot, dblSq]

theorem dblRoot_pow_four (ζ : Perm N) (hζ : ζ * ζ = 1) : dblRoot ζ hζ ^ 4 = 1 := by
  have h4 : dblRoot ζ hζ ^ 4 = (dblRoot ζ hζ ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, dblRoot_sq, pow_two]
  refine Equiv.ext fun p => ?_
  obtain ⟨x, i⟩ := p
  have : ζ (ζ x) = x := by simpa using congrArg (fun e : Perm N => e x) hζ
  simp [Perm.mul_apply, dblSq, this]

@[expose] def dblHom {D : Type*} [Group D] (ι : D →* Perm N) : D →* Perm (N × Fin 2) where
  toFun d := dblSq (ι d)
  map_one' := by
    refine Equiv.ext fun p => ?_
    obtain ⟨x, i⟩ := p
    simp [dblSq]
  map_mul' d d' := by
    refine Equiv.ext fun p => ?_
    obtain ⟨x, i⟩ := p
    simp [dblSq, Perm.mul_apply]

theorem dblHom_comm {D : Type*} [Group D] (ι : D →* Perm N) (ζ : Perm N) (hζ : ζ * ζ = 1)
    (hc : ∀ d, ι d * ζ = ζ * ι d) (d : D) :
    dblHom ι d * dblRoot ζ hζ = dblRoot ζ hζ * dblHom ι d := by
  refine Equiv.ext fun p => ?_
  obtain ⟨x, i⟩ := p
  have := congrArg (fun e : Perm N => e x) (hc d)
  simp only [Perm.mul_apply] at this
  fin_cases i
  · simp [dblHom, dblSq, dblRoot, Perm.mul_apply]
  · simp [dblHom, dblSq, dblRoot, Perm.mul_apply, this]

theorem card_support_dblSq [Fintype N] [DecidableEq N] (ζ : Perm N) :
    (dblSq ζ).support.card = 2 * ζ.support.card := by
  have : (dblSq ζ).support = ζ.support ×ˢ Finset.univ := by
    ext ⟨x, i⟩
    simp [Perm.mem_support, dblSq]
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]

end Doubling

theorem two_mul_le_card_support_of_doubleCover {f : ℕ} (hf : 5 ≤ f) {D : Type} [Group D]
    (hD : IsDoubleCoverOfAlt D f) {N : Type*} [Fintype N] [DecidableEq N] (ι : D →* Perm N)
    {z : D} (hz : z ∈ center D) (hιz : ι z ≠ 1) : 2 * f ≤ (ι z).support.card := by
  have hz2 : z * z = 1 := by
    have h1 : (⟨z, hz⟩ : center D) ^ Nat.card (center D) = 1 := pow_card_eq_one'
    rw [hD.2.1, pow_two] at h1
    simpa using congrArg Subtype.val h1
  have hζ : ι z * ι z = 1 := by rw [← map_mul, hz2, map_one]
  have hc : ∀ d, ι d * ι z = ι z * ι d := fun d => by
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz d]
  have h := four_mul_le_card_support_sq_of_doubleCover hf hD (dblRoot_pow_four (ι z) hζ)
    (dblHom ι) (dblHom_comm ι (ι z) hζ hc) (z := z) (by rw [dblRoot_sq]; rfl)
    (by
      rw [dblRoot_sq]
      intro h1
      apply hιz
      refine Equiv.ext fun x => ?_
      have := congrArg (fun e : Perm (N × Fin 2) => (e (x, 0)).1) h1
      simpa [dblSq] using this)
  rw [dblRoot_sq, card_support_dblSq] at h
  omega

end CFSG.OddStandard.Solomon75
