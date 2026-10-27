module

public import CFSG.GF2Type.Smith1979W3.CaseD.PermTables
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix Matrix Equiv Equiv.Perm

@[expose] def commImage (σ : Perm (Fin 8)) : Finset (ι6 → ZMod 2) :=
  Finset.univ.image fun v => v + Mm σ *ᵥ v

theorem Q6_Mm (g : Perm (Fin 8)) (v : ι6 → ZMod 2) : Q6 (Mm g *ᵥ v) = Q6 v := by
  simpa [psi_val] using mem_O6.mp (psi_mem_O6 g) v

theorem Mm_conj (g σ : Perm (Fin 8)) (v : ι6 → ZMod 2) :
    Mm (g * σ * g⁻¹) *ᵥ v = Mm g *ᵥ (Mm σ *ᵥ (Mm g⁻¹ *ᵥ v)) := by
  calc Mm (g * σ * g⁻¹) *ᵥ v
      = (Mm (g * σ) * Mm g⁻¹) *ᵥ v := by rw [Mm_mul]
    _ = ((Mm g * Mm σ) * Mm g⁻¹) *ᵥ v := by rw [Mm_mul]
    _ = (Mm g * Mm σ) *ᵥ (Mm g⁻¹ *ᵥ v) := by rw [← Matrix.mulVec_mulVec]
    _ = Mm g *ᵥ (Mm σ *ᵥ (Mm g⁻¹ *ᵥ v)) := by rw [← Matrix.mulVec_mulVec]

theorem Mm_mulVec_inv (g : Perm (Fin 8)) (v : ι6 → ZMod 2) :
    Mm g⁻¹ *ᵥ (Mm g *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Mm_mul, inv_mul_cancel, Mm_one, Matrix.one_mulVec]

theorem Mm_mulVec_inv' (g : Perm (Fin 8)) (v : ι6 → ZMod 2) :
    Mm g *ᵥ (Mm g⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Mm_mul, mul_inv_cancel, Mm_one, Matrix.one_mulVec]

theorem Mm_mulVec_add_commImage (g σ : Perm (Fin 8)) (v : ι6 → ZMod 2) :
    Mm g *ᵥ (v + Mm σ *ᵥ v) = Mm g *ᵥ v + Mm (g * σ * g⁻¹) *ᵥ (Mm g *ᵥ v) := by
  rw [Matrix.mulVec_add, Mm_conj, Mm_mulVec_inv]

theorem commImage_conj_eq (g σ : Perm (Fin 8)) :
    commImage (g * σ * g⁻¹) = (commImage σ).image (fun x => Mm g *ᵥ x) := by
  ext u
  simp only [commImage, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Mm g⁻¹ *ᵥ v + Mm σ *ᵥ (Mm g⁻¹ *ᵥ v), ⟨Mm g⁻¹ *ᵥ v, rfl⟩, ?_⟩
    rw [Mm_mulVec_add_commImage, Mm_mulVec_inv', hv]
  · rintro ⟨a, ⟨b, hb⟩, ha⟩
    refine ⟨Mm g *ᵥ b, ?_⟩
    rw [← Mm_mulVec_add_commImage, hb, ha]

theorem card_commImage_conj (g σ : Perm (Fin 8)) :
    (commImage (g * σ * g⁻¹)).card = (commImage σ).card := by
  rw [commImage_conj_eq]
  refine Finset.card_image_of_injective _ ?_
  intro a b h
  have h' := congrArg (fun x => Mm g⁻¹ *ᵥ x) h
  simpa only [Mm_mulVec_inv] using h'

theorem exists_Q6_commImage_conj (g σ : Perm (Fin 8)) :
    (∃ x ∈ commImage (g * σ * g⁻¹), Q6 x ≠ 0) ↔ ∃ x ∈ commImage σ, Q6 x ≠ 0 := by
  rw [commImage_conj_eq]
  constructor
  · rintro ⟨x, hx, hQ⟩
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, fun h => hQ (by rw [Q6_Mm, h])⟩
  · rintro ⟨y, hy, hQ⟩
    exact ⟨Mm g *ᵥ y, Finset.mem_image.2 ⟨y, hy, rfl⟩, fun h => hQ (by rw [Q6_Mm] at h; exact h)⟩

theorem cycleType_s1 : (swap (0 : Fin 8) 1).cycleType = Multiset.replicate 1 2 := by
  rw [Multiset.replicate_one]
  exact isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))

theorem cycleType_s2 : (swap (0 : Fin 8) 1 * swap 2 3).cycleType = Multiset.replicate 2 2 := by
  have h := cycleType_swap_mul_swap_of_nodup (α := Fin 8) (x := 0) (y := 1) (z := 2) (t := 3)
    (by decide)
  simpa using h

theorem cycleType_s3 :
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5).cycleType = Multiset.replicate 3 2 := by
  have hd : Disjoint (swap (0 : Fin 8) 1 * swap 2 3) (swap 4 5) :=
    Disjoint.mul_left
      (disjoint_swap_swap (α := Fin 8) (x := 0) (y := 1) (z := 4) (t := 5) (by decide))
      (disjoint_swap_swap (α := Fin 8) (x := 2) (y := 3) (z := 4) (t := 5) (by decide))
  rw [Disjoint.cycleType_mul hd, cycleType_s2,
    isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (4 : Fin 8) ≠ 5))]
  rw [← Multiset.replicate_one, ← Multiset.replicate_add]

theorem cycleType_s4 :
    (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7).cycleType =
      Multiset.replicate 4 2 := by
  have hd : Disjoint (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5) (swap 6 7) :=
    Disjoint.mul_left
      (Disjoint.mul_left
        (disjoint_swap_swap (α := Fin 8) (x := 0) (y := 1) (z := 6) (t := 7) (by decide))
        (disjoint_swap_swap (α := Fin 8) (x := 2) (y := 3) (z := 6) (t := 7) (by decide)))
      (disjoint_swap_swap (α := Fin 8) (x := 4) (y := 5) (z := 6) (t := 7) (by decide))
  rw [Disjoint.cycleType_mul hd, cycleType_s3,
    isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (6 : Fin 8) ≠ 7))]
  rw [← Multiset.replicate_one, ← Multiset.replicate_add]

theorem card_commImage_s1 : (commImage (swap (0 : Fin 8) 1)).card ≠ 4 := by
  decide +kernel

theorem card_commImage_s3 :
    (commImage (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5)).card ≠ 4 := by
  decide +kernel

theorem Q6_commImage_s4 :
    ∀ x ∈ commImage (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7), Q6 x = 0 := by
  decide +kernel

theorem isDT_of_commImage {σ : Perm (Fin 8)} (h1 : σ * σ = 1) (h2 : σ ≠ 1)
    (hc : (commImage σ).card = 4) (hq : ∃ x ∈ commImage σ, Q6 x ≠ 0) : IsDT σ := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two]; exact h1
  set k : ℕ := σ.cycleType.card with hk
  have hct' : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    cycleType_of_pow_prime_eq_one hpow
  have hct : σ.cycleType = Multiset.replicate k 2 := by rw [hk]; exact hct'
  have hk1 : 1 ≤ k := by
    have hpos : 0 < σ.cycleType.card := card_cycleType_pos.2 h2
    rw [hk]; omega
  have hk4 : k ≤ 4 := by
    have hsum := sum_cycleType σ
    rw [hct', Multiset.sum_replicate, nsmul_eq_mul] at hsum
    have hle : σ.support.card ≤ 8 := by simpa using Finset.card_le_univ σ.support
    have h2' : σ.cycleType.card * 2 ≤ 8 := hsum.le.trans hle
    rw [hk]; omega
  interval_cases k
  · obtain ⟨g, hg⟩ := isConj_iff.1
      (isConj_iff_cycleType_eq.2 (cycleType_s1.trans hct.symm) :
        IsConj (swap (0 : Fin 8) 1) σ)
    rw [← hg] at hc
    rw [card_commImage_conj g (swap (0 : Fin 8) 1)] at hc
    exact absurd hc card_commImage_s1
  · obtain ⟨g, hg⟩ := isConj_iff.1
      (isConj_iff_cycleType_eq.2 (cycleType_s2.trans hct.symm) :
        IsConj (swap (0 : Fin 8) 1 * swap 2 3) σ)
    have hdt : IsDT (g * (swap (0 : Fin 8) 1 * swap 2 3) * g⁻¹) :=
      IsDT.conj ⟨0, 1, 2, 3, by decide, rfl⟩ g
    rw [hg] at hdt
    exact hdt
  · obtain ⟨g, hg⟩ := isConj_iff.1
      (isConj_iff_cycleType_eq.2 (cycleType_s3.trans hct.symm) :
        IsConj (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5) σ)
    rw [← hg] at hc
    rw [card_commImage_conj g (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5)] at hc
    exact absurd hc card_commImage_s3
  · obtain ⟨g, hg⟩ := isConj_iff.1
      (isConj_iff_cycleType_eq.2 (cycleType_s4.trans hct.symm) :
        IsConj (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7) σ)
    rw [← hg] at hq
    rw [exists_Q6_commImage_conj g
      (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5 * swap 6 7)] at hq
    obtain ⟨x, hx, hQ⟩ := hq
    exact absurd (Q6_commImage_s4 x hx) hQ

end CFSG.GF2Type.Smith1979W3.CaseD
