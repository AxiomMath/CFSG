module

public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.CGT.T75I

open Matrix CFSG.GH74.Exceptional CFSG.ComponentClassification.PresentationLocal Equiv
  Equiv.Perm
open scoped Matrix

theorem exists_iso_alt8_carm :
    ∃ φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2),
      ∀ k : CarmichaelIndex 8, φ (carmichaelCycle k) = l42Gen k := by
  classical
  obtain ⟨φ, hφx⟩ := exists_hom_carmichaelCycle (n := 8) (by norm_num) l42Gen l42Gen_pow_three
    l42Gen_mul_sq
  have hinj : Function.Injective φ := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      let k₀ : CarmichaelIndex 8 := ⟨2, by decide⟩
      have hk : carmichaelCycle k₀ ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφx] at hk
      have : l42Mat 0 = 1 := by
        have := congrArg Units.val hk
        simpa [l42Gen, l42Unit, carmichaelIndexToFin6, k₀] using this
      exact absurd this (by decide)
  have hcard : Nat.card (alternatingGroup (Fin 8)) = Nat.card (GL (Fin 4) (ZMod 2)) := by
    rw [card_GL_four_two, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact ⟨MulEquiv.ofBijective φ (Function.Injective.bijective_of_nat_card_le hinj hcard.ge), hφx⟩

theorem mulVec_inv_mulVec (A : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (A : GL (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem card_fix_conj_mat (A B : GL (Fin 4) (ZMod 2)) :
    Nat.card {v : Fin 4 → ZMod 2 //
      ((A * B * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} =
      Nat.card {v : Fin 4 → ZMod 2 // (B : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} := by
  have e : ∀ v, ((A * B * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((B : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  refine Nat.card_congr
    { toFun := fun v => ⟨((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1,
        ?_⟩
      invFun := fun v => ⟨(A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v.1, ?_⟩
      left_inv := fun v => Subtype.ext (mulVec_mulVec_inv A v.1)
      right_inv := fun v => Subtype.ext (mulVec_inv_mulVec A v.1) }
  · have h := v.2
    rw [e] at h
    have h' := congrArg (fun w => ((A⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w) h
    simp only [mulVec_inv_mulVec] at h'
    exact h'
  · rw [e, mulVec_inv_mulVec, v.2]

theorem exists_even_conj_type22 {p q a b : Fin 8} (hpq : p ≠ q) (hab : a ≠ b) (hpa : p ≠ a)
    (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    ∃ π : Perm (Fin 8), Perm.sign π = 1 ∧
      π * (swap (0 : Fin 8) 2 * swap 1 3) * π⁻¹ = swap p q * swap a b := by
  classical
  have hct : (swap (0 : Fin 8) 2 * swap 1 3).cycleType = (swap p q * swap a b).cycleType := by
    rw [cycleType_swap_mul_swap_of_nodup (by decide : [(0 : Fin 8), 2, 1, 3].Nodup),
      cycleType_swap_mul_swap_of_nodup (x := p) (y := q) (z := a) (t := b)
        (by simp [hpq, hpa, hpb, hqa, hqb, hab])]
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 hct)
  by_cases hs : Perm.sign c = 1
  · exact ⟨c, hs, hc⟩
  · have hs' : Perm.sign c = -1 := by
      rcases Int.units_eq_one_or (Perm.sign c) with h | h
      · exact absurd h hs
      · exact h
    refine ⟨c * swap 4 5, ?_, ?_⟩
    · rw [map_mul, hs', Perm.sign_swap (by decide)]
      decide
    · have hcomm : swap (4 : Fin 8) 5 * (swap 0 2 * swap 1 3) * (swap (4 : Fin 8) 5)⁻¹ =
          swap 0 2 * swap 1 3 := by decide
      calc c * swap 4 5 * (swap 0 2 * swap 1 3) * (c * swap 4 5)⁻¹
          = c * (swap 4 5 * (swap 0 2 * swap 1 3) * (swap (4 : Fin 8) 5)⁻¹) * c⁻¹ := by group
        _ = c * (swap 0 2 * swap 1 3) * c⁻¹ := by rw [hcomm]
        _ = _ := hc

theorem card_fix_l42Mat :
    Nat.card {v : Fin 4 → ZMod 2 // (l42Mat 0 * l42Mat 1) *ᵥ v = v} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem carmichael_mul_eq :
    ((carmichaelCycle (n := 8) ⟨2, by decide⟩ * carmichaelCycle (n := 8) ⟨3, by decide⟩ :
      alternatingGroup (Fin 8)) : Perm (Fin 8)) = swap (0 : Fin 8) 2 * swap 1 3 := by
  decide +kernel

theorem card_fix_type22 (φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k : CarmichaelIndex 8, φ (carmichaelCycle k) = l42Gen k)
    {p q a b : Fin 8} (hpq : p ≠ q) (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a)
    (hqb : q ≠ b) (σ : alternatingGroup (Fin 8))
    (hσ : (σ : Perm (Fin 8)) = swap p q * swap a b) :
    Nat.card {v : Fin 4 → ZMod 2 //
      ((φ σ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} = 4 := by
  obtain ⟨π, hπ, hconj⟩ := exists_even_conj_type22 hpq hab hpa hpb hqa hqb
  let π' : alternatingGroup (Fin 8) := ⟨π, Equiv.Perm.mem_alternatingGroup.2 hπ⟩
  let σ₀ : alternatingGroup (Fin 8) :=
    carmichaelCycle (n := 8) ⟨2, by decide⟩ * carmichaelCycle (n := 8) ⟨3, by decide⟩
  have hσ₀ : (σ₀ : Perm (Fin 8)) = swap (0 : Fin 8) 2 * swap 1 3 := carmichael_mul_eq
  have hσeq : σ = π' * σ₀ * π'⁻¹ := by
    apply Subtype.ext
    rw [hσ, ← hconj]
    show _ = π * (σ₀ : Perm (Fin 8)) * π⁻¹
    rw [hσ₀]
  have hφσ₀ : φ σ₀ = l42Gen ⟨2, by decide⟩ * l42Gen ⟨3, by decide⟩ := by
    simp only [σ₀, map_mul, hφ]
  rw [hσeq, map_mul, map_mul, map_inv, card_fix_conj_mat, hφσ₀]
  exact card_fix_l42Mat

end CFSG.CGT.T75I
