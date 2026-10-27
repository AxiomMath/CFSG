module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix Matrix Finset Equiv

@[expose] def ind (S : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun k => if k ∈ S then 1 else 0

@[expose] def vS (S : Finset (Fin 8)) : ι6 → ZMod 2 := Tm *ᵥ ind S

theorem Tm_ne_zero : ∀ a : Fin 8 → ZMod 2, ∑ k, a k = 0 → a ≠ 0 → a ≠ one8 →
    Tm *ᵥ a ≠ 0 := by decide +kernel

theorem polar_Tm : ∀ a b : Fin 8 → ZMod 2, ∑ k, a k = 0 → ∑ k, b k = 0 →
    polar6 (Tm *ᵥ a) (Tm *ᵥ b) = ∑ k, a k * b k := by decide +kernel

theorem exists_vS_of_singular_decide : ∀ x : ι6 → ZMod 2, x ≠ 0 → Q6 x = 0 →
    ∃ T : Finset (Fin 8), T.card = 4 ∧ x = vS T := by decide +kernel

theorem nondeg6 : ∀ y : ι6 → ZMod 2, y ≠ 0 → ∃ v : ι6 → ZMod 2, polar6 v y = 1 := by
  decide +kernel

theorem sum_ind (S : Finset (Fin 8)) : ∑ k, ind S k = (S.card : ZMod 2) := by
  simp [ind, Finset.sum_boole]

theorem Pm_mulVec_ind (σ : Perm (Fin 8)) (S : Finset (Fin 8)) :
    Pm σ *ᵥ ind S = ind (S.map σ.toEmbedding) := by
  rw [Pm_mulVec]
  ext k
  simp [ind, Finset.mem_map_equiv]

theorem Mm_vS (σ : Perm (Fin 8)) {S : Finset (Fin 8)} (hS : Even S.card) :
    Mm σ *ᵥ vS S = vS (S.map σ.toEmbedding) := by
  have hp : ∑ k, ind S k = 0 := by
    rw [sum_ind, ZMod.natCast_eq_zero_iff_even]
    exact hS
  have hP : Pm σ *ᵥ ind S = ind (S.map σ.toEmbedding) := Pm_mulVec_ind σ S
  rw [Mm_mulVec, vS, vS, ← hP]
  rcases FT _ hp with h | h
  · rw [h]
  · rw [h, Matrix.mulVec_add, Pm_one8, Matrix.mulVec_add, T_one, add_zero]

theorem vS_eq_zero_iff {S : Finset (Fin 8)} (hS : Even S.card) :
    vS S = 0 ↔ S = ∅ ∨ S = Finset.univ := by
  have h0 : ind S = 0 ↔ S = ∅ := by
    constructor
    · intro h
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have := congrFun h k
      simp [ind, hk] at this
    · rintro rfl
      funext k
      simp [ind]
  have h1 : ind S = one8 ↔ S = Finset.univ := by
    constructor
    · intro h
      rw [Finset.eq_univ_iff_forall]
      intro k
      by_contra hk
      have := congrFun h k
      simp [ind, one8, hk] at this
    · rintro rfl
      funext k
      simp [ind, one8]
  constructor
  · intro h
    have hsum : ∑ k, ind S k = 0 := by
      rw [sum_ind, ZMod.natCast_eq_zero_iff_even]
      exact hS
    have hne := Tm_ne_zero (ind S) hsum
    by_cases hzero : ind S = 0
    · left; exact h0.mp hzero
    · right
      have hone : ind S = one8 := by
        by_contra hne1
        exact hne hzero hne1 h
      exact h1.mp hone
  · rintro (rfl | rfl)
    · have hz : ind ∅ = (0 : Fin 8 → ZMod 2) := by funext k; simp [ind]
      rw [vS, hz, Matrix.mulVec_zero]
    · have huniv : ind Finset.univ = one8 := by
        funext k
        simp [ind, one8]
      rw [vS, huniv, T_one]

theorem uvec_eq_vS {a b : Fin 8} (h : a ≠ b) : uvec a b = vS {a, b} := by
  have hp : pairvec a b = ind {a, b} := by
    funext k
    by_cases ha : k = a
    · simp [pairvec, ind, ha, h]
    · by_cases hb : k = b
      · simp [pairvec, ind, ha, hb, Ne.symm h]
      · simp [pairvec, ind, ha, hb]
  rw [uvec, vS, hp]

theorem polar6_vS {S T : Finset (Fin 8)} (hS : Even S.card) (hT : Even T.card) :
    polar6 (vS S) (vS T) = ((S ∩ T).card : ZMod 2) := by
  have hSs : ∑ k, ind S k = 0 := by
    rw [sum_ind, ZMod.natCast_eq_zero_iff_even]; exact hS
  have hTs : ∑ k, ind T k = 0 := by
    rw [sum_ind, ZMod.natCast_eq_zero_iff_even]; exact hT
  rw [vS, vS, polar_Tm _ _ hSs hTs]
  have hprod : ∀ k, ind S k * ind T k = ind (S ∩ T) k := by
    intro k
    by_cases hkS : k ∈ S <;> by_cases hkT : k ∈ T <;>
      simp [ind, hkS, hkT, Finset.mem_inter]
  simp_rw [hprod]
  rw [sum_ind]

theorem exists_vS_of_singular {x : ι6 → ZMod 2} (hx0 : x ≠ 0) (hx : Q6 x = 0) :
    ∃ T : Finset (Fin 8), T.card = 4 ∧ x = vS T :=
  exists_vS_of_singular_decide x hx0 hx

theorem polar6_self (v : ι6 → ZMod 2) : polar6 v v = 0 := by
  rw [polar6_eq]
  simp [CharTwo.add_self_eq_zero]

theorem polar6_add_left (u v w : ι6 → ZMod 2) :
    polar6 (u + v) w = polar6 u w + polar6 v w := by
  simp [polar6]

theorem polar6_smul_left (c : ZMod 2) (v w : ι6 → ZMod 2) :
    polar6 (c • v) w = c * polar6 v w := by
  rw [polar6, polar6, smul_dotProduct]
  rfl

theorem polar6_zero_left (w : ι6 → ZMod 2) : polar6 0 w = 0 := by
  simp [polar6]

theorem exists_polar6_eq_one {y : ι6 → ZMod 2} (hy : y ≠ 0) : ∃ v, polar6 v y = 1 :=
  nondeg6 y hy

end CFSG.GF2Type.Smith1979W3.CaseD
