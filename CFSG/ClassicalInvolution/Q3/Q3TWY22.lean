module

public import CFSG.ClassicalInvolution.Q3.Q3TWY17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.TWE.B4
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TY
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Lift

theorem lift_twin_odd3 {m : ℕ} (hm3 : 3 ≤ m) {X : Type} [Group X]
    (θ : spinGroup (quadOdd m 𝔽₃) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m 𝔽₃)))
    (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z)
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R R' : Subgroup (spinGroup (quadOdd m 𝔽₃))} {a b : ℕ} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (x : spinGroup (quadOdd m 𝔽₃))
    (hR : R = ((rootSL2 (oddFrame m 𝔽₃).toHypFrame a b ha hb hab true true).map
      (MulAut.conj x).toMonoidHom))
    (hR' : R' = ((rootSL2 (oddFrame m 𝔽₃).toHypFrame a b ha hb hab true false).map
      (MulAut.conj x).toMonoidHom))
    (hRp : Pow3 R) (hR'p : Pow3 R')
    (hfixM : ∀ y ∈ R, σ (θ y) = θ y) (hfixM' : ∀ y ∈ R', σ (θ y) = θ y) :
    ∃ (α : spinGroup (quadOdd m 𝔽₃) ≃* spinGroup (quadOdd m 𝔽₃))
      (g₀ : (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃)),
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadOdd m 𝔽₃) (α y) (g₀ z) =
        g₀ (spinAction (quadOdd m 𝔽₃) y z)) ∧
      (∀ c : Fin m, (c.val = a ∨ c.val = b) → ∀ s,
        g₀ (spinAction (quadOdd m 𝔽₃) x ((oddFrame m 𝔽₃).vec c s)) =
        spinAction (quadOdd m 𝔽₃) x ((oddFrame m 𝔽₃).vec c s)) := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hK : Nat.card 𝔽₃ = 3 ^ 1 := by rw [card_gf3]; norm_num
  set F₀ := (oddFrame m 𝔽₃).toHypFrame with hF₀
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_odd (p := 3) (f := 1) (by norm_num) hm3
    (le_refl 1) hK θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd m 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadOdd m 𝔽₃) →* _).comp
      (α : spinGroup (quadOdd m 𝔽₃) →* _))
      (MonoidHom.id (spinGroup (quadOdd m 𝔽₃))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hαM : ∀ r ∈ R, α r = r := eq_of_fixed_of_pow3 θ hker hcop α σ hαθ hRp hfixM
  have hαM' : ∀ r ∈ R', α r = r := eq_of_fixed_of_pow3 θ hker hcop α σ hαθ hR'p hfixM'
  let ia : Fin m := ⟨a, ha⟩
  let ib : Fin m := ⟨b, hb⟩
  have hab' : ia ≠ ib := fun h => hab (congrArg Fin.val h)
  have hba' : ib ≠ ia := hab'.symm
  have hmem : ∀ (s t : Bool) (c : 𝔽₃), ∃ t' : Bool,
      F₀.longRoot hab' s t (.ofAdd c) ∈ rootSL2 F₀ a b ha hb hab true t' := by
    intro s t c
    cases s
    · refine ⟨!t, ?_⟩
      rw [F₀.longRoot_swap hab' false t c]
      have e : F₀.longRoot hab'.symm t false (.ofAdd (-c)) =
          F₀.longSL2 hab' true (!t) (lowerSL2 (-c)) := by
        rw [HypFrame.longSL2_lowerSL2]
        simp
      show _ ∈ (F₀.longSL2 hab' true (!t)).range
      rw [e]
      exact ⟨_, rfl⟩
    · refine ⟨t, ?_⟩
      show _ ∈ (F₀.longSL2 hab' true t).range
      rw [← HypFrame.longSL2_upperSL2]
      exact ⟨_, rfl⟩
  have hfix23 : ∀ (s t : Bool) (c : 𝔽₃),
      conjTwist α x (F₀.longRoot hab' s t (.ofAdd c)) = F₀.longRoot hab' s t (.ofAdd c) := by
    intro s t c
    obtain ⟨t', ht'⟩ := hmem s t c
    have hy : x * F₀.longRoot hab' s t (.ofAdd c) * x⁻¹ ∈
        (rootSL2 F₀ a b ha hb hab true t').map (MulAut.conj x).toMonoidHom := ⟨_, ht', rfl⟩
    have hα' : α (x * F₀.longRoot hab' s t (.ofAdd c) * x⁻¹) =
        x * F₀.longRoot hab' s t (.ofAdd c) * x⁻¹ := by
      cases t'
      · rw [← hR'] at hy
        exact hαM' _ hy
      · rw [← hR] at hy
        exact hαM _ hy
    rw [conjTwist_apply, hα']
    group
  have hO : ∀ (c d : Fin m) (hcd : c ≠ d), (fun c : Fin m => c = ia ∨ c = ib) c →
      (fun c : Fin m => c = ia ∨ c = ib) d → ∀ (s t : Bool) (c' : 𝔽₃),
      conjTwist α x ((oddFrame m 𝔽₃).longRoot hcd s t (.ofAdd c')) =
        (oddFrame m 𝔽₃).longRoot hcd s t (.ofAdd c') := by
    intro c d hcd hc hd s t c'
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact absurd rfl hcd
    · exact hfix23 s t c'
    · rw [F₀.longRoot_swap hba' s t c']
      exact hfix23 t s (-c')
    · exact absurd rfl hcd
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot hab' true true (.ofAdd c)) =
      F₀.longRoot hab' true true (.ofAdd c) := fun c => hfix23 true true c
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ hab' true true hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar_odd h2
    (oddFrame m 𝔽₃) (fun y hy => odd_orth_eq_smul_z m hy) hα hα2 x
    (O := fun c : Fin m => c = ia ∨ c = ib) (a₁ := ia) (a₂ := ib) (Or.inl rfl) (Or.inr rfl)
    hab' hφ hO
  refine ⟨α, g₀, hαθ, hg₀O, hg₀2, hconj, fun c hc s => hfixv c ?_ s⟩
  rcases hc with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

end Lift

end CFSG.ClassicalInvolution.Q3.Q3TWY
