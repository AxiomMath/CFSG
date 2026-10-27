module

public import CFSG.ClassicalInvolution.Q3.Q3TWY16
public import CFSG.ClassicalInvolution.RouteD.TWEB4Rec

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
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (exists_spin_twin_pair)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Lift

theorem lift_b4_3 {X : Type} [Group X] (θ : spinGroup (quadOdd 4 𝔽₃) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd 4 𝔽₃)))
    (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z)
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {RM RM' : Subgroup (spinGroup (quadOdd 4 𝔽₃))}
    (hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 𝔽₃))
    (hRM'f : RM' ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 𝔽₃))
    (hne : RM' ≠ RM)
    (htwin : ∀ i j, IsFundamental (quadOdd 4 𝔽₃) (RM.map (spinAction (quadOdd 4 𝔽₃))) i →
      IsFundamental (quadOdd 4 𝔽₃) (RM'.map (spinAction (quadOdd 4 𝔽₃))) j → i = j)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hfixM' : ∀ y ∈ RM', σ (θ y) = θ y) :
    ∃ (x : spinGroup (quadOdd 4 𝔽₃)) (α : spinGroup (quadOdd 4 𝔽₃) ≃* spinGroup (quadOdd 4 𝔽₃))
      (g₀ : (Fin 4 ⊕ Fin 4 ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 ⊕ Unit → 𝔽₃)),
      RM = ((rootSL2 (oddFrame 4 𝔽₃).toHypFrame 2 3 (by omega) (by omega)
        (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM' = ((rootSL2 (oddFrame 4 𝔽₃).toHypFrame 2 3 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 4 𝔽₃) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadOdd 4 𝔽₃) (α y) (g₀ z) =
        g₀ (spinAction (quadOdd 4 𝔽₃) y z)) ∧
      (∀ a : Fin 4, 2 ≤ a.val → ∀ s,
        g₀ (spinAction (quadOdd 4 𝔽₃) x ((oddFrame 4 𝔽₃).vec a s)) =
        spinAction (quadOdd 4 𝔽₃) x ((oddFrame 4 𝔽₃).vec a s)) := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hK : Nat.card 𝔽₃ = 3 ^ 1 := by rw [card_gf3]; norm_num
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have cq := centralQuot3_odd (m := 4) hm3
  have hdim : 9 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
  have hQ : (quadOdd 4 𝔽₃).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd 4 _ h2)
  set F₀ := (oddFrame 4 𝔽₃).toHypFrame with hF₀
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  obtain ⟨FM, hFM, hiMe⟩ := hiM
  obtain ⟨x, hx1, hx2⟩ := exists_spin_twin_pair hodd hQ F₀ hdim FM
  have hRM : RM = ((rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true true).map
      (MulAut.conj x).toMonoidHom) :=
    cq.map_inj hRMf (cq.rootSL2_conj_mem F₀ _ _ _ true true x) (by rw [hFM, hx1])
  obtain ⟨iM', hiM'⟩ := cq.map_mem _ hRM'f
  obtain ⟨FM', hFM', hiM'e⟩ := hiM'
  have hii : FM'.La (-1) = FM.La (-1) := by
    have := htwin iM iM' ⟨FM, hFM, hiMe⟩ ⟨FM', hFM', hiM'e⟩
    rw [← hiMe, ← hiM'e]
    exact this.symm
  have hRM' : RM' = ((rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x).toMonoidHom) := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with h | h
    · exact absurd (cq.map_inj hRM'f hRMf (by rw [hFM', h, hFM])) hne
    · exact cq.map_inj hRM'f (cq.rootSL2_conj_mem F₀ _ _ _ true false x)
        (by rw [hFM', h, hx2])
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_odd (p := 3) (f := 1) (by norm_num) hm3
    (le_refl 1) hK θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadOdd 4 𝔽₃)) := isPerfect_spinGroup_quadOdd h2 hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadOdd 4 𝔽₃) →* _).comp
      (α : spinGroup (quadOdd 4 𝔽₃) →* _))
      (MonoidHom.id (spinGroup (quadOdd 4 𝔽₃))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hαM : ∀ r ∈ RM, α r = r :=
    eq_of_fixed_of_pow3 θ hker hcop α σ hαθ (cq.pow3 _ hRMf) hfixM
  have hαM' : ∀ r ∈ RM', α r = r :=
    eq_of_fixed_of_pow3 θ hker hcop α σ hαθ (cq.pow3 _ hRM'f) hfixM'
  let i2 : Fin 4 := ⟨2, by omega⟩
  let i3 : Fin 4 := ⟨3, by omega⟩
  have h23 : i2 ≠ i3 := fun h => by have := congrArg Fin.val h; simp [i2, i3] at this
  have h32 : i3 ≠ i2 := h23.symm
  have hmem : ∀ (s t : Bool) (c : 𝔽₃), ∃ t' : Bool,
      F₀.longRoot h23 s t (.ofAdd c) ∈
        rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true t' := by
    intro s t c
    cases s
    · refine ⟨!t, ?_⟩
      rw [F₀.longRoot_swap h23 false t c]
      have e : F₀.longRoot h23.symm t false (.ofAdd (-c)) =
          F₀.longSL2 h23 true (!t) (lowerSL2 (-c)) := by
        rw [HypFrame.longSL2_lowerSL2]
        simp
      show _ ∈ (F₀.longSL2 h23 true (!t)).range
      rw [e]
      exact ⟨_, rfl⟩
    · refine ⟨t, ?_⟩
      show _ ∈ (F₀.longSL2 h23 true t).range
      rw [← HypFrame.longSL2_upperSL2]
      exact ⟨_, rfl⟩
  have hfix23 : ∀ (s t : Bool) (c : 𝔽₃),
      conjTwist α x (F₀.longRoot h23 s t (.ofAdd c)) = F₀.longRoot h23 s t (.ofAdd c) := by
    intro s t c
    obtain ⟨t', ht'⟩ := hmem s t c
    have hy : x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ ∈
        (rootSL2 F₀ 2 3 (by omega) (by omega) (by omega) true t').map
          (MulAut.conj x).toMonoidHom := ⟨_, ht', rfl⟩
    have hα' : α (x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹) =
        x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ := by
      cases t'
      · rw [← hRM'] at hy
        exact hαM' _ hy
      · rw [← hRM] at hy
        exact hαM _ hy
    rw [conjTwist_apply, hα']
    group
  have hO : ∀ (a b : Fin 4) (hab : a ≠ b), (fun a : Fin 4 => 2 ≤ a.val) a →
      (fun a : Fin 4 => 2 ≤ a.val) b → ∀ (s t : Bool) (c : 𝔽₃),
      conjTwist α x ((oddFrame 4 𝔽₃).longRoot hab s t (.ofAdd c)) =
        (oddFrame 4 𝔽₃).longRoot hab s t (.ofAdd c) := by
    intro a b hab ha hb s t c
    have ha' : a = i2 ∨ a = i3 := by
      have ha2 : 2 ≤ a.val := ha
      have ha3 := a.isLt
      rcases (by omega : a.val = 2 ∨ a.val = 3) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    have hb' : b = i2 ∨ b = i3 := by
      have hb2 : 2 ≤ b.val := hb
      have hb3 := b.isLt
      rcases (by omega : b.val = 2 ∨ b.val = 3) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · exact hfix23 s t c
    · rw [F₀.longRoot_swap h32 s t c]
      exact hfix23 t s (-c)
    · exact absurd rfl hab
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h23 true true (.ofAdd c)) =
      F₀.longRoot h23 true true (.ofAdd c) := fun c => hfix23 true true c
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h23 true true hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar_odd h2
    (oddFrame 4 𝔽₃) (fun y hy => odd_orth_eq_smul_z 4 hy) hα hα2 x
    (O := fun a : Fin 4 => 2 ≤ a.val) (a₁ := i2) (a₂ := i3) (by simp [i2]) (by simp [i3]) h23 hφ
    hO
  exact ⟨x, α, g₀, hRM, hRM', hαθ, hg₀O, hg₀2, hconj, fun a ha s => hfixv a ha s⟩

end Lift

end CFSG.ClassicalInvolution.Q3.Q3TWY
