module

public import CFSG.ClassicalInvolution.Q3.Q3TY15
public import CFSG.ClassicalInvolution.RouteD.TWEB4Rec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B4
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD.TWT9
  CFSG.ClassicalInvolution.RouteD.TWT8
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Lift


theorem lift_td5_3 {X : Type} [Group X]
    (θ : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {RM RM' : Subgroup (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr 3 1)))
    (hRM'f : RM' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr 3 1)))
    (hne : RM' ≠ RM)
    (htwin : ∀ i j, IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) (RM.map (spinAction (quadMinus 5 (GaloisField 3 1)
          (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) i →
      IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (RM'.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) j → i = j)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hfixM' : ∀ y ∈ RM', σ (θ y) = θ y) :
    ∃ (x : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (α : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ≃*
        spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (g₀ : Vm 5 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 5 (GaloisField 3 1)),
      RM = ((rootSL2 (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 2 3
        (by omega) (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM' = ((rootSL2 (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 2 3
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) (α y) (g₀ z) =
        g₀ (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) y z)) ∧
      (∀ a : Fin (5 - 1), 2 ≤ a.val → ∀ s,
        g₀ (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) x ((minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).vec a s)) =
        spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x
          ((minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).vec a s)) := by
  classical
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 5; omega⟩
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_minus hadm
  have hY := yData3_minus (by norm_num : 4 ≤ 5) hadm
  have hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z := fun z hz => hY.cop z (hker hz)
  have hirr := minusCoeffs_irr 3 1
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 5 (by omega)]
    omega
  have hQ : (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField 3 1) hirr)
  set F₀ : HypFrame (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (5 - 1) := (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame with hF₀
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
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_minus (by norm_num : (3 : ℕ) ≠ 2)
    (by norm_num : 4 ≤ 5) le_rfl
    (by rw [card_gf3]; norm_num) hirr θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := isPerfect_spinGroup_quadMinus (by norm_num : 4 ≤ 5) hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →* _).comp
      (α : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) →* _))
      (MonoidHom.id (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hαM : ∀ r ∈ RM, α r = r :=
    eq_of_fixed_of_pow3 θ hker hcop α σ hαθ (cq.pow3 _ hRMf) hfixM
  have hαM' : ∀ r ∈ RM', α r = r :=
    eq_of_fixed_of_pow3 θ hker hcop α σ hαθ (cq.pow3 _ hRM'f) hfixM'
  let i2 : Fin (5 - 1) := ⟨2, by omega⟩
  let i3 : Fin (5 - 1) := ⟨3, by omega⟩
  have h23 : i2 ≠ i3 := fun h => by have := congrArg Fin.val h; simp [i2, i3] at this
  have h32 : i3 ≠ i2 := h23.symm
  have hmem : ∀ (s t : Bool) (c : GaloisField 3 1), ∃ t' : Bool,
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
  have hfix23 : ∀ (s t : Bool) (c : GaloisField 3 1),
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
  have hO : ∀ (a b : Fin (5 - 1)) (hab : a ≠ b), (fun a : Fin (5 - 1) => 2 ≤ a.val) a →
      (fun a : Fin (5 - 1) => 2 ≤ a.val) b → ∀ (s t : Bool) (c : GaloisField 3 1),
      conjTwist α x ((minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).longRoot hab s t
        (.ofAdd c)) =
        (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).longRoot hab s t (.ofAdd c) := by
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
    · rw [show (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).longRoot hab s t
          (.ofAdd c) = F₀.longRoot hab s t (.ofAdd c) from rfl, F₀.longRoot_swap h32 s t c]
      exact hfix23 t s (-c)
    · exact absurd rfl hab
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h23 true true (.ofAdd c)) =
      F₀.longRoot h23 true true (.ofAdd c) := fun c => hfix23 true true c
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h23 true true hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar_minus hirr hα hα2 x
    (O := fun a : Fin (5 - 1) => 2 ≤ a.val) (a₁ := i2) (a₂ := i3) (by simp [i2]) (by simp [i3])
    h23 hφ hO
  exact ⟨x, α, g₀, hRM, hRM', hαθ, hg₀O, hg₀2, hconj, fun a ha s => hfixv a ha s⟩


end Lift

end CFSG.ClassicalInvolution.Q3.Q3TY
