module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutNormal

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

section VLevel

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m)

theorem exists_adjust_vec (h2 : (2 : F) ≠ 0) (C : Submodule F V)
    (hC : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x ∈ C)
    (hCorth : ∀ x ∈ C, ∀ a r, polar Q x (Fr.vec a r) = 0) {g : V →ₗ[F] V} {μ : F}
    (hμ : ∀ x, Q (g x) = μ * Q x) {c : Fin m} (s : Bool) {l : F} (hl0 : l ≠ 0)
    (hu : g (Fr.vec c s) = l • Fr.vec c s) (hμl : μ = l * l)
    (hU : ∀ x : V, (∀ a, a ≠ c → ∀ r, polar Q x (Fr.vec a r) = 0) →
      ∀ a, a ≠ c → ∀ r, polar Q (g x) (Fr.vec a r) = 0)
    (hGw : g (g (Fr.vec c (!s))) = μ • Fr.vec c (!s)) :
    ∃ e ∈ C, g (eichler Q (Fr.vec c s) e (Fr.vec c (!s))) =
      l • eichler Q (Fr.vec c s) e (Fr.vec c (!s)) := by
  have hu0 : Q (Fr.vec c s) = 0 := Fr.map_vec c s
  have hw0 : Q (Fr.vec c (!s)) = 0 := Fr.map_vec c (!s)
  have hwu : polar Q (Fr.vec c (!s)) (Fr.vec c s) = 1 := Fr.polar_not_vec c s
  have huw : polar Q (Fr.vec c s) (Fr.vec c (!s)) = 1 := Fr.polar_vec_not c s
  have huu : polar Q (Fr.vec c s) (Fr.vec c s) = 0 := Fr.polar_vec_self c s
  have hugw : polar Q (Fr.vec c s) (g (Fr.vec c (!s))) = l := by
    have h1 := polar_map_of_similitude g hμ (Fr.vec c s) (Fr.vec c (!s))
    rw [hu, polar_smul_left, huw, smul_eq_mul, mul_one, hμl] at h1
    exact mul_left_cancel₀ hl0 h1
  obtain ⟨P, hP⟩ : ∃ P : V, P = (2 : F)⁻¹ • (Fr.vec c (!s) + l⁻¹ • g (Fr.vec c (!s))) := ⟨_, rfl⟩
  have hgP : g P = l • P := by
    rw [hP, map_smul, map_add, map_smul, hGw, hμl]
    match_scalars <;> field_simp
  have hPu : polar Q (Fr.vec c s) P = 1 := by
    rw [hP, polar_smul_right, polar_add_right, polar_smul_right, huw, hugw]
    simp only [smul_eq_mul]
    rw [inv_mul_cancel₀ hl0, show (1 : F) + 1 = 2 by norm_num, inv_mul_cancel₀ h2]
  obtain ⟨q, hq⟩ : ∃ q : F, q = Q P := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : V, w' = P - q • Fr.vec c s := ⟨_, rfl⟩
  have hgw' : g w' = l • w' := by
    rw [hw', map_sub, map_smul, hgP, hu]
    module
  have hPu' : polar Q P (Fr.vec c s) = 1 := by rw [polar_comm, hPu]
  have hw'u : polar Q w' (Fr.vec c s) = 1 := by
    rw [hw', polar_sub_left, polar_smul_left, hPu', huu]
    simp
  have hQw' : Q w' = 0 := by
    rw [hw', sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      polar_smul_right, hu0, hPu', ← hq]
    simp
  obtain ⟨θ, hθ⟩ : ∃ θ : F, θ = polar Q (w' - Fr.vec c (!s)) (Fr.vec c (!s)) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : V, e = (w' - Fr.vec c (!s)) - θ • Fr.vec c s := ⟨_, rfl⟩
  have hdec : w' = Fr.vec c (!s) + e + θ • Fr.vec c s := by
    rw [he]
    abel
  have heC : e ∈ C := by
    refine hC e fun a r => ?_
    by_cases hac : a = c
    · rw [hac]
      rcases Bool.eq_or_eq_not r s with hr | hr
      · rw [hr, he, polar_sub_left, polar_sub_left, polar_smul_left, hw'u, hwu, huu]
        simp
      · rw [hr, he, polar_sub_left, polar_smul_left, ← hθ, huw]
        simp
    · have hwa : ∀ r', polar Q (Fr.vec c (!s)) (Fr.vec a r') = 0 := fun r' =>
        Fr.polar_vec_of_ne (Ne.symm hac) (!s) r'
      have hua : ∀ r', polar Q (Fr.vec c s) (Fr.vec a r') = 0 := fun r' =>
        Fr.polar_vec_of_ne (Ne.symm hac) s r'
      have hgwa : polar Q (g (Fr.vec c (!s))) (Fr.vec a r) = 0 :=
        hU _ (fun a' ha' r' => Fr.polar_vec_of_ne (Ne.symm ha') (!s) r') a hac r
      have hPa : polar Q P (Fr.vec a r) = 0 := by
        rw [hP, polar_smul_left, polar_add_left, polar_smul_left, hwa, hgwa]
        simp
      rw [he, polar_sub_left, polar_sub_left, polar_smul_left, hw', polar_sub_left,
        polar_smul_left, hPa, hua, hwa]
      simp
  have hue : polar Q (Fr.vec c s) e = 0 := by rw [polar_comm]; exact hCorth e heC c s
  have hwe : polar Q (Fr.vec c (!s)) e = 0 := by rw [polar_comm]; exact hCorth e heC c (!s)
  have hQe : θ = -Q e := by
    have hue' : polar Q e (Fr.vec c s) = 0 := hCorth e heC c s
    have h1 : Q w' = Q e + θ := by
      rw [hdec, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul]
      simp only [polar_add_left, polar_smul_right, smul_eq_mul, hu0, hw0, hue', hwe, hwu]
      ring
    rw [hQw'] at h1
    linear_combination -h1
  have hE : eichler Q (Fr.vec c s) e (Fr.vec c (!s)) = w' := by
    rw [eichler_apply hu0 hue, hwu, hwe, hdec, hQe]
    module
  exact ⟨e, heC, by rw [hE, hgw']⟩

theorem scalar_vec_of_commute {G : V →ₗ[F] V} {ν : F} {a c : Fin m} (hac : a ≠ c) (s t : Bool)
    (hG : G (Fr.vec a (!t)) = ν • Fr.vec a (!t))
    (hcomm : ∀ x, G (eichler Q (Fr.vec a t) (Fr.vec c s) x) =
      eichler Q (Fr.vec a t) (Fr.vec c s) (G x)) : G (Fr.vec c s) = ν • Fr.vec c s := by
  have hu : Q (Fr.vec a t) = 0 := Fr.map_vec a t
  have huw : polar Q (Fr.vec a t) (Fr.vec c s) = 0 := Fr.polar_vec_of_ne hac t s
  have hE : eichler Q (Fr.vec a t) (Fr.vec c s) (Fr.vec a (!t)) =
      Fr.vec a (!t) + Fr.vec c s := by
    rw [eichler_apply hu huw, Fr.polar_not_vec a t, Fr.polar_vec_of_ne hac (!t) s, Fr.map_vec c s]
    simp
  have h1 := hcomm (Fr.vec a (!t))
  rw [hE, map_add, hG, map_smul, hE, smul_add] at h1
  exact add_left_cancel h1

variable {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem coords_eq_zero_of_orth_first {x : V}
    (hx : ∀ r, polar Q x (Fr.vec i₀ r) = 0 ∧ polar Q x (Fr.vec i₁ r) = 0) :
    (firstFrame Fr h01 s₀ t₀).coords x = 0 := by
  have h0 : ∀ r, polar Q x (Fr.vec i₀ r) = 0 := fun r => (hx r).1
  have h1 : ∀ r, polar Q x (Fr.vec i₁ r) = 0 := fun r => (hx r).2
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Frame.coords_apply, firstFrame, HypFrame.toFrame, h0, h1]

end VLevel

section AdjustedFrame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem conjTwist_mul_right (α : spinGroup Q ≃* spinGroup Q) (k y z : spinGroup Q) :
    conjTwist α (k * y) z = y⁻¹ * conjTwist α k (y * z * y⁻¹) * y := by
  have e : k * y * z * (k * y)⁻¹ = k * (y * z * y⁻¹) * k⁻¹ := by group
  rw [conjTwist_apply, conjTwist_apply, e]
  group

theorem conjTwist_mul_of_commute (α : spinGroup Q ≃* spinGroup Q) (k : spinGroup Q)
    {y z : spinGroup Q} (hyz : Commute y z) (hz : conjTwist α k z = z) :
    conjTwist α (k * y) z = z := by
  have h1 : y * z * y⁻¹ = z := by rw [hyz.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : y⁻¹ * z * y = z := by rw [hyz.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [conjTwist_mul_right, h1, hz, h2]

theorem exists_adjusted_frame (h2 : (2 : F) ≠ 0) (hm : 5 ≤ m) (C : Submodule F V)
    (hC : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x ∈ C)
    (hCorth : ∀ x ∈ C, ∀ a r, polar Q x (Fr.vec a r) = 0) {α : spinGroup Q ≃* spinGroup Q}
    {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y) (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c))
    {c₀ j : Fin m} (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀) (hj1 : j ≠ i₁) (hjc : c₀ ≠ j)
    (s₁ t₁ : Bool)
    (hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) (c : F), conjTwist α k (Fr.longRoot hab s t (.ofAdd c)) =
        Fr.longRoot hab s t (.ofAdd c))
    {c' : F} (hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c'))
    (hY : ∀ e ∈ C, ∃ y : spinGroup Q, spinAction Q y = eichler Q (Fr.vec c₀ s₁) e ∧
      ∀ (i j : Fin m) (hij : i ≠ j), i ≠ c₀ → j ≠ c₀ → ∀ (t t' : Bool) (c : F),
        Commute y (Fr.longRoot hij t t' (.ofAdd c))) :
    ∃ k' : spinGroup Q,
      (∀ c : F, conjTwist α k' (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
        Fr.longRoot h01 s₀ t₀ (.ofAdd c)) ∧
      (∀ c : F, conjTwist α k' (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
        Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) ∧
      ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g.conjSpin k' (Fr.vec i s) = c • Fr.vec i s := by
  classical
  obtain ⟨gL, hφ, hgL, hconj, hμL, hginj, hI1⟩ := exists_linear_conj Fr h01 s₀ t₀ hα k hA1 hA1'
  have hα₁c : IsConj (conjTwist α k) (g.conjSpin k) := hα.conjSpin k
  have hα₁2 : ∀ y, conjTwist α k (conjTwist α k y) = y := conjTwist_sq α hα2 k
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hcomm : ∀ a b : Fin m, a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) x, gL (eichler Q (Fr.vec b t) (Fr.vec a s) x) =
        eichler Q (Fr.vec b t) (Fr.vec a s) (gL x) := by
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s t x
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    rw [← e, ← hconj, hO a b hab ha0 ha1 hac hb0 hb1 hbc s t 1]
  have hnorm : ∀ z, gL (eichler Q (Fr.vec j t₁) (Fr.vec c₀ s₁) z) =
      eichler Q (Fr.vec j t₁) (c' • Fr.vec c₀ s₁) (gL z) := by
    intro z
    have e := Fr.spinAction_longRoot_eq_eichler hjc s₁ t₁ 1
    rw [one_smul] at e
    have e' := Fr.spinAction_longRoot_eq_eichler hjc s₁ t₁ c'
    rw [← e, ← e', ← hconj, hN]
  obtain ⟨a₁, a₂, ha₁0, ha₁1, ha₁c, ha₂0, ha₂1, ha₂c, h12⟩ := exists_two_others hm i₀ i₁ c₀
  obtain ⟨r, hr0, hrr, hr⟩ := diag_of_commuting_roots Fr gL hginj hμL
    (O := fun a => a ≠ i₀ ∧ a ≠ i₁ ∧ a ≠ c₀) ⟨ha₁0, ha₁1, ha₁c⟩ ⟨ha₂0, ha₂1, ha₂c⟩ h12
    (fun a b hab ha hb s t x => hcomm a b hab ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 s t x)
  have hl : gL (Fr.vec c₀ s₁) = (r * c') • Fr.vec c₀ s₁ :=
    map_vec_of_normalized (g := gL) (Fr.map_vec j t₁) (Fr.map_vec c₀ s₁)
      (Fr.polar_vec_of_ne hjc.symm t₁ s₁) (Fr.polar_not_vec j t₁)
      (Fr.polar_vec_of_ne hjc.symm (!t₁) s₁) (hr j ⟨hj0, hj1, hjc.symm⟩ (!t₁)) (hnorm _)
  have hl0 : r * c' ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hl
    exact polar_vec_ne_zero Fr c₀ s₁ (hginj (by rw [hl, map_zero]))
  have hGcomm : ∀ (y : spinGroup Q) x, gL (gL (spinAction Q y x)) =
      spinAction Q y (gL (gL x)) := fun y x => by
    rw [hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 y x
  have hGO : gL (gL (Fr.vec a₁ (!true))) = (g.μ : F) • Fr.vec a₁ (!true) := by
    rw [hr a₁ ⟨ha₁0, ha₁1, ha₁c⟩, map_smul, hr a₁ ⟨ha₁0, ha₁1, ha₁c⟩, smul_smul, hrr]
  have hGc : ∀ s, gL (gL (Fr.vec c₀ s)) = (g.μ : F) • Fr.vec c₀ s := by
    intro s
    refine scalar_vec_of_commute Fr (G := gL ∘ₗ gL) ha₁c s true ?_ ?_
    · exact hGO
    · intro x
      have e := Fr.spinAction_longRoot_eq_eichler ha₁c.symm s true 1
      rw [one_smul] at e
      change gL (gL (eichler Q (Fr.vec a₁ true) (Fr.vec c₀ s) x)) =
        eichler Q (Fr.vec a₁ true) (Fr.vec c₀ s) (gL (gL x))
      rw [← e]
      exact hGcomm _ x
  have hμl : (g.μ : F) = (r * c') * (r * c') := by
    have h1 := hGc s₁
    rw [hl, map_smul, hl, smul_smul] at h1
    exact ((smul_left_injective F (polar_vec_ne_zero Fr c₀ s₁)) h1).symm
  obtain ⟨-, -, hcoords⟩ := exists_mulRight_of_commute_La (firstFrame Fr h01 s₀ t₀) gL hI1
  have hU : ∀ x : V, (∀ a, a ≠ c₀ → ∀ r', polar Q x (Fr.vec a r') = 0) →
      ∀ a, a ≠ c₀ → ∀ r', polar Q (gL x) (Fr.vec a r') = 0 := by
    intro x hx a hac r'
    by_cases ha0 : a = i₀
    · rw [ha0]
      exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ (hcoords x
        (coords_eq_zero_of_orth_first Fr h01 s₀ t₀ fun r'' =>
          ⟨hx i₀ hc0.symm r'', hx i₁ hc1.symm r''⟩)) r').1
    · by_cases ha1 : a = i₁
      · rw [ha1]
        exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ (hcoords x
          (coords_eq_zero_of_orth_first Fr h01 s₀ t₀ fun r'' =>
            ⟨hx i₀ hc0.symm r'', hx i₁ hc1.symm r''⟩)) r').2
      · have h1 := polar_map_of_similitude gL hμL x (Fr.vec a r')
        rw [hr a ⟨ha0, ha1, hac⟩ r', polar_smul_right, hx a hac r', mul_zero, smul_eq_mul] at h1
        exact (mul_eq_zero.mp h1).resolve_left hr0
  obtain ⟨e, heC, hew⟩ := exists_adjust_vec Fr h2 C hC hCorth hμL s₁ hl0 hl hμl hU (hGc (!s₁))
  obtain ⟨y, hy, hycomm⟩ := hY e heC
  refine ⟨k * y, fun c => ?_, fun c => ?_, ?_⟩
  · exact conjTwist_mul_of_commute α k (hycomm i₀ i₁ h01 hc0.symm hc1.symm s₀ t₀ c) (hA1 c)
  · exact conjTwist_mul_of_commute α k
      (hycomm i₁ i₀ h01.symm hc1.symm hc0.symm (!t₀) (!s₀) c) (hA1' c)
  · have hconjSpin : ∀ v, g.conjSpin (k * y) v = spinAction Q y⁻¹ (gL (spinAction Q y v)) := by
      intro v
      rw [SemiSim.conjSpin_apply, mul_inv_rev, spinAction_mul_apply, spinAction_mul_apply, hgL]
      rfl
    have hinv : ∀ v, spinAction Q y v = v → spinAction Q y⁻¹ v = v := fun v hv => by
      have := spinAction_inv_apply y v
      rw [hv] at this
      exact this
    intro i hi0 hi1 s
    by_cases hic : i = c₀
    · rw [hic]
      rcases Bool.eq_or_eq_not s s₁ with hs | hs
      · have hfix : spinAction Q y (Fr.vec c₀ s₁) = Fr.vec c₀ s₁ := by
          rw [hy]
          exact eichler_apply_self _ _
        refine ⟨r * c', ?_⟩
        rw [hs, hconjSpin, hfix, hl, map_smul, hinv _ hfix]
      · have hEw : spinAction Q y (Fr.vec c₀ (!s₁)) =
            eichler Q (Fr.vec c₀ s₁) e (Fr.vec c₀ (!s₁)) := by rw [hy]
        refine ⟨r * c', ?_⟩
        rw [hs, hconjSpin, hEw, hew, ← hEw, map_smul, spinAction_inv_apply]
    · have hfix : spinAction Q y (Fr.vec i s) = Fr.vec i s := by
        rw [hy]
        exact eichler_apply_of_polar_eq_zero (Fr.polar_vec_of_ne hic s s₁)
          (by rw [polar_comm]; exact hCorth e heC i s)
      refine ⟨r, ?_⟩
      rw [hconjSpin, hfix, hr i ⟨hi0, hi1, hic⟩ s, map_smul, hinv _ hfix]

end AdjustedFrame

section DiagCompl

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {p : ℕ} [Fact p.Prime] [CharP F p] {m : ℕ} (Fr : HypFrame Q m) {i₀ i₁ : Fin m}
  (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_diag_form_of_diag_compl (hm : 3 ≤ m) (h2 : (2 : F) ≠ 0)
    (hp2 : p ≠ 2) (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c))
    (hmul : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g.conjSpin k (Fr.vec i s) = c • Fr.vec i s) :
    ∃ (κ : spinGroup Q) (lam : Fin m → Bool → F), (∀ c, g.φ c = c) ∧
      (∀ i, lam i true * lam i false = g.μ) ∧
      (∀ i s, g.conjSpin κ (Fr.vec i s) = lam i s • Fr.vec i s) ∧
      (∀ y : V, (∀ a r, polar Q y (Fr.vec a r) = 0) →
        ∀ a r, polar Q (g.conjSpin κ y) (Fr.vec a r) = 0) ∧
      (∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
        α (κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹) =
          κ * Fr.longRoot hij s t (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹) ∧
      ∃ r : spinGroup Q, κ = k * r⁻¹ ∧
        ∀ x : V, (firstFrame Fr h01 s₀ t₀).coords x = 0 → spinAction Q r x = x := by
  classical
  obtain ⟨gL, hφ, hgL, hconj, hμL, hginj, hI1⟩ := exists_linear_conj Fr h01 s₀ t₀ hα k hA1 hA1'
  have hα₁c : IsConj (conjTwist α k) (g.conjSpin k) := hα.conjSpin k
  have hα₁2 : ∀ y, conjTwist α k (conjTwist α k y) = y := conjTwist_sq α hα2 k
  have hI3 : ∀ (B : SL(2, F)) x, gL (gL ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
      (firstFrame Fr h01 s₀ t₀).swap.La B (gL (gL x)) := by
    intro B x
    have hLB : (firstFrame Fr h01 s₀ t₀).swap.La B =
        spinAction Q (Fr.longSL2 h01 s₀ (!t₀) B) := by
      rw [firstFrame, swap_toFrame]
      exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
    rw [hLB, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  obtain ⟨i₂, hi20, hi21⟩ := exists_ne_and_ne hm i₀ i₁
  have hI4 : ∀ x, gL (gL (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (gL (gL x)) := by
    intro x
    have e := Fr.spinAction_longRoot_eq_eichler (show i₁ ≠ i₂ from hi21.symm) (!t₀) false 1
    rw [one_smul] at e
    rw [← e, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  obtain ⟨B, lam, hlam, hprod⟩ := exists_eigenframe_of_diag Fr h01 s₀ t₀ h2 gL hginj hμL hI1
    (fun i hi0 hi1 s => by
      obtain ⟨c, hc⟩ := hmul i hi0 hi1 s
      exact ⟨c, by rw [hgL]; exact hc⟩) hI3 hi20 hi21 hI4
  set r := Fr.longSL2 h01 s₀ (!t₀) B with hr
  have hρ : (firstFrame Fr h01 s₀ t₀).swap.La B = spinAction Q r := by
    rw [firstFrame, swap_toFrame]
    exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
  have hρsymm : ∀ w, ((firstFrame Fr h01 s₀ t₀).swap.La B).symm w = spinAction Q r⁻¹ w :=
    fun w => by
    rw [LinearEquiv.symm_apply_eq, hρ, spinAction_apply_inv]
  have hg₂ : ∀ i s, g.conjSpin (k * r⁻¹) (Fr.vec i s) = lam i s • Fr.vec i s := by
    intro i s
    have h1 := hlam i s
    rw [hρsymm, hρ, hgL] at h1
    rw [SemiSim.conjSpin_apply, mul_inv_rev, inv_inv, spinAction_mul_apply r k⁻¹,
      spinAction_mul_apply k r⁻¹]
    exact h1
  have hα₂c : IsConj (conjTwist α (k * r⁻¹)) (g.conjSpin (k * r⁻¹)) := hα.conjSpin _
  have hφ₂ : ∀ c, (g.conjSpin (k * r⁻¹)).φ c = c := hφ
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hlam0 : ∀ i s, lam i s ≠ 0 := by
    intro i s h0
    apply hμ0
    rw [← hprod i]
    cases s
    · rw [h0, mul_zero]
    · rw [h0, zero_mul]
  refine ⟨k * r⁻¹, lam, hφ, hprod, hg₂, fun y hy a r' => ?_, fun i j hij s t c => ?_,
    r, rfl, fun x hx => ?_⟩
  · have h1 := (g.conjSpin (k * r⁻¹)).polar_apply y (Fr.vec a r')
    rw [hg₂ a r', hy a r', hφ₂, mul_zero, polar_smul_right, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hlam0 a r')
  · have h3 := IsConj.longRoot_eq hp2 hker2 Fr hα₂c lam (fun _ s => s) hg₂ hij s t c
    have e1 : α (k * r⁻¹ * Fr.longRoot hij s t (.ofAdd c) * (k * r⁻¹)⁻¹) =
        k * r⁻¹ * conjTwist α (k * r⁻¹) (Fr.longRoot hij s t (.ofAdd c)) * (k * r⁻¹)⁻¹ := by
      rw [conjTwist_apply]
      group
    rw [e1, h3, hφ₂ c]
    rfl
  · rw [← hρ]
    exact Frame.La_apply_of_coords_eq_zero (firstFrame Fr h01 s₀ t₀).swap B
      (by rw [Frame.coords_swap, hx, map_zero])

end DiagCompl

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
