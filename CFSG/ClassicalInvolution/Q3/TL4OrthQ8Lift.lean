module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Q8
public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.OrthQ8

open CFSG.ClassicalInvolution.Generic QuaternionGroup

theorem q8_pow_four : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by
  decide

theorem q8_cases (q : QuaternionGroup 2) : ∃ k : ℕ, q = a 1 ^ k ∨ q = xa 0 * a 1 ^ k := by
  cases q with
  | a k => exact ⟨k.val, Or.inl (by rw [a_one_pow, ZMod.natCast_zmod_val])⟩
  | xa k => exact ⟨k.val, Or.inr (by rw [a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add])⟩

private theorem q8_rel :
    (a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧ (xa 0 : QuaternionGroup 2) ^ 2 = a 1 ^ 2 ∧
      xa 0 * a 1 * (xa 0)⁻¹ = (a 1 : QuaternionGroup 2)⁻¹ ∧
      (xa 0 * a 1 : QuaternionGroup 2) ^ 2 = a 1 ^ 2 ∧ (xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
      (xa 0 * a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by
  decide

namespace Lift

variable {G S : Type*} [Group G] [Group S]

section Gen

variable {A : Subgroup S} (e : ↥A ≃* QuaternionGroup 2)

@[expose] def genX : S := (e.symm (a 1) : S)

@[expose] def genY : S := (e.symm (xa 0) : S)

theorem genX_mem : genX e ∈ A := (e.symm (a 1)).2

theorem genY_mem : genY e ∈ A := (e.symm (xa 0)).2

private theorem coe_pow (q : QuaternionGroup 2) (k : ℕ) :
    ((e.symm (q ^ k) : ↥A) : S) = (e.symm q : S) ^ k := by
  rw [map_pow, Subgroup.coe_pow]

theorem genX_pow_four : genX e ^ 4 = 1 := by
  rw [genX, ← coe_pow, q8_pow_four, map_one, Subgroup.coe_one]

theorem genX_sq_ne_one : genX e ^ 2 ≠ 1 := by
  intro h
  apply q8_rel.1
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_pow, map_one]
  exact h

theorem genY_sq : genY e ^ 2 = genX e ^ 2 := by
  have h := congrArg (fun q => (e.symm q : S)) q8_rel.2.1
  simpa only [coe_pow, genX, genY] using h

theorem conj_genY_genX : genY e * genX e * (genY e)⁻¹ = (genX e)⁻¹ := by
  have h := congrArg (fun q => (e.symm q : S)) q8_rel.2.2.1
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, genX, genY] using h

theorem genYX_sq : (genY e * genX e) ^ 2 = genX e ^ 2 := by
  have h := congrArg (fun q => (e.symm q : S)) q8_rel.2.2.2.1
  simpa only [map_pow, map_mul, Subgroup.coe_pow, Subgroup.coe_mul, genX, genY] using h

theorem genY_sq_ne_one : genY e ^ 2 ≠ 1 := by
  rw [genY_sq]
  exact genX_sq_ne_one e

theorem genYX_sq_ne_one : (genY e * genX e) ^ 2 ≠ 1 := by
  rw [genYX_sq]
  exact genX_sq_ne_one e

theorem mem_cases {s : S} (hs : s ∈ A) : ∃ k : ℕ, s = genX e ^ k ∨ s = genY e * genX e ^ k := by
  obtain ⟨k, hk | hk⟩ := q8_cases (e ⟨s, hs⟩)
  · refine ⟨k, Or.inl ?_⟩
    have h := congrArg (fun q => (e.symm q : S)) hk
    simpa only [MulEquiv.symm_apply_apply, coe_pow, genX] using h
  · refine ⟨k, Or.inr ?_⟩
    have h := congrArg (fun q => (e.symm q : S)) hk
    simpa only [MulEquiv.symm_apply_apply, map_mul, Subgroup.coe_mul, coe_pow, genX, genY] using h

theorem le_of_mem {M : Subgroup S} (hx : genX e ∈ M) (hy : genY e ∈ M) : A ≤ M := by
  intro s hs
  obtain ⟨k, rfl | rfl⟩ := mem_cases e hs
  · exact M.pow_mem hx k
  · exact M.mul_mem hy (M.pow_mem hx k)

theorem natCard_eq (e : ↥A ≃* QuaternionGroup 2) : Nat.card ↥A = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end Gen

section Aut

variable {A : Subgroup S} (e : ↥A ≃* QuaternionGroup 2) {c : S}

@[expose] def conjEquiv (hc : conjSub c A = A) : ↥A ≃* ↥A where
  toFun s := ⟨c * s * c⁻¹, by have h := conj_mem_conjSub (n := c) s.2; rwa [hc] at h⟩
  invFun s := ⟨c⁻¹ * s * c, by
    have h : (s : S) ∈ conjSub c A := by rw [hc]; exact s.2
    exact mem_conjSub_iff.mp h⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem coe_conjEquiv (hc : conjSub c A = A) (s : ↥A) :
    ((conjEquiv hc s : ↥A) : S) = c * s * c⁻¹ := rfl

@[expose] def qAut (hc : conjSub c A = A) : MulAut (QuaternionGroup 2) :=
  (e.symm.trans (conjEquiv hc)).trans e

theorem qAut_pow_apply (hc : conjSub c A = A) (m : ℕ) (q : QuaternionGroup 2) :
    (qAut e hc ^ m) q =
      e ⟨c ^ m * e.symm q * (c ^ m)⁻¹, by
        have h : ∀ k : ℕ, ∀ s ∈ A, c ^ k * s * (c ^ k)⁻¹ ∈ A := by
          intro k
          induction k with
          | zero => intro s hs; simpa using hs
          | succ k ih =>
            intro s hs
            have h0 : c * s * c⁻¹ ∈ A := by
              have h := conj_mem_conjSub (n := c) hs; rwa [hc] at h
            have h1 := ih _ h0
            rwa [show c ^ k * (c * s * c⁻¹) * (c ^ k)⁻¹ = c ^ (k + 1) * s * (c ^ (k + 1))⁻¹ by
              group] at h1
        exact h m _ (e.symm q).2⟩ := by
  induction m generalizing q with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one, MulAut.one_apply]
    exact (e.apply_symm_apply q).symm
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    congr 1
    apply Subtype.ext
    simp only [qAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, coe_conjEquiv]
    group

theorem exists_conj_eq (e : ↥A ≃* QuaternionGroup 2) (hc : conjSub c A = A) (hc3 : c ^ 3 = 1)
    (hne : ∃ s ∈ A, c * s * c⁻¹ ≠ s) {u w : S} (hu : u ∈ A) (hu2 : u ^ 2 ≠ 1) (hw : w ∈ A)
    (hw2 : w ^ 2 ≠ 1) :
    ∃ m : ℕ, c ^ m * u * (c ^ m)⁻¹ = w ∨ c ^ m * u * (c ^ m)⁻¹ = w⁻¹ := by
  have h3 : qAut e hc ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    rw [qAut_pow_apply, MulAut.one_apply]
    apply e.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    simp [hc3]
  have h1 : qAut e hc ≠ 1 := by
    obtain ⟨s, hs, hsne⟩ := hne
    intro h1
    have h2 := congrArg (fun φ : MulAut (QuaternionGroup 2) => φ (e ⟨s, hs⟩)) h1
    simp only [MulAut.one_apply] at h2
    have h3 := qAut_pow_apply e hc 1 (e ⟨s, hs⟩)
    rw [pow_one, h2] at h3
    have h4 := congrArg Subtype.val (e.injective h3)
    simp only [MulEquiv.symm_apply_apply, pow_one] at h4
    exact hsne h4.symm
  have hsq : ∀ s : ↥A, (s : S) ^ 2 ≠ 1 → e s ^ 2 ≠ 1 := fun s hs h2 => hs (by
    have := congrArg (fun q => (e.symm q : S)) h2
    simpa only [map_pow, MulEquiv.symm_apply_apply, Subgroup.coe_pow, map_one,
      Subgroup.coe_one] using this)
  obtain ⟨m, -, hm⟩ := CFSG.ClassicalInvolution.q8_aut_transitive h3 h1
    (hsq ⟨u, hu⟩ hu2) (q8_pow_four _) (hsq ⟨w, hw⟩ hw2) (q8_pow_four _)
  refine ⟨m, ?_⟩
  rw [qAut_pow_apply] at hm
  rcases hm with hm | hm
  · left
    have := congrArg Subtype.val (e.injective hm)
    simpa only [MulEquiv.symm_apply_apply] using this
  · right
    rw [← map_inv] at hm
    have := congrArg Subtype.val (e.injective hm)
    simpa only [MulEquiv.symm_apply_apply, Subgroup.coe_inv] using this

end Aut

section Lifts

variable (θ : G →* S)

theorem exists_ker_mul {T T' : G} (h : θ T = θ T') : ∃ z ∈ θ.ker, T' = z * T :=
  ⟨T' * T⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel], by group⟩

theorem comm_of_pow_three (hker : θ.ker ≤ Subgroup.center G)
    (hker2 : ∀ z ∈ θ.ker, z * z = 1) {g T : G} (hg3 : g ^ 3 = 1)
    (h : θ g * θ T = θ T * θ g) : g * T = T * g := by
  set z := g * T * g⁻¹ * T⁻¹ with hz
  have hzk : z ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hzc : ∀ w : G, w * z = z * w := fun w => Subgroup.mem_center_iff.mp (hker hzk) w
  have hzz := hker2 z hzk
  have e1 : g * T * g⁻¹ = z * T := by rw [hz]; group
  have hg2 : g * g = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three']
    exact hg3
  have e2 : g * g * T * (g * g)⁻¹ = T := by
    calc g * g * T * (g * g)⁻¹ = g * (g * T * g⁻¹) * g⁻¹ := by group
      _ = g * (z * T) * g⁻¹ := by rw [e1]
      _ = z * (g * T * g⁻¹) := by rw [← mul_assoc g z, hzc g]; group
      _ = T := by rw [e1, ← mul_assoc, hzz, one_mul]
  rw [hg2, inv_inv] at e2
  calc g * T = g * (g⁻¹ * T * g) := by rw [e2]
    _ = T * g := by group

theorem comm_or_moved (hker : θ.ker ≤ Subgroup.center G) (hker2 : ∀ z ∈ θ.ker, z * z = 1)
    {A : Subgroup S} (e : ↥A ≃* QuaternionGroup 2) {g : G} (hg3 : g ^ 3 = 1)
    (hgA : conjSub (θ g) A = A) {X H : G} (hXA : θ X ∈ A) (hX2 : θ X ^ 2 ≠ 1) (hHA : θ H ∈ A)
    (hH2 : θ H ^ 2 ≠ 1) :
    (∀ T : G, θ T ∈ A → g * T = T * g) ∨
      ∃ m : ℕ, ∃ z ∈ θ.ker, g ^ m * X * (g ^ m)⁻¹ = z * H ∨ g ^ m * X * (g ^ m)⁻¹ = z * H⁻¹ := by
  by_cases hall : ∀ T : G, θ T ∈ A → g * T = T * g
  · exact Or.inl hall
  right
  have hne : ∃ s ∈ A, θ g * s * (θ g)⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    apply hall
    intro T hT
    refine comm_of_pow_three θ hker hker2 hg3 ?_
    have := hcon _ hT
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  obtain ⟨m, hm⟩ := exists_conj_eq e hgA (by rw [← map_pow, hg3, map_one]) hne hXA hX2 hHA hH2
  refine ⟨m, ?_⟩
  rcases hm with hm | hm
  · obtain ⟨z, hz, hzeq⟩ := exists_ker_mul θ (T := H) (T' := g ^ m * X * (g ^ m)⁻¹)
      (by simp only [map_mul, map_inv, map_pow]; rw [hm])
    exact ⟨z, hz, Or.inl hzeq⟩
  · obtain ⟨z, hz, hzeq⟩ := exists_ker_mul θ (T := H⁻¹) (T' := g ^ m * X * (g ^ m)⁻¹)
      (by simp only [map_mul, map_inv, map_pow]; rw [hm])
    exact ⟨z, hz, Or.inr hzeq⟩

theorem mul_self_eq_of_moved (hker : θ.ker ≤ Subgroup.center G)
    (hker2 : ∀ z ∈ θ.ker, z * z = 1) {g X H : G} (hρρ : X * X * (X * X) = 1)
    (hgρ : g * (X * X) = X * X * g) {m : ℕ} {z : G} (hz : z ∈ θ.ker)
    (h : g ^ m * X * (g ^ m)⁻¹ = z * H ∨ g ^ m * X * (g ^ m)⁻¹ = z * H⁻¹) : H * H = X * X := by
  have hzc : ∀ w : G, w * z = z * w := fun w => Subgroup.mem_center_iff.mp (hker hz) w
  have hzz := hker2 z hz
  have hgm : g ^ m * (X * X) = X * X * g ^ m := (Commute.pow_left hgρ m)
  have hsq : (g ^ m * X * (g ^ m)⁻¹) * (g ^ m * X * (g ^ m)⁻¹) = X * X := by
    calc (g ^ m * X * (g ^ m)⁻¹) * (g ^ m * X * (g ^ m)⁻¹) = g ^ m * (X * X) * (g ^ m)⁻¹ := by
          group
      _ = X * X := by rw [hgm]; group
  have hzsq : ∀ w : G, (z * w) * (z * w) = w * w := fun w => by
    calc (z * w) * (z * w) = z * (w * z) * w := by group
      _ = w * w := by rw [hzc w, ← mul_assoc, hzz, one_mul]
  rcases h with h | h
  · rw [h, hzsq] at hsq
    exact hsq
  · rw [h, hzsq] at hsq
    have h1 : H * H = (X * X)⁻¹ := by
      rw [← hsq, mul_inv_rev, inv_inv]
    rw [h1, inv_eq_of_mul_eq_one_right hρρ]

end Lifts

section Rho

variable (θ : G →* S) {A : Subgroup S} (e : ↥A ≃* QuaternionGroup 2)

theorem rho_mul_rho (hker : θ.ker ≤ Subgroup.center G) (hker2 : ∀ z ∈ θ.ker, z * z = 1)
    {X Y : G} (hX : θ X = genX e) (hY : θ Y = genY e) :
    X * X * (X * X) = 1 ∧ Y * (X * X) = X * X * Y := by
  obtain ⟨z₁, hz₁, h₁⟩ := exists_ker_mul θ (T := X * X) (T' := Y * Y)
    (by rw [map_mul, map_mul, hX, hY, ← pow_two, ← pow_two, genY_sq])
  obtain ⟨z₂, hz₂, h₂⟩ := exists_ker_mul θ (T := X⁻¹) (T' := Y * X * Y⁻¹)
    (by rw [map_mul, map_mul, map_inv, map_inv, hX, hY, conj_genY_genX])
  have hc₁ : ∀ w : G, w * z₁ = z₁ * w := fun w => Subgroup.mem_center_iff.mp (hker hz₁) w
  have hc₂ : ∀ w : G, w * z₂ = z₂ * w := fun w => Subgroup.mem_center_iff.mp (hker hz₂) w
  have hzz₂ := hker2 z₂ hz₂
  have hYρ : Y * (X * X) = X * X * Y := by
    have hρ : X * X = z₁⁻¹ * (Y * Y) := by rw [h₁]; group
    rw [hρ]
    have hc₁' : ∀ w : G, w * z₁⁻¹ = z₁⁻¹ * w := fun w =>
      (show Commute w z₁ from hc₁ w).inv_right
    calc Y * (z₁⁻¹ * (Y * Y)) = (Y * z₁⁻¹) * (Y * Y) := by group
      _ = z₁⁻¹ * (Y * Y) * Y := by rw [hc₁']; group
  refine ⟨?_, hYρ⟩
  have hconj : Y * (X * X) * Y⁻¹ = (X * X)⁻¹ := by
    calc Y * (X * X) * Y⁻¹ = (Y * X * Y⁻¹) * (Y * X * Y⁻¹) := by group
      _ = z₂ * X⁻¹ * (z₂ * X⁻¹) := by rw [h₂]
      _ = z₂ * (X⁻¹ * z₂) * X⁻¹ := by group
      _ = (X * X)⁻¹ := by rw [hc₂, ← mul_assoc, hzz₂, one_mul]; group
  rw [hYρ, mul_inv_cancel_right] at hconj
  calc X * X * (X * X) = X * X * (X * X)⁻¹ := by rw [← hconj]
    _ = 1 := mul_inv_cancel _

theorem conjSub_eq_of_sq {r : S} (hsq : ∀ c ∈ Subgroup.centralizer ({r} : Set S),
      conjSub (c * c) A = A) {g ρ : G} (hρ : θ ρ = r) (hg3 : g ^ 3 = 1) (hgρ : g * ρ = ρ * g) :
    conjSub (θ g) A = A := by
  have hc : θ (g * g) ∈ Subgroup.centralizer ({r} : Set S) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hρ, ← map_mul, ← map_mul]
    congr 1
    calc g * g * ρ = g * (g * ρ) := by rw [mul_assoc]
      _ = g * (ρ * g) := by rw [hgρ]
      _ = (g * ρ) * g := by rw [mul_assoc]
      _ = ρ * g * g := by rw [hgρ]
      _ = ρ * (g * g) := by rw [mul_assoc]
  have h := hsq _ hc
  rwa [← map_mul, show g * g * (g * g) = g by
    calc g * g * (g * g) = g ^ 3 * g := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = g := by rw [hg3, one_mul]] at h

end Rho

end Lift

end CFSG.ClassicalInvolution.Q3.TL4.OrthQ8
