module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveCommon

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E}

theorem smul_add_smul_eq_zero {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) {α γ : ZMod 2}
    (h : α • u + γ • v = 0) : α = 0 ∧ γ = 0 := by
  rcases zmod_two_cases α with rfl | rfl <;> rcases zmod_two_cases γ with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at h
    exact absurd h hv
  · rw [zero_smul, one_smul, add_zero] at h
    exact absurd h hu
  · rw [one_smul, one_smul] at h
    exact absurd (eq_of_add_eq_zero_zmod2 h) huv

theorem eq_zero_of_invariant_linear (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (ℓ : E →ₗ[ZMod 2] ZMod 2) (hℓ : ∀ (s : bilinIsometryGroup b) x, ℓ (sE s x) = ℓ x) (u : E) :
    ℓ u = 0 := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hu
  have h := hℓ (tau hb u) x
  rwa [sE_tau, hx, one_smul, map_add, add_eq_left] at h

theorem exists_eq_mul_of_invariant_bilin (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (β : LinearMap.BilinForm (ZMod 2) E)
    (hβ : ∀ (s : bilinIsometryGroup b) x y, β (sE s x) (sE s y) = β x y) :
    ∃ c : ZMod 2, ∀ x y, β x y = c * b x y := by
  have horth : ∀ v u, b v u = 0 → β v u = 0 := by
    intro v u hvu
    by_cases hu : u = 0
    · rw [hu, map_zero]
    obtain ⟨y, hy⟩ := exists_apply_eq_one hnd hu
    have h := hβ (tau hb u) v y
    rwa [sE_tau, sE_tau, hvu, hy, zero_smul, add_zero, one_smul, map_add, add_eq_left] at h
  have hline : ∀ v, v ≠ 0 → ∃ c : ZMod 2, ∀ y, β v y = c * b v y := by
    intro v hv
    obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hv
    rw [symm_apply hb] at hx
    refine ⟨β v x, fun y => ?_⟩
    have h0 : b v (y + b v y • x) = 0 := by
      rw [map_add, map_smul, smul_eq_mul, hx, mul_one, zmod2_add_self]
    have h1 := horth v _ h0
    rw [map_add, map_smul, smul_eq_mul] at h1
    rw [eq_of_add_eq_zero_zmod2 h1, mul_comm]
  by_cases hE0 : ∀ v : E, v = 0
  · exact ⟨0, fun x y => by rw [hE0 x, map_zero, LinearMap.zero_apply, zero_mul]⟩
  push Not at hE0
  obtain ⟨v₀, hv₀⟩ := hE0
  obtain ⟨c, hc⟩ := hline v₀ hv₀
  refine ⟨c, fun x y => ?_⟩
  by_cases hx : x = 0
  · simp only [hx, map_zero, LinearMap.zero_apply, mul_zero]
  by_cases hxv : x = v₀
  · rw [hxv, hc]
  obtain ⟨c₁, hc₁⟩ := hline x hx
  obtain ⟨c₂, hc₂⟩ := hline (x + v₀) fun h => hxv (eq_of_add_eq_zero_zmod2 h)
  have hz : (c₂ + c₁) • x + (c₂ + c) • v₀ = 0 := by
    refine hnd.1 _ fun y => ?_
    have h := hc₂ y
    rw [map_add, LinearMap.add_apply, hc₁, hc, map_add, LinearMap.add_apply] at h
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have key : ∀ a₁ a₂ a₃ p₁ p₂ : ZMod 2, a₁ * p₁ + a₃ * p₂ = a₂ * (p₁ + p₂) →
        (a₂ + a₁) * p₁ + (a₂ + a₃) * p₂ = 0 := by decide
    exact key _ _ _ _ _ h
  obtain ⟨h1, h2⟩ := smul_add_smul_eq_zero hx hv₀ hxv hz
  rw [hc₁, ← eq_of_add_eq_zero_zmod2 h1, eq_of_add_eq_zero_zmod2 h2]

theorem exists_orthogonal_pair (hnd : b.Nondegenerate) [Finite E]
    (hE : 4 < Nat.card E) : ∃ v w : E, v ≠ 0 ∧ w ≠ 0 ∧ w ≠ v ∧ b v w = 0 := by
  have : Fintype E := Fintype.ofFinite E
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨u, hu⟩ := exists_apply_eq_one hnd hv
  have hE' : Fintype.card (ZMod 2 × ZMod 2) < Fintype.card E :=
    calc Fintype.card (ZMod 2 × ZMod 2) = 4 := rfl
      _ < Nat.card E := hE
      _ = Fintype.card E := Nat.card_eq_fintype_card
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : E => (b v x, b u x)) hE'
  simp only [Prod.mk.injEq] at hf
  refine ⟨v, x - y, hv, sub_ne_zero.mpr hxy, fun h => ?_, by rw [map_sub, hf.1, sub_self]⟩
  have h1 : b u (x - y) = 0 := by rw [map_sub, hf.2, sub_self]
  rw [h, hu] at h1
  exact absurd h1 (by decide)

theorem not_invariant_of_polar_eq (hb : b.IsAlt) (hnd : b.Nondegenerate) [Finite E]
    (hE : 4 < Nat.card E) (f : E → ZMod 2) (hf : ∀ x y, f (x + y) = f x + f y + b x y)
    (hfS : ∀ (s : bilinIsometryGroup b) x, f (sE s x) = f x) : False := by
  have hone : ∀ u, u ≠ 0 → f u = 1 := by
    intro u hu
    obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hu
    have h := hfS (tau hb u) x
    rw [sE_tau, hx, one_smul, hf, hx] at h
    generalize f x = p at h
    generalize f u = c at h ⊢
    revert p c
    decide
  obtain ⟨v, w, hv, hw, hwv, hvw⟩ := exists_orthogonal_pair hnd hE
  have h := hf v w
  rw [hone v hv, hone w hw, hvw, hone (v + w) fun h => hwv (eq_of_add_eq_zero_zmod2 h).symm] at h
  exact absurd h (by decide)

section Quadratic

variable {Q : QuadraticForm (ZMod 2) E}

theorem eq_zero_of_invariant_linear_V (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) [Finite E] (hE : 4 < Nat.card E)
    (ℓ : (E × ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hℓ : ∀ (s : bilinIsometryGroup b) w t, ℓ (sE s w, t + Q w + Q (sE s w)) = ℓ (w, t))
    (v : E × ZMod 2) : ℓ v = 0 := by
  have hdec : ∀ w t, ℓ (w, t) = ℓ (w, 0) + t * ℓ rV := fun w t => by
    rw [← smul_eq_mul, ← map_smul, ← map_add, rV, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
      Prod.mk_add_mk, add_zero, zero_add]
  have hrel : ∀ (s : bilinIsometryGroup b) w,
      ℓ (sE s w, 0) + (Q w + Q (sE s w)) * ℓ rV = ℓ (w, 0) := fun s w => by
    rw [← hdec, ← hℓ s w 0, zero_add]
  rcases zmod_two_cases (ℓ rV) with h0 | h1
  ·
    have hE0 := eq_zero_of_invariant_linear hb hnd (ℓ.comp (LinearMap.inl (ZMod 2) E (ZMod 2)))
      (fun s w => by
        have h := hrel s w
        rwa [h0, mul_zero, add_zero] at h)
    rw [← Prod.mk.eta (p := v), hdec, h0, mul_zero, add_zero]
    exact hE0 v.1
  ·
    exfalso
    refine not_invariant_of_polar_eq hb hnd hE (fun w => Q w + ℓ (w, 0)) (fun x y => ?_)
      (fun s w => ?_)
    · rw [Q_add hQ, show ((x + y, 0) : E × ZMod 2) = (x, 0) + (y, 0) by simp, map_add]
      ring
    · have h := hrel s w
      rw [h1, mul_one] at h
      rw [← h]
      generalize Q w = p₁
      generalize Q (sE s w) = p₂
      generalize ℓ (sE s w, 0) = p₃
      revert p₁ p₂ p₃
      decide

theorem exists_eq_mul_qV_of_invariant (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) [Finite E] (hE : 4 < Nat.card E)
    {f : E × ZMod 2 → ZMod 2} (p : LinearMap.BilinForm (ZMod 2) (E × ZMod 2))
    (hf : ∀ v w, f (v + w) = f v + f w + p v w)
    (hfS : ∀ (s : bilinIsometryGroup b) w t, f (sE s w, t + Q w + Q (sE s w)) = f (w, t)) :
    ∃ β : ZMod 2, ∀ v, f v = β * qV Q v := by
  set h : bilinIsometryGroup b → E × ZMod 2 → E × ZMod 2 :=
    fun s v => (sE s v.1, v.2 + Q v.1 + Q (sE s v.1)) with hh
  have hfS' : ∀ s v, f (h s v) = f v := fun s v => hfS s v.1 v.2
  have hadd : ∀ s v w, h s (v + w) = h s v + h s w := fun s v w =>
    map_add (hLin hQ (sE s) (b_sE s)) v w
  have hr : ∀ s, h s rV = rV := fun s => by
    simp only [hh, rV, map_zero, add_zero]
  have hpol : ∀ v w, p v w = f (v + w) + f v + f w := fun v w => by
    rw [hf]
    generalize f v = a₁
    generalize f w = a₂
    generalize p v w = a₃
    revert a₁ a₂ a₃
    decide
  have hpS : ∀ s v w, p (h s v) (h s w) = p v w := fun s v w => by
    rw [hpol, hpol, ← hadd, hfS', hfS', hfS']
  have hfix : ∀ s w t, h s (w, t) = (sE s w, t + Q w + Q (sE s w)) := fun _ _ _ => rfl
  have hpr : ∀ v, p rV v = 0 := eq_zero_of_invariant_linear_V hb hnd hQ hE (p rV)
    (fun s w t => by
      have h1 := hpS s rV (w, t)
      rwa [hr] at h1)
  have hpr' : ∀ v, p v rV = 0 := eq_zero_of_invariant_linear_V hb hnd hQ hE
    (LinearMap.BilinForm.flip p rV)
    (fun s w t => by
      have h1 := hpS s (w, t) rV
      rw [hr] at h1
      rwa [LinearMap.BilinForm.flip_apply, LinearMap.BilinForm.flip_apply])
  have hdec : ∀ v : E × ZMod 2, v = (v.1, 0) + v.2 • rV := fun v => by
    simp only [rV, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero,
      zero_add]
  have hpE : ∀ v w, p v w = p (v.1, 0) (w.1, 0) := fun v w => by
    conv_lhs => rw [hdec v, hdec w]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpr, hpr',
      smul_zero, add_zero]
  obtain ⟨c, hc⟩ := exists_eq_mul_of_invariant_bilin hb hnd
    (p.compl₁₂ (LinearMap.inl (ZMod 2) E (ZMod 2)) (LinearMap.inl (ZMod 2) E (ZMod 2)))
    (fun s x y => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.inl_apply]
      rw [← hpS s (x, 0) (y, 0), hpE (h s (x, 0)) (h s (y, 0))])
  have hpc : ∀ v w, p v w = c * b v.1 w.1 := fun v w => by
    rw [hpE, ← hc]
    rfl
  have hq : ∀ v w, qV Q (v + w) = qV Q v + qV Q w + b v.1 w.1 := fun v w => by
    simp only [qV, Prod.fst_add, Prod.snd_add, Q_add hQ]
    ring
  have key : ∀ a₁ a₂ a₃ a₄ a₅ c : ZMod 2,
      a₁ + a₂ + c * a₅ + c * (a₃ + a₄ + a₅) = a₁ + c * a₃ + (a₂ + c * a₄) := by decide
  let g : (E × ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun v => f v + c * qV Q v) fun v w => by
    rw [hf, hq, hpc]
    exact key _ _ _ _ _ _
  have hg := eq_zero_of_invariant_linear_V hb hnd hQ hE (g.toZModLinearMap 2) (fun s w t => by
    change f (h s (w, t)) + c * qV Q (h s (w, t)) = f (w, t) + c * qV Q (w, t)
    rw [hfS', hfix, qV, qV]
    simp only
    congr 1
    have key2 : ∀ c t p₁ p₂ : ZMod 2, c * (p₂ + (t + p₁ + p₂)) = c * (p₁ + t) := by decide
    exact key2 c t _ _)
  refine ⟨c, fun v => ?_⟩
  have := hg v
  change f v + c * qV Q v = 0 at this
  exact eq_of_add_eq_zero_zmod2 this

end Quadratic

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
