module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11a

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

section
variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G}

theorem fzFus_commute_of_mem_ctxW (hc : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  have := hc.abelian_W.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem fzFus_rels (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    t ^ 2 = 1 ∧ t * x₁ = x₁ * t ∧ t * x₂ = x₂ * t ∧ x₁ * x₂ = x₂ * x₁ := by
  have hc := h.ctx
  have htW : t ∈ ctxW t x₁ x₂ := mem_sup_left hc.hyp.mem_twoCore
  have hx₁W : x₁ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  have hx₂W : x₂ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  exact ⟨by rw [← hc.hyp.ord_t]; exact pow_orderOf_eq_one t,
    fzFus_commute_of_mem_ctxW hc htW hx₁W, fzFus_commute_of_mem_ctxW hc htW hx₂W,
    fzFus_commute_of_mem_ctxW hc hx₁W hx₂W⟩

omit [Finite G] in
theorem fzFus_t_eq_prod {t x₁ x₂ : G} (ht2 : t * t = 1) (h2 : t * x₂ = x₂ * t) :
    t = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := by
  calc t = x₁ * x₂ * (t * t) * (x₁ * x₂)⁻¹ * t := by rw [ht2]; group
    _ = x₁ * (x₂ * t) * t * (x₁ * x₂)⁻¹ * t := by group
    _ = x₁ * (t * x₂) * t * (x₁ * x₂)⁻¹ * t := by rw [h2]
    _ = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := by group

theorem a32_conj_t (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    a₃₂ * t * a₃₂⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hc := h.ctx
  have htW : t ∈ ctxW t x₁ x₂ := mem_sup_left hc.hyp.mem_twoCore
  have hx₁W : x₁ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  have hx₂W : x₂ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
  have h1 : t * x₁ = x₁ * t := fzFus_commute_of_mem_ctxW hc htW hx₁W
  have h2 : t * x₂ = x₂ * t := fzFus_commute_of_mem_ctxW hc htW hx₂W
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t; rw [hc.hyp.ord_t, pow_two] at this; exact this
  obtain ⟨-, -, hq3, -⟩ := h.shape.quat₃
  have hc1 : Commute a₃₂ (x₁ * t) := (h.shape.comm₁₃ _ (by simp) _ (by simp)).symm
  have hc2 : Commute a₃₂ (x₂ * t) := (h.shape.comm₂₃ _ (by simp) _ (by simp)).symm
  have htc : t = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := by
    calc t = x₁ * x₂ * (t * t) * (x₁ * x₂)⁻¹ * t := by rw [ht2]; group
      _ = x₁ * (x₂ * t) * t * (x₁ * x₂)⁻¹ * t := by group
      _ = x₁ * (t * x₂) * t * (x₁ * x₂)⁻¹ * t := by rw [h2]
      _ = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) := by group
  have key : a₃₂ * t * a₃₂⁻¹ = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t)⁻¹ := by
    calc a₃₂ * t * a₃₂⁻¹ = a₃₂ * ((x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t)) * a₃₂⁻¹ := by
          rw [← htc]
      _ = (a₃₂ * (x₁ * t)) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t) * a₃₂⁻¹ := by group
      _ = (x₁ * t) * (a₃₂ * (x₂ * t)) * ((x₁ * x₂)⁻¹ * t) * a₃₂⁻¹ := by rw [hc1.eq]; group
      _ = (x₁ * t) * (x₂ * t) * (a₃₂ * ((x₁ * x₂)⁻¹ * t) * a₃₂⁻¹) := by rw [hc2.eq]; group
      _ = (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t)⁻¹ := by rw [hq3]
  rw [key]
  calc (x₁ * t) * (x₂ * t) * ((x₁ * x₂)⁻¹ * t)⁻¹ = (x₁ * t) * x₂ * x₁ * x₂ := by group
    _ = (t * x₁) * x₂ * x₁ * x₂ := by rw [h1]
    _ = t * (x₁ * x₂) ^ 2 := by rw [pow_two]; group

theorem fzFus_isConj_t_tz (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) :
    IsConj t (t * (x₁ * x₂) ^ 2) :=
  isConj_iff.mpr ⟨a₃₂, a32_conj_t h⟩

theorem fzFus_eq_one_or_eq_t_of_mem (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂) {p : G}
    (hp : p ∈ twoCore t) : p = 1 ∨ p = t := by
  apply h.ctx.hyp.eq_one_or_eq p hp
  have := pow_card_eq_one' (G := ↥(twoCore t)) (x := ⟨p, hp⟩)
  rw [h.card_twoCore] at this
  simpa using congrArg Subtype.val this

omit [Finite G] in
theorem fzFus_conj_of_eq {a b g : G} (hab : g * a * g⁻¹ = b) : IsConj a b :=
  isConj_iff.mpr ⟨g, hab⟩

theorem fzProdLemma :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S T₂ : Subgroup G)
      (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
      FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
      ∀ e u : G, IsConj t e → u * e = e * u → u ^ 2 = 1 → u ≠ 1 → u ≠ e →
        (IsConj ((x₁ * x₂) ^ 2) u ∧ IsConj t (u * e)) ∨
        (IsConj t u ∧ IsConj ((x₁ * x₂) ^ 2) (u * e)) ∨
        (IsConj tau u ∧ IsConj (t * tau) (u * e)) ∨
        (IsConj (t * tau) u ∧ IsConj tau (u * e)) := by
  intro G _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ h e u he hue hu2 hu1 hne
  obtain ⟨g, rfl⟩ := isConj_iff.mp he
  have hcomm : ∀ k ∈ invCent t, k * t = t * k := fun k hk =>
    ((mem_centralizer_iff.mp hk) t (Set.mem_singleton t)).symm
  set v := g⁻¹ * u * g with hv
  have hu : u = g * v * g⁻¹ := by rw [hv]; group
  have hvt : v * t = t * v := by
    have : g⁻¹ * (u * (g * t * g⁻¹)) * g = g⁻¹ * ((g * t * g⁻¹) * u) * g := by rw [hue]
    calc v * t = g⁻¹ * (u * (g * t * g⁻¹)) * g := by rw [hv]; group
      _ = g⁻¹ * ((g * t * g⁻¹) * u) * g := this
      _ = t * v := by rw [hv]; group
  have hvH : v ∈ invCent t := mem_centralizer_iff.mpr (fun k hk => by
    rw [Set.mem_singleton_iff.mp hk]; exact hvt.symm)
  have huu : u * u = 1 := by rw [← pow_two]; exact hu2
  have hv2 : v * v = 1 := by
    rw [hv]; calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [huu]; group
  have hv1 : v ≠ 1 := by intro h1; apply hu1; rw [hu, h1]; group
  have hvt' : v ≠ t := by intro h1; apply hne; rw [hu, h1]
  have hprod : u * (g * t * g⁻¹) = g * (v * t) * g⁻¹ := by rw [hu]; group
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t; rw [h.ctx.hyp.ord_t, pow_two] at this; exact this
  have htau : tau * t = t * tau := hcomm tau (h.ctx.le_invCent h.ctx.tau_mem)
  have cu : ∀ {X : G}, IsConj X v → IsConj X u := fun hX =>
    hX.trans (fzFus_conj_of_eq (g := g) (by rw [hu]))
  have cue : ∀ {X : G}, IsConj X (v * t) → IsConj X (u * (g * t * g⁻¹)) := fun hX =>
    hX.trans (fzFus_conj_of_eq (g := g) hprod.symm)
  have hzt : (x₁ * x₂) ^ 2 * t = t * (x₁ * x₂) ^ 2 := by
    have hx₁W : x₁ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
    have hx₂W : x₂ ∈ ctxW t x₁ x₂ := mem_sup_right (subset_closure (by simp))
    exact fzFus_commute_of_mem_ctxW h.ctx (pow_mem (mul_mem hx₁W hx₂W) 2)
      (mem_sup_left h.ctx.hyp.mem_twoCore)
  by_cases hPL : v ∈ twoCore t ⊔ L
  · obtain ⟨k, hk, hcase⟩ := h.ctx.invol_PL v hPL hv2 hv1
    have hkt := hcomm k hk
    have hkt' : k⁻¹ * t * k = t := by rw [mul_assoc, ← hkt]; group
    rcases hcase with h1 | h1 | h1
    · exfalso; apply hvt'
      calc v = k⁻¹ * (k * v * k⁻¹) * k := by group
        _ = k⁻¹ * t * k := by rw [h1]
        _ = t := hkt'
    · left
      refine ⟨cu (fzFus_conj_of_eq (g := k⁻¹) (by rw [← h1]; group)), cue ?_⟩
      have hv' : v = k⁻¹ * (x₁ * x₂) ^ 2 * k := by rw [← h1]; group
      refine (fzFus_isConj_t_tz h).trans (fzFus_conj_of_eq (g := k⁻¹) ?_)
      rw [hv']
      calc k⁻¹ * (t * (x₁ * x₂) ^ 2) * k⁻¹⁻¹ = k⁻¹ * ((x₁ * x₂) ^ 2 * t) * k := by
            rw [hzt]; group
        _ = k⁻¹ * (x₁ * x₂) ^ 2 * (t * k) := by group
        _ = k⁻¹ * (x₁ * x₂) ^ 2 * k * t := by rw [← hkt]; group
    · right; left
      refine ⟨(fzFus_isConj_t_tz h).trans
        (cu (fzFus_conj_of_eq (g := k⁻¹) (by rw [← h1]; group))), cue ?_⟩
      refine fzFus_conj_of_eq (g := k⁻¹) ?_
      have hv' : v = k⁻¹ * (t * (x₁ * x₂) ^ 2) * k := by rw [← h1]; group
      rw [hv']
      calc k⁻¹ * (x₁ * x₂) ^ 2 * k⁻¹⁻¹ = k⁻¹ * ((t * t) * (x₁ * x₂) ^ 2) * k := by rw [ht2]; group
        _ = k⁻¹ * (t * ((x₁ * x₂) ^ 2 * t)) * k := by rw [hzt]; group
        _ = k⁻¹ * (t * (x₁ * x₂) ^ 2) * (t * k) := by group
        _ = k⁻¹ * (t * (x₁ * x₂) ^ 2) * k * t := by rw [← hkt]; group
  · obtain ⟨k, hk, p, hp, h1⟩ := h.ctx.invol_outer v hvH hPL (by rw [pow_two, hv2]; exact one_mem _)
    have hkt := hcomm k hk
    have hvk : v = k⁻¹ * (p * tau) * k := by rw [← h1]; group
    have hvtk : v * t = k⁻¹ * (p * tau * t) * k := by
      rw [hvk]; calc k⁻¹ * (p * tau) * k * t = k⁻¹ * (p * tau) * (k * t) := by group
        _ = k⁻¹ * (p * tau) * (t * k) := by rw [hkt]
        _ = k⁻¹ * (p * tau * t) * k := by group
    rcases fzFus_eq_one_or_eq_t_of_mem h hp with hp1 | hp1
    · rw [hp1, one_mul] at hvk hvtk
      right; right; left
      refine ⟨cu (fzFus_conj_of_eq (g := k⁻¹) (by rw [hvk]; group)),
        cue (fzFus_conj_of_eq (g := k⁻¹) ?_)⟩
      rw [hvtk, htau]; group
    · rw [hp1] at hvk hvtk
      right; right; right
      refine ⟨cu (fzFus_conj_of_eq (g := k⁻¹) (by rw [hvk]; group)),
        cue (fzFus_conj_of_eq (g := k⁻¹) ?_)⟩
      have htt : t * tau * t = tau := by
        calc t * tau * t = t * (tau * t) := by group
          _ = t * (t * tau) := by rw [htau]
          _ = (t * t) * tau := by group
          _ = tau := by rw [ht2]; group
      rw [hvtk, htt]; group

end

end CFSG.OddStandard.SmallF3.FritzII
