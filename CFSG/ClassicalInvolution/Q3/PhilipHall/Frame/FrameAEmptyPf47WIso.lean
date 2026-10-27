module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WIsoMat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf


theorem w_iso_of_shape {X : Type} [Group X] [Finite X] {W : Subgroup X} [W.Normal]
    (hW : Nonempty (↥W ≃* Multiplicative (ZMod 4 × ZMod 4)))
    (hC : Subgroup.centralizer (W : Set X) = W) (hD : Nonempty ((X ⧸ W) ≃* DihedralGroup 6)) :
    Nonempty (X ≃* G192) := by
  obtain ⟨e⟩ := hW
  obtain ⟨q⟩ := hD
  have hWn : W.Normal := inferInstance
  have hWcard : Nat.card W = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hXcard : Nat.card X = 192 := by
    rw [W.card_eq_card_quotient_mul_card_subgroup, Nat.card_congr q.toEquiv, DihedralGroup.nat_card, hWcard]
  let κ : X →* MulAut (Multiplicative (ZMod 4 × ZMod 4)) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have hκ : ∀ (x : X) (v), ((e.symm (κ x v) : W) : X) = x * (e.symm v : X) * x⁻¹ := by
    intro x v
    change ((e.symm (e (MulAut.conjNormal x (e.symm v))) : W) : X) = _
    rw [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]
  have hκW : ∀ x, κ x = 1 → x ∈ W := by
    intro x hx
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro w hw
    have h := hκ x (e ⟨w, hw⟩)
    rw [hx, MulAut.one_apply, MulEquiv.symm_apply_apply] at h
    change w = x * w * x⁻¹ at h
    calc w * x = x * w * x⁻¹ * x := by rw [← h]
      _ = x * w := by group
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hXcard]; norm_num)
  have hg3 : g ^ 3 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hgW : g ∉ W := by
    intro h
    have := W.orderOf_dvd_natCard h
    rw [hg, hWcard] at this
    norm_num at this
  have hfpf : ∀ w ∈ W, w * g = g * w → w = 1 := by
    intro w hw hwg
    have h3 : κ g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    have h1 : κ g ≠ 1 := fun h => hgW (hκW g h)
    have hfix : κ g (e ⟨w, hw⟩) = e ⟨w, hw⟩ := by
      apply e.symm.injective
      apply Subtype.ext
      rw [hκ, MulEquiv.symm_apply_apply]
      change g * w * g⁻¹ = w
      rw [← hwg, mul_inv_cancel_right]
    have h := WIso.mulAut_three_fpf h3 h1 hfix
    rw [MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  have hcm : ∀ w ∈ W, w * g * w⁻¹ * g⁻¹ ∈ W := by
    intro w hw
    simpa only [mul_assoc] using W.mul_mem hw (hWn.conj_mem _ (W.inv_mem hw) g)
  let φ : W → W := fun w => ⟨w * g * (w : X)⁻¹ * g⁻¹, hcm w w.2⟩
  have hφ : Function.Surjective φ := by
    refine Finite.injective_iff_surjective.mp fun a b hab => ?_
    have h : (a : X) * g * (a : X)⁻¹ * g⁻¹ = b * g * (b : X)⁻¹ * g⁻¹ := congrArg Subtype.val hab
    have hc : (b : X)⁻¹ * a * g = g * ((b : X)⁻¹ * a) := by
      calc (b : X)⁻¹ * a * g = (b : X)⁻¹ * ((a : X) * g * (a : X)⁻¹ * g⁻¹) * g * a := by group
        _ = (b : X)⁻¹ * ((b : X) * g * (b : X)⁻¹ * g⁻¹) * g * a := by rw [h]
        _ = g * ((b : X)⁻¹ * a) := by group
    exact Subtype.ext (inv_mul_eq_one.mp (hfpf _ (W.mul_mem (W.inv_mem b.2) a.2) hc)).symm
  have hconj : ∀ x : X, x * g * x⁻¹ * g⁻¹ ∈ W ∨ x * g⁻¹ * x⁻¹ * g⁻¹ ∈ W := by
    intro x
    have ha3 : q (g : X ⧸ W) ^ 3 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hg3, QuotientGroup.mk_one, map_one]
    have ha1 : q (g : X ⧸ W) ≠ 1 := by
      rw [Ne, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      exact hgW
    have key : ∀ y a : DihedralGroup 6, y * a * y⁻¹ = a⁻¹ → y * a⁻¹ * y⁻¹ * a⁻¹ = 1 := by
      decide
    rcases WIso.d12_conj _ (q (x : X ⧸ W)) ha3 ha1 with h | h
    · left
      rw [← QuotientGroup.eq_one_iff, ← MulEquiv.map_eq_one_iff q]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, h, mul_inv_cancel]
    · right
      rw [← QuotientGroup.eq_one_iff, ← MulEquiv.map_eq_one_iff q]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
      exact key _ _ h
  let N : Subgroup X :=
    { carrier := {x | x * g * x⁻¹ = g ∨ x * g * x⁻¹ = g⁻¹}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [show a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ by group]
        rcases hb with hb | hb <;> rw [hb]
        · exact ha
        · rw [show a * g⁻¹ * a⁻¹ = (a * g * a⁻¹)⁻¹ by group]
          rcases ha with ha | ha <;> rw [ha]
          · exact Or.inr rfl
          · exact Or.inl (inv_inv g)
      one_mem' := by
        simp only [Set.mem_setOf_eq, one_mul, inv_one, mul_one, true_or]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, inv_inv] at ha ⊢
        rcases ha with ha | ha
        · left
          calc a⁻¹ * g * a = a⁻¹ * (a * g * a⁻¹) * a := by rw [ha]
            _ = g := by group
        · right
          calc a⁻¹ * g * a = a⁻¹ * (g⁻¹)⁻¹ * a := by rw [inv_inv]
            _ = a⁻¹ * (a * g * a⁻¹)⁻¹ * a := by rw [ha]
            _ = g⁻¹ := by group }
  have hNW : ∀ x ∈ N, x ∈ W → x = 1 := by
    intro x hxN hxW
    rcases hxN with h | h
    · refine hfpf x hxW ?_
      calc x * g = x * g * x⁻¹ * x := by group
        _ = g * x := by rw [h]
    · refine absurd ?_ hgW
      have h2 : g⁻¹ * g⁻¹ ∈ W := by
        have := hcm x hxW
        rwa [h] at this
      have hg4 : g = (g⁻¹ * g⁻¹)⁻¹ * (g⁻¹ * g⁻¹)⁻¹ := by
        calc g = g ^ 3 * g := by rw [hg3, one_mul]
          _ = (g⁻¹ * g⁻¹)⁻¹ * (g⁻¹ * g⁻¹)⁻¹ := by group
      rw [hg4]
      exact W.mul_mem (W.inv_mem h2) (W.inv_mem h2)
  have hNs : ∀ x : X, ∃ y ∈ N, x⁻¹ * y ∈ W := by
    intro x
    have hmem : ∀ w ∈ W, x⁻¹ * (w⁻¹ * x) ∈ W := fun w hw => by
      simpa only [mul_assoc, inv_inv] using hWn.conj_mem _ (W.inv_mem hw) x⁻¹
    rcases hconj x with h | h
    · obtain ⟨w, hw⟩ := hφ ⟨_, h⟩
      have hw0 : (w : X) * g * (w : X)⁻¹ * g⁻¹ = x * g * x⁻¹ * g⁻¹ := congrArg Subtype.val hw
      have hw' : (w : X) * g * (w : X)⁻¹ = x * g * x⁻¹ := mul_right_cancel hw0
      refine ⟨(w : X)⁻¹ * x, Or.inl ?_, hmem w w.2⟩
      calc (w : X)⁻¹ * x * g * ((w : X)⁻¹ * x)⁻¹ = (w : X)⁻¹ * (x * g * x⁻¹) * w := by group
        _ = (w : X)⁻¹ * ((w : X) * g * (w : X)⁻¹) * w := by rw [hw']
        _ = g := by group
    · obtain ⟨w, hw⟩ := hφ ⟨_, h⟩
      have hw0 : (w : X) * g * (w : X)⁻¹ * g⁻¹ = x * g⁻¹ * x⁻¹ * g⁻¹ := congrArg Subtype.val hw
      have hw' : (w : X) * g * (w : X)⁻¹ = x * g⁻¹ * x⁻¹ := mul_right_cancel hw0
      refine ⟨(w : X)⁻¹ * x, Or.inr ?_, hmem w w.2⟩
      calc (w : X)⁻¹ * x * g * ((w : X)⁻¹ * x)⁻¹ = ((w : X)⁻¹ * (x * g⁻¹ * x⁻¹) * w)⁻¹ := by group
        _ = ((w : X)⁻¹ * ((w : X) * g * (w : X)⁻¹) * w)⁻¹ := by rw [hw']
        _ = g⁻¹ := by group
  let πN : N →* X ⧸ W := (QuotientGroup.mk' W).comp N.subtype
  have hπN : Function.Bijective πN := by
    refine ⟨(injective_iff_map_eq_one πN).mpr fun y hy =>
      Subtype.ext (hNW y y.2 ((QuotientGroup.eq_one_iff _).mp hy)), fun z => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨y, hyN, hy⟩ := hNs x
    exact ⟨⟨y, hyN⟩, (QuotientGroup.eq.mpr hy).symm⟩
  let τ : N ≃* X ⧸ W := MulEquiv.ofBijective πN hπN
  let σ : DihedralGroup 6 →* X := N.subtype.comp (τ.symm.toMonoidHom.comp q.symm.toMonoidHom)
  have hσ : ∀ d, ((σ d : X) : X ⧸ W) = q.symm d := fun d => τ.apply_symm_apply (q.symm d)
  have hψ : Function.Injective (κ.comp σ) := by
    refine (injective_iff_map_eq_one _).mpr fun d hd => ?_
    have h1 : ((σ d : X) : X ⧸ W) = 1 := (QuotientGroup.eq_one_iff _).mpr (hκW _ hd)
    rwa [hσ, MulEquiv.map_eq_one_iff] at h1
  obtain ⟨Q, β, hQ⟩ := WIso.rep_conj (κ.comp σ) hψ
  let f₁ : Multiplicative (ZMod 4 × ZMod 4) →* X := W.subtype.comp (e.symm.toMonoidHom.comp Q.toMonoidHom)
  let f₂ : DihedralGroup 6 →* X := σ.comp β
  have hf : ∀ d v, f₁ (W192.act d v) = f₂ d * f₁ v * (f₂ d)⁻¹ := by
    intro d v
    have h := DFunLike.congr_fun (hQ d) v
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    change ((e.symm (Q (W192.act d v)) : W) : X) = σ (β d) * (e.symm (Q v) : X) * (σ (β d))⁻¹
    rw [h]
    exact hκ (σ (β d)) (Q v)
  let Φ : G192 →* X := SemidirectProduct.lift f₁ f₂ fun d => MonoidHom.ext fun v => hf d v
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have h : (⟨a, ha⟩ * ⟨b, hb⟩ : W) = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hf₁W : ∀ v, f₁ v ∈ W := fun v => (e.symm (Q v)).2
  have hf₁ : Function.Injective f₁ := fun a b h => Q.injective (e.symm.injective (Subtype.ext h))
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_one Φ).mpr fun x hx => ?_
    have hx' : f₁ x.left * f₂ x.right = 1 := hx
    have h2 : f₂ x.right ∈ W := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact W.inv_mem (hf₁W _)
    have hr : x.right = 1 := WIso.act_faithful _ fun v => hf₁ (by
      rw [hf, hWc _ h2 _ (hf₁W v), mul_inv_cancel_right])
    have hl : x.left = 1 := by
      rw [hr, map_one, mul_one] at hx'
      exact hf₁ (hx'.trans (map_one f₁).symm)
    exact SemidirectProduct.ext hl hr
  exact ⟨(MulEquiv.ofBijective Φ (hΦ.bijective_of_nat_card_le (by rw [hXcard, W192.w192_card]))).symm⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
