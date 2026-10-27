module

public import CFSG.GH74.GLS.IVK.L2.Lemma13c
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.GH74.GLS.IVK

open CFSG.ABGLocalTools

section FFNorm

variable {F : Type*} [Field F] [Finite F]

theorem finite_ringEquiv (F : Type*) [Field F] [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) (fun _ _ h => RingEquiv.ext (congrFun h))

theorem prod_pow_fixed (σ : F ≃+* F) (w : F) :
    σ (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) w) = ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) w := by
  have := finite_ringEquiv F
  have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
  rw [map_prod]
  have h1 : ∏ i ∈ Finset.range (orderOf σ), σ ((σ ^ i) w) =
      ∏ i ∈ Finset.range (orderOf σ), (σ ^ (i + 1)) w := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [pow_succ', RingAut.mul_apply]
  rw [h1]
  by_cases hw : w = 0
  · subst hw
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm]
    simp
  · have h2 := Finset.prod_range_succ (fun i => (σ ^ i) w) (orderOf σ)
    have h3 := Finset.prod_range_succ' (fun i => (σ ^ i) w) (orderOf σ)
    rw [h2] at h3
    have h4 : (σ ^ orderOf σ) w = w := by rw [pow_orderOf_eq_one]; rfl
    rw [h4] at h3
    simp only [pow_zero] at h3
    have h5 : (1 : F ≃+* F) w = w := rfl
    rw [h5] at h3
    exact (mul_right_cancel₀ hw h3).symm

theorem isSquare_of_prod_fixed_sq (hodd : (2 : F) ≠ 0) (σ : F ≃+* F) {d μ : F} (hd : d ≠ 0)
    (hμ : σ μ = μ) (h : μ ^ 2 = ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) d) : IsSquare d := by
  classical
  have := finite_ringEquiv F
  have : Fintype F := Fintype.ofFinite F
  by_contra hns
  let H : Subgroup (F ≃+* F) := Subgroup.zpowers σ
  let F₀ := FixedPoints.subfield H F
  have hfix : ∀ ρ : F, σ ρ = ρ → ρ ∈ F₀ := by
    intro ρ hρ
    have hstab : H ≤ MulAction.stabilizer (F ≃+* F) ρ := by
      rw [Subgroup.zpowers_le]
      exact hρ
    intro h'
    exact hstab h'.property
  have hch : ringChar F₀ ≠ 2 := by
    intro h2
    have hc : CharP F₀ 2 := h2 ▸ ringChar.charP F₀
    have h20 : (2 : F₀) = 0 := by exact_mod_cast CharP.cast_eq_zero F₀ 2
    have h3 : F₀.subtype (2 : F₀) = F₀.subtype 0 := by rw [h20]
    rw [map_ofNat, map_zero] at h3
    exact hodd h3
  obtain ⟨c₀, hc₀⟩ := FiniteField.exists_nonsquare hch
  set c : F := (c₀ : F) with hcdef
  have hc : σ c = c := c₀.2 ⟨σ, Subgroup.mem_zpowers σ⟩
  have hc0 : c ≠ 0 := by
    intro h0
    apply hc₀
    have : c₀ = 0 := Subtype.ext h0
    rw [this]
    exact IsSquare.zero
  obtain ⟨e, he⟩ := exists_prod_pow_eq σ hc
  have he0 : e ≠ 0 := by
    rintro rfl
    have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
    apply hc0
    rw [← he]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hm, Finset.prod_range_succ]
    simp
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have hpos : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
    have : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) d ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ h0 =>
        hd ((map_eq_zero_iff (σ ^ i) (σ ^ i).injective).1 h0))
    apply this
    rw [← h]
    simp
  have key : ∀ ρ : F, σ ρ = ρ → ρ ^ 2 = c → False := by
    intro ρ hρ hρc
    apply hc₀
    refine ⟨⟨ρ, hfix ρ hρ⟩, Subtype.ext ?_⟩
    simpa [sq] using hρc.symm
  have hprodsq : ∀ w : F, ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (w * w) =
      (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) w) ^ 2 := by
    intro w
    rw [sq, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_mul])
  have hprodmul : ∀ a b : F, ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (a * b) =
      (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) a) * ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) b := by
    intro a b
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_mul])
  by_cases hes : IsSquare e
  · obtain ⟨w, hw⟩ := hes
    refine key _ (prod_pow_fixed σ w) ?_
    rw [← he, hw, hprodsq]
  · obtain ⟨w, hw⟩ := isSquare_mul_of_not_isSquare hns hes
    refine key ((∏ i ∈ Finset.range (orderOf σ), (σ ^ i) w) * μ⁻¹) ?_ ?_
    · rw [map_mul, prod_pow_fixed σ w, map_inv₀, hμ]
    · have h1 := hprodsq w
      rw [← hw, hprodmul, ← h, he] at h1
      rw [mul_pow, inv_pow, ← h1]
      field_simp

end FFNorm

end CFSG.GH74.GLS.IVK
