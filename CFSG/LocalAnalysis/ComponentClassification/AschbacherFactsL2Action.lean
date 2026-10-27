module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPSL2ToPGammaL2Apply
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter

theorem field_involution_commuting_pair {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (x : PGammaL2 K)
    (hx : x ^ 2 = 1) (hfield : x.right ≠ 1) :
    ∃ u w : PSL2 K, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      x * SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL u) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL u) * x ∧
      x * SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL w) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL w) * x := by
  classical
  let ι : PSL2 K →* PGammaL2 K :=
    (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K))
  have hι : Function.Injective ι := fun a b h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (SemidirectProduct.inl_injective h)
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hfield rfl
  have hxord : orderOf x = 2 := orderOf_eq_prime hx hx1
  obtain ⟨C, hC⟩ := projective_semilinear_involution_conj_inr hK x hxord hfield
  set σ := x.right with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right hx
    simpa [pow_two] using h
  obtain ⟨a, b, ha1, hb1, hab, ha, hb, hcomm, haPSL, hbPSL, hpa, hpb⟩ :=
    pure_field_involution_fixed_psl_generators hK σ hσ2 hfield
  let c : PGammaL2 K := SemidirectProduct.inl C
  have hxc : x = c * SemidirectProduct.inr σ * c⁻¹ := by
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * SemidirectProduct.inr σ * c⁻¹ := by rw [hC]
  have hnorm := pGammaL2PSLRange_normal K hK hcard
  have hmem : ∀ v : PGL2 K, SemidirectProduct.inl v ∈ pGammaL2PSLRange K →
      ∃ y : PSL2 K, ι y = c * SemidirectProduct.inl v * c⁻¹ := by
    intro v hv
    exact (mem_pGammaL2PSLRange_iff K _).mp (hnorm.conj_mem _ hv c)
  obtain ⟨u, hu⟩ := hmem a haPSL
  obtain ⟨w, hw⟩ := hmem b hbPSL
  have hconj_sq : ∀ v : PGL2 K, v * v = 1 →
      (c * SemidirectProduct.inl v * c⁻¹) ^ 2 = (1 : PGammaL2 K) := by
    intro v hv
    rw [pow_two, show c * SemidirectProduct.inl v * c⁻¹ * (c * SemidirectProduct.inl v * c⁻¹) =
      c * SemidirectProduct.inl (v * v) * c⁻¹ by rw [map_mul]; group, hv, map_one]
    group
  have hconj_ne : ∀ v : PGL2 K, v ≠ 1 → c * SemidirectProduct.inl v * c⁻¹ ≠ 1 := by
    intro v hv h
    apply hv
    have : (SemidirectProduct.inl v : PGammaL2 K) = 1 := by
      calc (SemidirectProduct.inl v : PGammaL2 K) = c⁻¹ * (c * SemidirectProduct.inl v * c⁻¹) * c
          := by group
        _ = 1 := by rw [h]; group
    exact SemidirectProduct.inl_injective (this.trans (map_one _).symm)
  have hcomm_x : ∀ v : PGL2 K, Commute (SemidirectProduct.inr σ : PGammaL2 K)
      (SemidirectProduct.inl v) →
      x * (c * SemidirectProduct.inl v * c⁻¹) = (c * SemidirectProduct.inl v * c⁻¹) * x := by
    intro v hv
    rw [hxc]
    calc c * SemidirectProduct.inr σ * c⁻¹ * (c * SemidirectProduct.inl v * c⁻¹) =
        c * (SemidirectProduct.inr σ * SemidirectProduct.inl v) * c⁻¹ := by group
      _ = c * (SemidirectProduct.inl v * SemidirectProduct.inr σ) * c⁻¹ := by rw [hv.eq]
      _ = c * SemidirectProduct.inl v * c⁻¹ * (c * SemidirectProduct.inr σ * c⁻¹) := by group
  refine ⟨u, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hι
    rw [map_pow, hu, map_one]
    exact hconj_sq a ha
  · apply hι
    rw [map_pow, hw, map_one]
    exact hconj_sq b hb
  · intro h
    apply hconj_ne a ha1
    rw [← hu, h, map_one]
  · intro h
    apply hconj_ne b hb1
    rw [← hw, h, map_one]
  · intro h
    apply hab
    have h1 : c * SemidirectProduct.inl a * c⁻¹ = c * SemidirectProduct.inl b * c⁻¹ := by
      rw [← hu, ← hw, h]
    have h2 : (SemidirectProduct.inl a : PGammaL2 K) = SemidirectProduct.inl b := by
      have := congrArg (fun z => c⁻¹ * z * c) h1
      simpa [mul_assoc] using this
    exact SemidirectProduct.inl_injective h2
  · apply hι
    rw [map_mul, map_mul, hu, hw]
    calc c * SemidirectProduct.inl a * c⁻¹ * (c * SemidirectProduct.inl b * c⁻¹) =
        c * SemidirectProduct.inl (a * b) * c⁻¹ := by rw [map_mul]; group
      _ = c * SemidirectProduct.inl (b * a) * c⁻¹ := by rw [hcomm.eq]
      _ = c * SemidirectProduct.inl b * c⁻¹ * (c * SemidirectProduct.inl a * c⁻¹) := by
        rw [map_mul]; group
  · have := hcomm_x a hpa
    change x * ι u = ι u * x
    rw [hu]
    exact this
  · have := hcomm_x b hpb
    change x * ι w = ι w * x
    rw [hw]
    exact this

section Action

variable {R : Type} [Group R] (N : Subgroup R) [N.Normal] {K : Type} [Field K] [Finite K]
  (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (e : N ≃* PSL2 K)
  (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))

theorem psl2Action_apply (n : N) :
    normalPSL2ToPGammaL2 N K hK hcard e hsurj (n : R) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)) :=
  normalPSL2ToPGammaL2_apply_subtype N K hK hcard e hsurj n

theorem psl2Action_injective_on {n₁ n₂ : N}
    (h : normalPSL2ToPGammaL2 N K hK hcard e hsurj (n₁ : R) =
      normalPSL2ToPGammaL2 N K hK hcard e hsurj (n₂ : R)) : n₁ = n₂ := by
  rw [psl2Action_apply, psl2Action_apply] at h
  exact e.injective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (SemidirectProduct.inl_injective h))

theorem psl2Action_commute_iff (r : R) (n : N) :
    r * n = n * r ↔ normalPSL2ToPGammaL2 N K hK hcard e hsurj r *
      normalPSL2ToPGammaL2 N K hK hcard e hsurj n =
      normalPSL2ToPGammaL2 N K hK hcard e hsurj n * normalPSL2ToPGammaL2 N K hK hcard e hsurj r
    := by
  constructor
  · intro h
    rw [← map_mul, h, map_mul]
  · intro h
    let n' : N := ⟨r * n * r⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.2 r⟩
    have h1 : normalPSL2ToPGammaL2 N K hK hcard e hsurj (n' : R) =
        normalPSL2ToPGammaL2 N K hK hcard e hsurj (n : R) := by
      change normalPSL2ToPGammaL2 N K hK hcard e hsurj (r * n * r⁻¹) = _
      rw [map_mul, map_mul, map_inv, h]
      group
    have h2 := congrArg Subtype.val (psl2Action_injective_on N hK hcard e hsurj h1)
    change r * n * r⁻¹ = n at h2
    calc r * n = r * n * r⁻¹ * r := by group
      _ = n * r := by rw [h2]

theorem psl2Action_mem_pslRange (r : R)
    (hr : normalPSL2ToPGammaL2 N K hK hcard e hsurj r ∈ pGammaL2PSLRange K) :
    ∃ n : N, ∀ m : N, (r * (n : R)⁻¹) * m = m * (r * (n : R)⁻¹) := by
  obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff K _).mp hr
  refine ⟨e.symm y, fun m => ?_⟩
  rw [psl2Action_commute_iff N hK hcard e hsurj]
  have h1 : normalPSL2ToPGammaL2 N K hK hcard e hsurj (r * ((e.symm y : N) : R)⁻¹) = 1 := by
    rw [map_mul, map_inv, psl2Action_apply, MulEquiv.apply_symm_apply, hy, mul_inv_cancel]
  rw [h1, one_mul, mul_one]

theorem psl2Action_involution_linear (r : R) (hr : r ^ 2 = 1)
    (hno : ∀ u w : N, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u ≠ w → u * w = w * u →
      r * u = u * r → r * w = w * r → False) :
    ∃ g : PGL2 K, normalPSL2ToPGammaL2 N K hK hcard e hsurj r = SemidirectProduct.inl g := by
  set x := normalPSL2ToPGammaL2 N K hK hcard e hsurj r with hxdef
  have hx2 : x ^ 2 = 1 := by rw [hxdef, ← map_pow, hr, map_one]
  by_cases hfield : x.right = 1
  · refine ⟨x.left, ?_⟩
    apply SemidirectProduct.ext <;> simp [hfield]
  · exfalso
    obtain ⟨u, w, hu, hw, hu1, hw1, huw, hc, hxu, hxw⟩ :=
      field_involution_commuting_pair hK hcard x hx2 hfield
    have hpre : ∀ y : PSL2 K, normalPSL2ToPGammaL2 N K hK hcard e hsurj ((e.symm y : N) : R) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      intro y
      rw [psl2Action_apply, MulEquiv.apply_symm_apply]
    refine hno (e.symm u) (e.symm w) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_pow, hu, map_one]
    · rw [← map_pow, hw, map_one]
    · simpa using hu1
    · simpa using hw1
    · simpa using huw
    · rw [← map_mul, ← map_mul, hc]
    · rw [psl2Action_commute_iff N hK hcard e hsurj, hpre]
      exact hxu
    · rw [psl2Action_commute_iff N hK hcard e hsurj, hpre]
      exact hxw

end Action

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
