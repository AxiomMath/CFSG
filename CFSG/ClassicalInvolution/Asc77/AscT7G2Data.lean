module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Cnt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7G2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


section Data

variable (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)

include hyp

theorem exists_nonfused_of_data {g : G} (hg : g * z * g⁻¹ = t) (ht2 : t * t = 1) {x c₁ ω : G}
    (hc₁R : c₁ ∈ R) (hc₁4 : orderOf c₁ = 4) (hωc₁ : ω * c₁ = c₁ * ω) (hω2 : ω * ω = 1)
    (htω : t * ω = ω * t) (hω1 : ω ≠ 1) (hωz : ω ≠ z) (hxt : x⁻¹ * t * x = t * ω) :
    ∃ s' : G, s' * s' = 1 ∧ s' * z = z * s' ∧ (∃ y : G, y * z * y⁻¹ = s') ∧
      conjSub s' K ≠ K ∧ ¬ ∃ y : G, y * z * y⁻¹ = s' * z := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 : MuIsoE4 Ω W := hyp.hE4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  obtain ⟨htS, htz, -⟩ := hyp.ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : (t * ω) * (t * ω) = 1 := by
    calc (t * ω) * (t * ω) = (t * (ω * t)) * ω := by group
      _ = (t * (t * ω)) * ω := by rw [htω]
      _ = (t * t) * (ω * ω) := by group
      _ = 1 := by rw [ht2, hω2]; group
  have hst : (t * ω) * t = t * (t * ω) := by
    calc (t * ω) * t = t * (ω * t) := by group
      _ = t * (t * ω) := by rw [htω]
  have hsne : t * ω ≠ t := by
    intro h
    apply hω1
    have := congrArg (fun w => t⁻¹ * w) h
    simpa using this
  obtain ⟨hsy⟩ : Nonempty (∃ y : G, y * z * y⁻¹ = t * ω) := by
    refine ⟨⟨x⁻¹ * g, ?_⟩⟩
    calc x⁻¹ * g * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
      _ = x⁻¹ * t * x := by rw [hg]
      _ = t * ω := hxt
  have hts : t * (t * ω) = ω := by
    calc t * (t * ω) = (t * t) * ω := by group
      _ = ω := by rw [ht2]; group
  have hnotz : ¬ ∃ y : G, y * z * y⁻¹ = ω := by
    rintro ⟨y, hy⟩
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hK hz (y := y) (by rw [hy]; exact hωz)
      (hRsyl.1 hc₁R) hc₁4
    rw [hy] at this
    exact this hωc₁
  have hnotN : conjSub (t * ω) (conjSub g K) ≠ conjSub g K := by
    intro hN
    have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have htJ : IsUniqueInvolution (conjSub g K) t := by
      have := hz.conj g
      rwa [hg] at this
    have hsN : t * ω ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hN
    obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (T7ER.isPGroup_zpowers_of_sq hs2)
      (Subgroup.zpowers_le.mpr hsN)
    have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
    have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hp hRtmem
    have htRt : t ∈ Rt := T7C.mem_of_isSylow2In hp hΩ hJt hRtsyl htJ
    have hzRt : IsUniqueInvolution Rt t :=
      ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
    have hsRt : conjSub (t * ω) Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
    have hbR : ∀ r ∈ Rt, (t * ω) * r * (t * ω)⁻¹ ∈ Rt := fun r hr => by
      have := conj_mem_conjSub (n := t * ω) hr
      rwa [hsRt] at this
    have hfixt : ∀ r ∈ Rt, orderOf r = 4 → (t * ω) * r * (t * ω)⁻¹ ≠ r := by
      intro r hr hr4 h
      obtain ⟨y, hy⟩ := hsy
      have := T7ER.not_commute_of_conj hs hW₀ hE4 hJt htJ (y := y)
        (by rw [hy]; exact hsne) (hRtsyl.1 hr) hr4
      rw [hy] at this
      apply this
      have h1 := congrArg (fun w => w * (t * ω)) h
      simpa [mul_assoc] using h1
    obtain ⟨ρ, hρ, hρs⟩ := T7ER.exists_conj_eq_mul_inv hRtq hzRt hs2 hbR hfixt
    apply hnotz
    obtain ⟨y, hy⟩ := hsy
    refine ⟨ρ⁻¹ * y, ?_⟩
    calc ρ⁻¹ * y * z * (ρ⁻¹ * y)⁻¹ = ρ⁻¹ * (y * z * y⁻¹) * ρ := by group
      _ = ρ⁻¹ * (t * ω) * ρ := by rw [hy]
      _ = ρ⁻¹ * ((t * ω) * ρ * (t * ω)⁻¹) * (t * ω) := by group
      _ = ρ⁻¹ * (ρ * t) * (t * ω) := by rw [hρs]
      _ = t * (t * ω) := by group
      _ = ω := hts
  refine ⟨g⁻¹ * (t * ω) * g, ?_, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * (t * ω) * g * (g⁻¹ * (t * ω) * g) = g⁻¹ * ((t * ω) * (t * ω)) * g := by group
      _ = 1 := by rw [hs2]; group
  · have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
      _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
      _ = z * (g⁻¹ * (t * ω) * g) := by rw [hzg]; group
  · obtain ⟨y, hy⟩ := hsy
    refine ⟨g⁻¹ * y, ?_⟩
    calc g⁻¹ * y * z * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * z * y⁻¹) * g := by group
      _ = g⁻¹ * (t * ω) * g := by rw [hy]
  · intro hN
    apply hnotN
    have h1 : conjSub (g * (g⁻¹ * (t * ω) * g)) K = conjSub ((t * ω) * g) K := by
      congr 1; group
    rw [conjSub_mul, hN, conjSub_mul] at h1
    exact h1.symm
  · rintro ⟨y, hy⟩
    apply hnotz
    refine ⟨g * y, ?_⟩
    have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    have hsz : g⁻¹ * (t * ω) * g * z = g⁻¹ * ω * g := by
      calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
        _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
        _ = g⁻¹ * ω * g := by rw [hts]
    rw [hsz] at hy
    calc g * y * z * (g * y)⁻¹ = g * (y * z * y⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * ω * g) * g⁻¹ := by rw [hy]
      _ = ω := by group

end Data

section Swap

variable (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)

include hyp

theorem not_orderOf_four_of_mem_inf {y : G} (hyR : y ∈ R) (hyR' : y ∈ R') (hy4 : orderOf y = 4)
    (ht2 : t * t = 1) (hRt : conjSub t R = R') : False := by
  have hT : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t := ⟨hyp, hyp.ht.1, ht2, hRt⟩
  have hle : Subgroup.zpowers y ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hyR, hyR'⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hy4, hT.inf_R_R'] at h1
  omega

theorem data_of_swap (ht2 : t * t = 1) (hRt : conjSub t R = R') :
    ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧ t * ω = ω * t ∧
      ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
  have hT : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t := ⟨hyp, hyp.ht.1, ht2, hRt⟩
  obtain ⟨hu₁R, hu₁4, -⟩ := hyp.hu₁
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set c₂ : G := t * u₁⁻¹ * t with hc₂
  have hc₂R' : c₂ ∈ R' := by
    have := conj_mem_conjSub (n := t) (R.inv_mem hu₁R)
    rw [hRt, hti] at this
    exact this
  have hc₂4 : orderOf c₂ = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj t) u₁⁻¹
    simp only [MulAut.conj_apply, hti] at h
    rw [hc₂, h, orderOf_inv, hu₁4]
  have hcc : u₁ * c₂ = c₂ * u₁ := hT.hcomm u₁ hu₁R c₂ hc₂R'
  have hc₁sq : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hT.hzR hu₁R hu₁4
  have hc₂sq : c₂ * c₂ = z := T7A.sq_eq_of_orderOf_four hT.hzR' hc₂R' hc₂4
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have hω2 : (c₂ * u₁) * (c₂ * u₁) = 1 := by
    calc (c₂ * u₁) * (c₂ * u₁) = c₂ * (u₁ * c₂) * u₁ := by group
      _ = c₂ * (c₂ * u₁) * u₁ := by rw [hcc]
      _ = (c₂ * c₂) * (u₁ * u₁) := by group
      _ = 1 := by rw [hc₁sq, hc₂sq, hzz]
  have hωinv : (c₂ * u₁)⁻¹ = c₂ * u₁ := inv_eq_of_mul_eq_one_right hω2
  have h1 : t * c₂ * t = u₁⁻¹ := by
    rw [hc₂]
    calc t * (t * u₁⁻¹ * t) * t = (t * t) * u₁⁻¹ * (t * t) := by group
      _ = u₁⁻¹ := by rw [ht2]; group
  have h2 : t * u₁ * t = c₂⁻¹ := by
    rw [hc₂]
    calc t * u₁ * t = t⁻¹ * u₁ * t⁻¹ := by rw [hti]
      _ = (t * u₁⁻¹ * t)⁻¹ := by group
  have hconj : t * (c₂ * u₁) * t = c₂ * u₁ := by
    calc t * (c₂ * u₁) * t = (t * c₂ * t) * (t * u₁ * t) := by
          calc t * (c₂ * u₁) * t = t * c₂ * (t * t) * u₁ * t := by rw [ht2]; group
            _ = (t * c₂ * t) * (t * u₁ * t) := by group
      _ = u₁⁻¹ * c₂⁻¹ := by rw [h1, h2]
      _ = (c₂ * u₁)⁻¹ := by group
      _ = c₂ * u₁ := hωinv
  refine ⟨u₁, u₁, c₂ * u₁, hu₁R, hu₁4, ?_, hω2, ?_, ?_, ?_, ?_⟩
  · calc (c₂ * u₁) * u₁ = (u₁ * c₂) * u₁ := by rw [hcc]
      _ = u₁ * (c₂ * u₁) := by group
  · calc t * (c₂ * u₁) = (t * (c₂ * u₁) * t) * t := by
          rw [mul_assoc (t * (c₂ * u₁)) t t, ht2, mul_one]
      _ = (c₂ * u₁) * t := by rw [hconj]
  · intro h
    have hu : u₁ = c₂⁻¹ := eq_inv_of_mul_eq_one_right h
    exact not_orderOf_four_of_mem_inf hyp hu₁R (hu ▸ R'.inv_mem hc₂R') hu₁4 ht2 hRt
  · intro h
    have hc₂z : c₂ = z * u₁⁻¹ := by
      have : c₂ * u₁ * u₁⁻¹ = z * u₁⁻¹ := by rw [h]
      simpa using this
    have hc₂R : c₂ ∈ R := by
      rw [hc₂z]
      exact R.mul_mem hT.hzR.mem (R.inv_mem hu₁R)
    exact not_orderOf_four_of_mem_inf hyp hc₂R hc₂R' hc₂4 ht2 hRt
  · calc u₁⁻¹ * t * u₁ = (t * t) * u₁⁻¹ * t * u₁ := by rw [ht2]; group
      _ = t * (c₂ * u₁) := by rw [hc₂]; group

end Swap

end T7G2

end CFSG.ClassicalInvolution.Asc77
