module

public import CFSG.ClassicalInvolution.SmallOrth.Primitive

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap
open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section TwoPairs

variable {P₁ P₂ : HypPair Q}

theorem exists_eichler_apply_eq_proj (hQ : (polarBilin Q).Nondegenerate) {x : V} (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) :
    ∃ w : V, w ∈ P₁.perp ∧ Q w = 0 ∧ w ≠ 0 ∧
      ∃ v : V, polar Q P₁.e v = 0 ∧ eichler Q P₁.e v x = w := by
  have hW := P₁.polarNondegOn_perp hQ
  set w := x - polar Q x P₁.f • P₁.e with hw
  have hwperp : w ∈ P₁.perp := by
    have := P₁.proj_mem_perp x
    rwa [HypPair.proj, polar_comm Q x P₁.e, hex, zero_smul, sub_zero] at this
  have hQw : Q w = 0 := by
    rw [hw, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, P₁.Q_e,
      polar_neg_right, polar_smul_right_eq, polar_comm Q x P₁.e, hex, hx]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    exact hxe (polar Q x P₁.f) (sub_eq_zero.mp h0)
  obtain ⟨v, hvW, hwv⟩ := hW.exists_polar_ne_zero hwperp hw0
  set v' := (polar Q x P₁.f / polar Q w v) • v with hv'
  have hv'W : v' ∈ P₁.perp := P₁.perp.smul_mem _ hvW
  have he₁v' : polar Q P₁.e v' = 0 := (HypPair.mem_perp.mp hv'W).1
  have hwv' : polar Q w v' = polar Q x P₁.f := by
    rw [hv', polar_smul_right_eq, div_mul_cancel₀ _ hwv]
  have hxv' : polar Q x v' = polar Q x P₁.f := by
    have : x = w + polar Q x P₁.f • P₁.e := by rw [hw]; abel
    rw [this, polar_add_left, polar_smul_left_eq, he₁v', mul_zero, add_zero, hwv', ← this]
  refine ⟨w, hwperp, hQw, hw0, v', he₁v', ?_⟩
  rw [eichler_apply P₁.Q_e he₁v', polar_comm Q x P₁.e, hex, hxv', zero_smul, add_zero, mul_zero,
    add_zero, hw]

theorem exists_fix_apply_eq_smul_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    (hA' : HasAnisoPerp (Q.restrict P₁.perp)) {x y : V} (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) (hy : Q y = 0)
    (hey : polar Q P₁.e y = 0) (hye : ∀ c : K, y ≠ c • P₁.e) :
    ∃ g ∈ elementaryGroup Q, g P₁.e = P₁.e ∧ ∃ c : K, c ≠ 0 ∧ g x = c • y := by
  have hW := P₁.polarNondegOn_perp hQ
  obtain ⟨wx, hwxP, hwxQ, hwx0, vx, hvx, hxw⟩ := exists_eichler_apply_eq_proj hQ hx hex hxe
  obtain ⟨wy, hwyP, hwyQ, hwy0, vy, hvy, hyw⟩ := exists_eichler_apply_eq_proj hQ hy hey hye
  obtain ⟨g', hg', c, hc, hgc⟩ := exists_mem_elementaryGroup_apply_eq_smul
    (Q := Q.restrict P₁.perp) (nondegenerate_polarBilin_restrict hW) hA'
    (x := (⟨wx, hwxP⟩ : P₁.perp)) (y := (⟨wy, hwyP⟩ : P₁.perp))
    hwxQ hwyQ (fun h => hwx0 (congrArg Subtype.val h)) (fun h => hwy0 (congrArg Subtype.val h))
  obtain ⟨g, hg, hgW, hgz⟩ := exists_extend_of_mem_elementaryGroup_restrict hg'
  have hge : g P₁.e = P₁.e :=
    hgz P₁.e fun z hz => (HypPair.mem_perp.mp hz).1
  have hgw : g wx = c • wy := by
    have := hgW ⟨wx, hwxP⟩
    rw [hgc] at this
    exact this
  refine ⟨(eichler Q P₁.e vy)⁻¹ * g * eichler Q P₁.e vx,
    mul_mem (mul_mem (inv_mem (eichler_mem_elementaryGroup Q _ _)) hg)
      (eichler_mem_elementaryGroup Q _ _), ?_, c, hc, ?_⟩
  · have h1 : (eichler Q P₁.e vy)⁻¹ P₁.e = P₁.e := by
      apply (eichler Q P₁.e vy).injective
      rw [LinearEquiv.apply_inv_apply', eichler_apply_self]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_apply_self, hge, h1]
  · have h1 : (eichler Q P₁.e vy)⁻¹ wy = y := by
      apply (eichler Q P₁.e vy).injective
      rw [LinearEquiv.apply_inv_apply', hyw]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxw, hgw, map_smul, h1]

theorem e₂_ne (h₁₂ : P₁.Orth P₂) : ∀ c : K, P₂.e ≠ c • P₁.e := by
  intro c hc
  have := congrArg (fun z => polar Q z P₂.f) hc
  simp only [polar_smul_left_eq, P₂.polar_ef, h₁₂.ef, mul_zero] at this
  exact one_ne_zero this

theorem f₂_ne (h₁₂ : P₁.Orth P₂) : ∀ c : K, P₂.f ≠ c • P₁.e := by
  intro c hc
  have := congrArg (fun z => polar Q z P₂.e) hc
  simp only [polar_smul_left_eq, P₂.polar_fe, h₁₂.ee, mul_zero] at this
  exact one_ne_zero this

variable {B : Set (singularLines Q)}

theorem mem_of_isBlock_perp' (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hA' : HasAnisoPerp (Q.restrict P₁.perp)) (hB : MulAction.IsBlock (elementaryGroup Q) B)
    (hα : lineMk P₁.e P₁.e_ne_zero P₁.Q_e ∈ B) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) (hxB : lineMk x hx0 hx ∈ B)
    {y : V} (hy0 : y ≠ 0) (hy : Q y = 0) (hey : polar Q P₁.e y = 0)
    (hye : ∀ c : K, y ≠ c • P₁.e) : lineMk y hy0 hy ∈ B := by
  obtain ⟨g, hg, hge, c₁, hc₁, hgx⟩ := exists_fix_apply_eq_smul_of_polar_eq_zero hQ hA' hx hex hxe
    P₂.Q_e h₁₂.ee (e₂_ne h₁₂)
  obtain ⟨k, hk, hke, c₂, hc₂, hky⟩ := exists_fix_apply_eq_smul_of_polar_eq_zero hQ hA' hy hey hye
    P₂.Q_e h₁₂.ee (e₂_ne h₁₂)
  have hgα : (⟨g, hg⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hge)
  have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
  have he₂ : lineMk P₂.e P₂.e_ne_zero P₂.Q_e ∈ B := by
    have := smul_mem_of_isBlock' hB hα hxB hgα
    rwa [smul_lineMk_of_apply_eq_smul hx0 P₂.e_ne_zero hx P₂.Q_e (c := c₁) hgx] at this
  have := inv_smul_mem_of_isBlock' hB hα he₂ hkα
  have hky' : (⟨k, hk⟩ : elementaryGroup Q) • lineMk y hy0 hy =
      lineMk P₂.e P₂.e_ne_zero P₂.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := c₂) hky
  rwa [← hky', inv_smul_smul] at this

theorem eq_univ_of_isBlock_perp' (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) (hA' : HasAnisoPerp (Q.restrict P₁.perp))
    (hB : MulAction.IsBlock (elementaryGroup Q) B)
    (hα : lineMk P₁.e P₁.e_ne_zero P₁.Q_e ∈ B) {x : V} (hx0 : x ≠ 0) (hx : Q x = 0)
    (hex : polar Q P₁.e x = 0) (hxe : ∀ c : K, x ≠ c • P₁.e) (hxB : lineMk x hx0 hx ∈ B) :
    B = Set.univ := by
  have hperp : ∀ {y : V} (hy0 : y ≠ 0) (hy : Q y = 0), polar Q P₁.e y = 0 →
      (∀ c : K, y ≠ c • P₁.e) → lineMk y hy0 hy ∈ B := fun hy0 hy hey hye =>
    mem_of_isBlock_perp' h₁₂ hQ hA' hB hα hx0 hx hex hxe hxB hy0 hy hey hye
  have he₂B : lineMk P₂.e P₂.e_ne_zero P₂.Q_e ∈ B := hperp _ _ h₁₂.ee (e₂_ne h₁₂)
  have hf₂B : lineMk P₂.f P₂.f_ne_zero P₂.Q_f ∈ B := hperp _ _ h₁₂.ef (f₂_ne h₁₂)
  obtain ⟨h, hh, c₀, hc₀, hhe⟩ := exists_mem_elementaryGroup_apply_eq_smul hQ hA P₂.Q_e P₁.Q_e
    P₂.e_ne_zero P₁.e_ne_zero
  have hhO := elementaryGroup_le_orthogonalGroup Q hh
  have hhα : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₂.e P₂.e_ne_zero P₂.Q_e =
      lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    smul_lineMk_of_apply_eq_smul _ _ _ _ (c := c₀) hhe
  have hBh := hB.smul_eq_of_mem he₂B (by rw [hhα]; exact hα)
  have hzB : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₂.f P₂.f_ne_zero P₂.Q_f ∈ B := by
    rw [← hBh]
    exact Set.smul_mem_smul_set hf₂B
  rw [smul_lineMk] at hzB
  set z := h P₂.f
  have hez : polar Q P₁.e z ≠ 0 := by
    intro h0
    have := polar_map_of_mem hhO P₂.e P₂.f
    rw [hhe, polar_smul_left_eq, h0, mul_zero, P₂.polar_ef] at this
    exact zero_ne_one this
  have hz0 : z ≠ 0 := fun h0 => hez (by rw [h0, polar_zero_right])
  have hQz : Q z = 0 := by rw [map_of_mem hhO, P₂.Q_f]
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨y, hy0, hy, rfl⟩ := exists_eq_lineMk p
  by_cases hey : polar Q P₁.e y = 0
  · by_cases hye : ∀ c : K, y ≠ c • P₁.e
    · exact hperp hy0 hy hey hye
    · push Not at hye
      obtain ⟨c, rfl⟩ := hye
      have hc : c ≠ 0 := by
        rintro rfl
        exact hy0 (zero_smul K _)
      have : lineMk (c • P₁.e) hy0 hy = lineMk P₁.e P₁.e_ne_zero P₁.Q_e := by
        rw [lineMk_eq_lineMk_iff]
        exact ⟨c, rfl⟩
      rw [this]
      exact hα
  · obtain ⟨k, hk, hke, c, hkz⟩ :=
      exists_fix_apply_eq_smul_of_polar_ne_zero P₁.Q_e hQz hy hez hey
    have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
        lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
      smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
    have := smul_mem_of_isBlock' hB hα hzB hkα
    rwa [smul_lineMk_of_apply_eq_smul hz0 hy0 hQz hy hkz] at this

theorem isPreprimitive_singularLines_of_orth (h₁₂ : P₁.Orth P₂) (hQ : (polarBilin Q).Nondegenerate)
    (hA : HasAnisoPerp Q) (hA' : HasAnisoPerp (Q.restrict P₁.perp)) :
    MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q) := by
  have := isPretransitive_singularLines_small hQ hA
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base (lineMk P₁.e P₁.e_ne_zero P₁.Q_e)
  intro B hα hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨b, hbB, hbα⟩ : ∃ b ∈ B, b ≠ lineMk P₁.e P₁.e_ne_zero P₁.Q_e := by
    by_contra hcon
    push Not at hcon
    exact hsub fun p hp q hq => by rw [hcon p hp, hcon q hq]
  obtain ⟨x, hx0, hx, rfl⟩ := exists_eq_lineMk b
  have hxe : ∀ c : K, x ≠ c • P₁.e := by
    intro c hc
    apply hbα
    rw [lineMk_eq_lineMk_iff]
    exact ⟨c, hc.symm⟩
  by_cases hex : polar Q P₁.e x = 0
  · exact eq_univ_of_isBlock_perp' h₁₂ hQ hA hA' hB hα hx0 hx hex hxe hbB
  ·
    have hef₁ : polar Q P₁.e P₁.f ≠ 0 := by rw [P₁.polar_ef]; exact one_ne_zero
    have hQfe : Q (P₁.f + P₂.e) = 0 := by
      rw [QuadraticMap.map_add Q, P₁.Q_f, P₂.Q_e, h₁₂.fe, add_zero, add_zero]
    have hefe : polar Q P₁.e (P₁.f + P₂.e) ≠ 0 := by
      rw [polar_add_right, P₁.polar_ef, h₁₂.ee, add_zero]
      exact one_ne_zero
    have hfe0 : P₁.f + P₂.e ≠ 0 := fun h0 => hefe (by rw [h0, polar_zero_right])
    have hmem : ∀ {y : V} (hy0 : y ≠ 0) (hy : Q y = 0), polar Q P₁.e y ≠ 0 →
        lineMk y hy0 hy ∈ B := by
      intro y hy0 hy hey
      obtain ⟨k, hk, hke, c, hkx⟩ :=
        exists_fix_apply_eq_smul_of_polar_ne_zero P₁.Q_e hx hy hex hey
      have hkα : (⟨k, hk⟩ : elementaryGroup Q) • lineMk P₁.e P₁.e_ne_zero P₁.Q_e =
          lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
        smul_lineMk_of_apply_eq_smul _ _ _ _ (c := 1) (by rw [one_smul]; exact hke)
      have := smul_mem_of_isBlock' hB hα hbB hkα
      rwa [smul_lineMk_of_apply_eq_smul hx0 hy0 hx hy hkx] at this
    have hf₁B := hmem P₁.f_ne_zero P₁.Q_f hef₁
    have hfeB := hmem hfe0 hQfe hefe
    obtain ⟨h, hh, c₀, hc₀, hhf⟩ := exists_mem_elementaryGroup_apply_eq_smul hQ hA P₁.Q_f P₁.Q_e
      P₁.f_ne_zero P₁.e_ne_zero
    have hhO := elementaryGroup_le_orthogonalGroup Q hh
    have hhα : (⟨h, hh⟩ : elementaryGroup Q) • lineMk P₁.f P₁.f_ne_zero P₁.Q_f =
        lineMk P₁.e P₁.e_ne_zero P₁.Q_e :=
      smul_lineMk_of_apply_eq_smul _ _ _ _ (c := c₀) hhf
    have hBh := hB.smul_eq_of_mem hf₁B (by rw [hhα]; exact hα)
    have hzB : (⟨h, hh⟩ : elementaryGroup Q) • lineMk (P₁.f + P₂.e) hfe0 hQfe ∈ B := by
      rw [← hBh]
      exact Set.smul_mem_smul_set hfeB
    rw [smul_lineMk] at hzB
    have he₁ : P₁.e = c₀⁻¹ • h P₁.f := by rw [hhf, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
    refine eq_univ_of_isBlock_perp' h₁₂ hQ hA hA' hB hα _ _ ?_ ?_ hzB
    · rw [he₁, polar_smul_left_eq, polar_map_of_mem hhO, polar_add_right, P₁.polar_ff, h₁₂.fe,
        add_zero, mul_zero]
    · intro c hc
      have h1 : P₁.f + P₂.e = (c * c₀⁻¹) • P₁.f := by
        apply h.injective
        rw [hc, map_smul, hhf, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀, mul_one]
      have := congrArg (fun z => polar Q z P₂.f) h1
      simp only [polar_add_left, polar_smul_left_eq, P₂.polar_ef, h₁₂.ff, mul_zero,
        zero_add] at this
      exact one_ne_zero this

end TwoPairs

end CFSG.ClassicalGroups.Orthogonal.Small
