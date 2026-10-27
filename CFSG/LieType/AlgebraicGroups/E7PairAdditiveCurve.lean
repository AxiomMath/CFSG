module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.InnerInvolutionTorus
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
import CFSG.LieType.Chevalley.MonomialInvertedRootRotation
import CFSG.LieType.AlgebraicGroups.E7MonomialGoodRoot
import CFSG.LieType.AlgebraicGroups.MonomialCentralizerRootCurves
import CFSG.LieType.AlgebraicGroups.CocharacterCurve

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p]

private abbrev e7RootDiag (a : Fin Tag.E7.rank → Lˣ) : ModGL Tag.E7 L :=
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E7 a

theorem e7_exists_additive_curve_commute_pair (hp2 : p ≠ 2)
    (halg : letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L)
    {x y : ModGL Tag.E7 L} (hx : x ∈ adjointGroup Tag.E7 L) (hy : y ∈ adjointGroup Tag.E7 L)
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hxy : Commute x y) :
    ∃ c : L → ModGL Tag.E7 L, IsPolynomialCurve c ∧ c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧
      (∃ t, c t ≠ 1) ∧
        ∀ t, c t ∈ adjointGroup Tag.E7 L ∧ Commute (c t) x ∧ Commute (c t) y := by
  classical
  obtain ⟨g₁, hg₁G, a, hasign, hconj⟩ :=
    exceptional_Lang_inner_involution_torus_conjugacy Tag.E7 hp2 L hx hx2
  have hdaG : e7RootDiag a ∈ adjointGroup Tag.E7 L := by
    rw [show e7RootDiag a = g₁ * x * g₁⁻¹ from hconj.symm]
    exact (adjointGroup Tag.E7 L).mul_mem
      ((adjointGroup Tag.E7 L).mul_mem hg₁G hx) ((adjointGroup Tag.E7 L).inv_mem hg₁G)
  set y₁ : ModGL Tag.E7 L := g₁ * y * g₁⁻¹ with hy₁def
  have hy₁G : y₁ ∈ adjointGroup Tag.E7 L := by
    rw [hy₁def]
    exact (adjointGroup Tag.E7 L).mul_mem
      ((adjointGroup Tag.E7 L).mul_mem hg₁G hy) ((adjointGroup Tag.E7 L).inv_mem hg₁G)
  have hy₁2 : y₁ ^ 2 = 1 := by
    rw [hy₁def, conj_pow, hy2, mul_one, mul_inv_cancel]
  have hcomm : Commute (e7RootDiag a) y₁ := by
    have h := hxy.map (MulAut.conj g₁).toMonoidHom
    simpa [MulAut.conj_apply, hconj, hy₁def] using h
  have hBfin : (Subgroup.zpowers y₁ : Set (ModGL Tag.E7 L)).Finite := by
    have hcard : Nat.card (Subgroup.zpowers y₁) ≠ 0 := by
      rw [Nat.card_zpowers]
      exact (Nat.pos_of_dvd_of_pos (orderOf_dvd_iff_pow_eq_one.2 hy₁2) (by norm_num)).ne'
    exact Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero hcard)
  have hexp : ∀ x ∈ Subgroup.zpowers y₁, x ^ 2 = 1 := by
    intro x hx
    exact orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_iff_pow_eq_one.2 hy₁2))
  have hBa : ∀ x ∈ Subgroup.zpowers y₁,
      e7RootDiag a * x = x * e7RootDiag a := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (hcomm.zpow_right k).eq
  obtain ⟨z, hzG, hzda, hzB⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_le_monomial_centralizer_bar
      (τ := Tag.E7) (L := L) (ℓ := p) (p := 2) hp2 halg a
      (Subgroup.zpowers_le.2 hy₁G) hBfin hBa hexp
  set n : ModGL Tag.E7 L := z * y₁ * z⁻¹ with hndef
  have hnN : n ∈ monomialSubgroup Tag.E7 L := hzB y₁ (Subgroup.mem_zpowers y₁)
  have hnG : n ∈ adjointGroup Tag.E7 L := by
    rw [hndef]
    exact (adjointGroup Tag.E7 L).mul_mem
      ((adjointGroup Tag.E7 L).mul_mem hzG hy₁G) ((adjointGroup Tag.E7 L).inv_mem hzG)
  have hn2 : n ^ 2 = 1 := by
    rw [hndef, conj_pow, hy₁2, mul_one, mul_inv_cancel]
  have hna : e7RootDiag a * n = n * e7RootDiag a := by
    have hdz : Commute (e7RootDiag a) z := hzda
    have hdn : Commute (e7RootDiag a) (z * y₁ * z⁻¹) :=
      (hdz.mul_right hcomm).mul_right hdz.inv_right
    rw [hndef]
    exact hdn.eq
  have hk : ringChar L ≠ 2 := by
    rw [ringChar.eq L p]
    exact hp2
  obtain ⟨g, hgG, hgda, hgn, hnoinv⟩ :=
    exists_conj_monomial_no_inverted_root hk a hnN hn2
  set n' : ModGL Tag.E7 L := g * n * g⁻¹ with hn'def
  have hn'G : n' ∈ adjointGroup Tag.E7 L := by
    rw [hn'def]
    exact (adjointGroup Tag.E7 L).mul_mem
      ((adjointGroup Tag.E7 L).mul_mem hgG hnG) ((adjointGroup Tag.E7 L).inv_mem hgG)
  have hn'2 : n' ^ 2 = 1 := by
    rw [hn'def, conj_pow, hn2, mul_one, mul_inv_cancel]
  have hn'a : e7RootDiag a * n' = n' * e7RootDiag a := by
    have hdg : Commute (e7RootDiag a) g := hgda
    have hdn : Commute (e7RootDiag a) (g * n * g⁻¹) :=
      (hdg.mul_right hna).mul_right hdg.inv_right
    rw [hn'def]
    exact hdn.eq
  obtain ⟨α, hα, hαa, hgood⟩ :=
    e7_exists_good_root hp2 a hasign hdaG hn'G hgn hn'2 hn'a
  have hαinv : weylQuotientHom Tag.E7 L ⟨n', hgn⟩ • α ≠ -α := hnoinv α hα hαa
  obtain ⟨c, hc, hc0, hcadd, hcntriv, hcprops⟩ :=
    exists_additive_curve_of_good_root (hτ := Or.inr (Or.inr (Or.inl rfl))) hk a hgn hn'2 hn'a
      hα hαa hαinv hgood
  set h : ModGL Tag.E7 L := g * z * g₁ with hhdef
  have hhG : h ∈ adjointGroup Tag.E7 L := by
    rw [hhdef]
    exact (adjointGroup Tag.E7 L).mul_mem
      ((adjointGroup Tag.E7 L).mul_mem hgG hzG) hg₁G
  have hzd : z * e7RootDiag a * z⁻¹ = e7RootDiag a := by
    rw [hzda.symm, mul_inv_cancel_right]
  have hgd : g * e7RootDiag a * g⁻¹ = e7RootDiag a := by
    rw [hgda.symm, mul_inv_cancel_right]
  have hxh : h * x * h⁻¹ = e7RootDiag a := by
    rw [hhdef]
    calc (g * z * g₁) * x * (g * z * g₁)⁻¹
        = g * z * (g₁ * x * g₁⁻¹) * z⁻¹ * g⁻¹ := by group
      _ = g * z * e7RootDiag a * z⁻¹ * g⁻¹ := by rw [hconj]
      _ = g * (z * e7RootDiag a * z⁻¹) * g⁻¹ := by group
      _ = g * e7RootDiag a * g⁻¹ := by rw [hzd]
      _ = e7RootDiag a := by rw [hgd]
  have hyh : h * y * h⁻¹ = n' := by
    rw [hhdef, hn'def, hndef, hy₁def]
    group
  have hxeq : x = h⁻¹ * e7RootDiag a * h := by
    calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
      _ = h⁻¹ * e7RootDiag a * h := by rw [hxh]
  have hyeq : y = h⁻¹ * n' * h := by
    calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
      _ = h⁻¹ * n' * h := by rw [hyh]
  refine ⟨fun t => h⁻¹ * c t * h, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [inv_inv] using hc.conj h⁻¹
  · change h⁻¹ * c 0 * h = 1
    rw [hc0]
    group
  · intro s t
    change h⁻¹ * c (s + t) * h = (h⁻¹ * c s * h) * (h⁻¹ * c t * h)
    rw [hcadd]
    group
  · obtain ⟨t, ht⟩ := hcntriv
    refine ⟨t, fun h1 => ht ?_⟩
    calc c t = h * (h⁻¹ * c t * h) * h⁻¹ := by group
      _ = h * 1 * h⁻¹ := by rw [show h⁻¹ * c t * h = 1 from h1]
      _ = 1 := by group
  · intro t
    refine ⟨?_, ?_, ?_⟩
    · change h⁻¹ * c t * h ∈ adjointGroup Tag.E7 L
      exact (adjointGroup Tag.E7 L).mul_mem
        ((adjointGroup Tag.E7 L).mul_mem ((adjointGroup Tag.E7 L).inv_mem hhG) (hcprops t).1)
        hhG
    · change Commute (h⁻¹ * c t * h) x
      have hct : Commute (c t) (e7RootDiag a) := (hcprops t).2.1
      rw [hxeq]
      simpa only [inv_inv] using hct.conj h⁻¹
    · change Commute (h⁻¹ * c t * h) y
      have hct : Commute (c t) n' := (hcprops t).2.2
      rw [hyeq]
      simpa only [inv_inv] using hct.conj h⁻¹

end CFSG.LieType.AlgebraicGroups
