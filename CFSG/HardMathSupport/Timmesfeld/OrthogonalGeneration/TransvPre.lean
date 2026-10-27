module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthJ
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Iwasawa
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Odd

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [IsF2 K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_of_commute_eichler [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hd : 3 ≤ finrank K V) {g : V ≃ₗ[K] V}
    (hc : ∀ u w, Q u = 0 → polar Q u w = 0 → g * eichler Q u w = eichler Q u w * g) : g = 1 := by
  refine eq_one_of_fixes_singular hQ hd fun u hu0 hu => ?_
  have hfix : ∀ w, polar Q u w = 0 → eichler Q u w (g u) = g u := by
    intro w hw
    have h1 := hc u w hu hw
    have h2 := congrArg (fun z => z u) h1
    simp only [LinearEquiv.mul_apply, eichler_apply_self] at h2
    exact h2.symm
  obtain ⟨c, hc'⟩ := exists_smul_of_fixed_by_rootGroup hQ hd hu hu0 hfix
  rcases IsF2.eq_zero_or_one c with h | h
  · exfalso
    rw [h, zero_smul, LinearEquiv.map_eq_zero_iff] at hc'
    exact hu0 hc'
  · rw [h, one_smul] at hc'
    exact hc'

theorem eq_apply_of_commute_orthJ_of_three_le [FiniteDimensional K V] {W : Submodule K V}
    (hW : PolarNondegOn Q W) (hd : 3 ≤ finrank K W) {g : V ≃ₗ[K] V}
    (hgW : ∀ w, w ∈ W ↔ g w ∈ W) (hc : ∀ x ∈ orthJ Q W, g * x = x * g) :
    ∀ w ∈ W, g w = w := by
  set g' : W ≃ₗ[K] W := restrictStab W g hgW with hg'
  have hcomm : ∀ u w : W, (Q.restrict W) u = 0 → polar (Q.restrict W) u w = 0 →
      g' * eichler (Q.restrict W) u w = eichler (Q.restrict W) u w * g' := by
    intro u w _ _
    rw [← orthJRestrict_eichler u.2 w.2]
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    have := congrArg (fun f : V ≃ₗ[K] V => f (x : V)) (hc _ (eichler_mem_orthJ u.2 w.2))
    exact this
  have h1 := eq_one_of_commute_eichler (nondegenerate_polarBilin_restrict hW) hd hcomm
  intro w hw
  have := congrArg (fun f : W ≃ₗ[K] W => (f ⟨w, hw⟩ : V)) h1
  exact this

theorem two_le_finrank_of_polar_ne_zero [FiniteDimensional K V] {W : Submodule K V} {b b' : V}
    (hb : b ∈ W) (hb' : b' ∈ W) (h : polar Q b b' ≠ 0) : 2 ≤ finrank K W := by
  by_contra hlt
  push Not at hlt
  have h1 : finrank K W ≤ 1 := by omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h1
  obtain ⟨c, hc⟩ := hv ⟨b, hb⟩
  obtain ⟨c', hc'⟩ := hv ⟨b', hb'⟩
  have e1 : b = c • (v : V) := congrArg Subtype.val hc.symm
  have e2 : b' = c' • (v : V) := congrArg Subtype.val hc'.symm
  apply h
  rw [e1, e2, polar_smul_left_eq, polar_smul_right_eq, polar_self_f2, mul_zero, mul_zero]

theorem two_le_finrank_of_polarNondegOn [FiniteDimensional K V] {W : Submodule K V}
    (hW : PolarNondegOn Q W) (h0 : W ≠ ⊥) : 2 ≤ finrank K W := by
  obtain ⟨a, haW, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨y, hyW, hy⟩ := hW.exists_polar_ne_zero haW ha0
  exact two_le_finrank_of_polar_ne_zero haW hyW hy

theorem four_le_finrank_of_lt [FiniteDimensional K V] {W₁ W₂ : Submodule K V}
    (h1 : PolarNondegOn Q W₁) (h2 : PolarNondegOn Q W₂) (h0 : W₁ ≠ ⊥) (hlt : W₁ < W₂) :
    4 ≤ finrank K W₂ := by
  obtain ⟨x, hx2, hx1⟩ := IsConcreteLE.exists_of_lt hlt
  have hsplit : ∀ z : V, ∃ a ∈ W₁, ∃ b ∈ perpSub Q W₁, z = a + b := by
    intro z
    have hz : z ∈ W₁ ⊔ perpSub Q W₁ := by rw [(isCompl_perpSub h1).sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, h⟩ := Submodule.mem_sup.mp hz
    exact ⟨a, ha, b, hb, h.symm⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hsplit x
  have hb2 : b ∈ W₂ := by
    have := W₂.sub_mem hx2 (hlt.le ha)
    simpa using this
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx1 (by simpa using ha)
  obtain ⟨y, hy2, hy⟩ := h2.exists_polar_ne_zero hb2 hb0
  obtain ⟨a', ha', b', hb', rfl⟩ := hsplit y
  have hb'2 : b' ∈ W₂ := by
    have := W₂.sub_mem hy2 (hlt.le ha')
    simpa using this
  have hpol : polar Q b b' ≠ 0 := by
    intro h
    apply hy
    rw [polar_add_right, hb a' ha', h, add_zero]
  have hU : 2 ≤ finrank K ↥(W₂ ⊓ perpSub Q W₁) :=
    two_le_finrank_of_polar_ne_zero (W := W₂ ⊓ perpSub Q W₁) ⟨hb2, hb⟩ ⟨hb'2, hb'⟩ hpol
  have hW1 : 2 ≤ finrank K ↥W₁ := two_le_finrank_of_polarNondegOn h1 h0
  have hdisj : W₁ ⊓ (W₂ ⊓ perpSub Q W₁) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, -, hz3⟩
    exact h1 z hz1 fun w hw => hz3 w hw
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂ ⊓ perpSub Q W₁)
  rw [hdisj, finrank_bot] at hsum
  have hle : W₁ ⊔ (W₂ ⊓ perpSub Q W₁) ≤ W₂ := sup_le hlt.le inf_le_left
  have := Submodule.finrank_mono hle
  omega

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
