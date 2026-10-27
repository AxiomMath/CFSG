module

public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.LargeExtraspecial.S3bTenGeom
public import CFSG.LargeExtraspecial.S4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

section Forms

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem eq_of_add_eq_zero' {x y : U} (h : x + y = 0) : y = x := by
  have := eq_neg_of_add_eq_zero_right h
  rwa [vec_neg] at this

theorem exists_ne_zero_q_eq_zero (Q : QuadraticForm (ZMod 2) U) {W : Submodule (ZMod 2) U}
    [FiniteDimensional (ZMod 2) W] (hW : 3 ≤ finrank (ZMod 2) W) :
    ∃ x ∈ W, x ≠ 0 ∧ Q x = 0 := by
  by_contra hcon
  push Not at hcon
  have hQ : ∀ x ∈ W, x ≠ 0 → Q x = 1 := fun x hx hx0 => zmod2_eq_one_of_ne_zero (hcon x hx hx0)
  obtain ⟨u₁, hu₁W, hu₁⟩ : ∃ u ∈ W, u ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot fun h => by
      rw [h, finrank_bot] at hW
      omega
  have hlt1 : (ZMod 2) ∙ u₁ < W := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hu₁W) fun h => ?_
    have h1 := finrank_span_le_card (R := ZMod 2) ({u₁} : Set U)
    rw [Set.toFinset_singleton, Finset.card_singleton, h] at h1
    omega
  obtain ⟨u₂, hu₂W, hu₂⟩ := IsConcreteLE.exists_of_lt hlt1
  have hle2 : Submodule.span (ZMod 2) ({u₁, u₂} : Set U) ≤ W := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    exacts [hu₁W, hu₂W]
  have hlt2 : Submodule.span (ZMod 2) ({u₁, u₂} : Set U) < W := by
    refine lt_of_le_of_ne hle2 fun h => ?_
    have h1 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({u₁, u₂} : Set U)) ≤ 2 := by
      rw [Submodule.span_insert]
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have h2 := finrank_span_le_card (R := ZMod 2) ({u₁} : Set U)
      have h3 := finrank_span_le_card (R := ZMod 2) ({u₂} : Set U)
      simp only [Set.toFinset_singleton, Finset.card_singleton] at h2 h3
      omega
    rw [h] at h1
    omega
  obtain ⟨u₃, hu₃W, hu₃⟩ := IsConcreteLE.exists_of_lt hlt2
  have hm1 : u₁ ∈ Submodule.span (ZMod 2) ({u₁, u₂} : Set U) := Submodule.subset_span (by simp)
  have hm2 : u₂ ∈ Submodule.span (ZMod 2) ({u₁, u₂} : Set U) := Submodule.subset_span (by simp)
  have hn2 : u₂ ≠ 0 := fun h => hu₂ (h ▸ Submodule.zero_mem _)
  have hn3 : u₃ ≠ 0 := fun h => hu₃ (h ▸ Submodule.zero_mem _)
  have hn12 : u₁ + u₂ ≠ 0 := fun h =>
    hu₂ (eq_of_add_eq_zero' h ▸ Submodule.mem_span_singleton_self _)
  have hn13 : u₁ + u₃ ≠ 0 := fun h => hu₃ (eq_of_add_eq_zero' h ▸ hm1)
  have hn23 : u₂ + u₃ ≠ 0 := fun h => hu₃ (eq_of_add_eq_zero' h ▸ hm2)
  have hn123 : u₁ + u₂ + u₃ ≠ 0 := fun h => hu₃ (eq_of_add_eq_zero' h ▸ add_mem hm1 hm2)
  exact false_of_three_anisotropic (hQ _ hu₁W hu₁) (hQ _ hu₂W hn2) (hQ _ hu₃W hn3)
    (hQ _ (add_mem hu₁W hu₂W) hn12) (hQ _ (add_mem hu₁W hu₃W) hn13)
    (hQ _ (add_mem hu₂W hu₃W) hn23) (hQ _ (add_mem (add_mem hu₁W hu₂W) hu₃W) hn123)

theorem exists_hyperbolic_pair [FiniteDimensional (ZMod 2) U] {Q : QuadraticForm (ZMod 2) U}
    (hnd : Q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) U}
    (hF : finrank (ZMod 2) U < 2 * finrank (ZMod 2) F) {d : U} (hdF : d ∈ F) (hQd : Q d = 1)
    (hFd : ∀ v ∈ F, polar Q v d = 0) :
    ∃ u ∈ F, ∃ w ∈ F, Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 1 := by
  obtain ⟨u, hu, w, hw, huw⟩ : ∃ u ∈ F, ∃ w ∈ F, polar Q u w = 1 := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ LinearMap.BilinForm.orthogonal Q.polarBilin F := by
      intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [polarBilin_apply_apply]
      rcases zmod2_eq_zero_or_eq_one (polar Q u v) with h | h
      · exact h
      · exact absurd h (hcon u hu v hv)
    have h1 := Submodule.finrank_mono hle
    rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    omega
  have hdd : polar Q d d = 0 := polar_self_eq_zero Q d
  have hsing : ∀ v ∈ F, Q (v + Q v • d) = 0 := by
    intro v hv
    rw [map_add_eq, map_smul_zmod2, hQd, mul_one, polar_smul_right, hFd v hv, smul_zero,
      add_zero, zmod2_add_self]
  refine ⟨u + Q u • d, add_mem hu (Submodule.smul_mem _ _ hdF), w + Q w • d,
    add_mem hw (Submodule.smul_mem _ _ hdF), hsing u hu, hsing w hw, ?_⟩
  rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_right, polar_smul_left,
    polar_smul_left, polar_smul_right, hFd u hu, polar_comm Q d w, hFd w hw, hdd]
  simp [huw]

theorem finrank_ker_add_one [FiniteDimensional (ZMod 2) U] {β : LinearMap.BilinForm (ZMod 2) U}
    (hnd : β.Nondegenerate) {c : U} (hc : c ≠ 0) :
    finrank (ZMod 2) (LinearMap.ker (β c)) + 1 = finrank (ZMod 2) U := by
  obtain ⟨y, hy⟩ : ∃ y, β c y ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (hnd.1 c h)
  have hy1 := zmod2_eq_one_of_ne_zero hy
  have hrange : LinearMap.range (β c) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro e
    exact ⟨e • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (β c)
  rw [hrange, finrank_top, finrank_self] at h1
  omega

theorem finrank_le_finrank_add_one_of_add_mem [FiniteDimensional (ZMod 2) U]
    {F₀ F : Submodule (ZMod 2) U} (hle : F₀ ≤ F)
    (h : ∀ v ∈ F, ∀ w ∈ F, v ∉ F₀ → w ∉ F₀ → v + w ∈ F₀) :
    finrank (ZMod 2) F ≤ finrank (ZMod 2) F₀ + 1 := by
  by_cases hF : F ≤ F₀
  · rw [le_antisymm hF hle]
    omega
  obtain ⟨v₀, hv₀F, hv₀⟩ := Set.not_subset.mp hF
  have hsup : F ≤ F₀ ⊔ (ZMod 2) ∙ v₀ := by
    intro v hv
    by_cases hvF : v ∈ F₀
    · exact Submodule.mem_sup_left hvF
    · have h1 := h v hv v₀ hv₀F hvF hv₀
      have e : v = (v + v₀) + v₀ := by rw [add_assoc, vec_add_self, add_zero]
      rw [e]
      exact add_mem (Submodule.mem_sup_left h1)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
  have h1 := Submodule.finrank_mono hsup
  have h2 := Submodule.finrank_add_le_finrank_add_finrank F₀ ((ZMod 2) ∙ v₀)
  have h3 := finrank_span_le_card (R := ZMod 2) ({v₀} : Set U)
  rw [Set.toFinset_singleton, Finset.card_singleton] at h3
  omega

end Forms

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem exists_swap_of_mem_Qa {g₁ c : G} (haQ : g₁ * S.z * g₁⁻¹ ∈ S.QG) (hcQ : c ∈ S.QG)
    (haz : g₁ * S.z * g₁⁻¹ ≠ S.z) (hcz : c ≠ S.z) (hconj : ∃ g₂ : G, g₂ * S.z * g₂⁻¹ = c)
    (hcQa : c ∈ S.Qa g₁) (hca : c ≠ g₁ * S.z * g₁⁻¹) (hcaz : c ≠ g₁ * S.z * g₁⁻¹ * S.z) :
    ∃ k : G, k * S.z * k⁻¹ = g₁ * S.z * g₁⁻¹ * c ∧
      ∃ y ∈ S.Qa k, y ∈ S.M ∧ y * (g₁ * S.z * g₁⁻¹) * y⁻¹ = c := by
  obtain ⟨g₂, hg₂⟩ := hconj
  set a := g₁ * S.z * g₁⁻¹ with ha
  set T := S.conjBy g₁ with hT
  have hTz : T.z = a := rfl
  have hc1 : c ≠ 1 := by
    rw [← hg₂]
    exact conj_z_ne_one S g₂
  have ha2 : a * a = 1 := by
    rw [← hTz]
    exact T.z_mul_z
  have hac : c * a = a * c := T.mem_M_iff.mp (T.QG_le_M hcQa)
  have hgc : (g₂ * g₁⁻¹) * T.z * (g₂ * g₁⁻¹)⁻¹ = c := by
    rw [hTz, ha, ← hg₂]
    group
  have hca' : c * T.z ≠ T.z := fun h => hc1 (by
    calc c = c * T.z * T.z⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  obtain ⟨u, -, hua, -⟩ := (T.lemma_3_8_1 hgc hcQa (by rw [hTz]; exact hca)).2 (c * T.z)
    (by simp) T.z (by simp) hca'
  set k := u * g₁ with hk
  have hkz : k * S.z * k⁻¹ = a * c := by
    rw [hk, show u * g₁ * S.z * (u * g₁)⁻¹ = u * (g₁ * S.z * g₁⁻¹) * u⁻¹ by group, ← ha,
      ← hTz, hua, hTz, hac]
  refine ⟨k, hkz, ?_⟩
  have hacQ : a * c ∈ S.QG := S.QG.mul_mem haQ hcQ
  have hac_a : k * S.z * k⁻¹ ≠ g₁ * S.z * g₁⁻¹ := by
    rw [hkz]
    intro h
    apply hc1
    calc c = a⁻¹ * (a * c) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hacz : k * S.z * k⁻¹ ≠ S.z := by
    rw [hkz]
    intro h
    apply hcaz
    calc c = a * (a * c) := by rw [← mul_assoc, ha2, one_mul]
      _ = a * S.z := by rw [h]
  have hacQa : k * S.z * k⁻¹ ∈ S.Qa g₁ := by
    rw [hkz]
    exact mul_mem T.z_mem_QG hcQa
  have haQk : a ∈ S.Qa k := S.mem_Qa_symm hac_a hacQa
  have hzQk : S.z ∈ S.Qa k := S.z_mem_Qa (by rw [hkz]; exact hacQ) hacz
  set T' := S.conjBy k with hT'
  have hT'z : T'.z = a * c := hkz
  obtain ⟨y, hy, hyz, hya⟩ := T'.exists_conj_eq_mul_z_of_commute haQk hzQk
    (conj_z_ne_one S g₁) (by rw [hT'z]; exact fun h => hac_a (hkz.trans h.symm))
    (fun h => haz h.symm) (by
      rw [hT'z, ← mul_assoc, ha2, one_mul]
      exact fun h => hcz h.symm)
  refine ⟨y, hy, S.mem_M_iff.mpr hyz, ?_⟩
  rw [hya, hT'z, ← mul_assoc, ha2, one_mul]

end CFSG.LargeExtraspecial.S6
