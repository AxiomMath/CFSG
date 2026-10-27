module

public import CFSG.LieType.SeitzGeneration.OrthHyperRad
public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
structure RootSetup (H : Subgroup (V ≃ₗ[K] V)) (C : Submodule K V) : Prop where
  le_orth : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q
  regular : PolarNondegOn Q C
  decomp : ∀ v : V, ∃ c ∈ C, v - c ∈ qPerp Q C
  eichler_mem : ∀ u ∈ C, ∀ w ∈ C, eichler Q u w ∈ H

theorem isRootCenter_of_stable {H : Subgroup (V ≃ₗ[K] V)} {C : Submodule K V}
    (hS : RootSetup Q H C) {X : Submodule K V} (hXC : X ≤ C) (hX : ∀ x ∈ X, Q x = 0)
    (hrad : ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ H) {x : V} (hx : x ∈ X) (hx0 : x ≠ 0) :
    IsRootCenter Q H x := by
  refine ⟨hx0, hX x hx, fun w hw => ?_⟩
  obtain ⟨c, hc, hd⟩ := hS.decomp w
  have hdX : w - c ∈ qPerp Q X := fun y hy => hd y (hXC hy)
  have hxd : polar Q x (w - c) = 0 := hdX x hx
  have hxc : polar Q x c = 0 := by
    have h : polar Q x w = polar Q x c + polar Q x (w - c) := by
      rw [← polar_add_right]
      congr 1
      abel
    rw [hw, hxd, add_zero] at h
    exact h.symm
  have hsplit : eichler Q x w = eichler Q x c * eichler Q x (w - c) := by
    rw [eichler_mul hxc hxd]
    congr 2
    abel
  rw [hsplit]
  exact H.mul_mem (hS.eichler_mem x (hXC hx) c hc) (hrad x hx _ hdX)

theorem exists_partner_of_polarNondegOn {C : Submodule K V} (hC : PolarNondegOn Q C) {e : V}
    (heC : e ∈ C) (he0 : e ≠ 0) (heQ : Q e = 0) : ∃ f ∈ C, Q f = 0 ∧ polar Q e f = 1 := by
  obtain ⟨g, hgC, hg⟩ := hC.exists_polar_ne_zero heC he0
  obtain ⟨f₀, hf₀C, hf₀⟩ : ∃ f₀ ∈ C, polar Q e f₀ = 1 :=
    ⟨(polar Q e g)⁻¹ • g, C.smul_mem _ hgC, by rw [polar_smul_right_eq, inv_mul_cancel₀ hg]⟩
  have hee : polar Q e e = 0 := polar_self_eq_zero heQ
  refine ⟨f₀ - Q f₀ • e, C.sub_mem hf₀C (C.smul_mem _ heC), ?_, ?_⟩
  · have h1 : Q (f₀ - Q f₀ • e) = Q f₀ + Q (-(Q f₀ • e)) + polar Q f₀ (-(Q f₀ • e)) := by
      rw [sub_eq_add_neg]
      exact QuadraticMap.map_add Q f₀ (-(Q f₀ • e))
    rw [h1, QuadraticMap.map_neg, map_smul_eq_sq, heQ, polar_neg_right, polar_smul_right_eq,
      polar_comm Q f₀ e, hf₀]
    ring
  · rw [polar_sub_right, polar_smul_right_eq, hee, hf₀]
    ring

theorem exists_rootCenter_pair {H : Subgroup (V ≃ₗ[K] V)} {C : Submodule K V}
    (hS : RootSetup Q H C) {𝒜 : Subgroup (V ≃ₗ[K] V)}
    (h𝒜 : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C)
    (hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) → (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) →
      ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ H)
    {X₁ : Submodule K V} (hX₁C : X₁ ≤ C) (hX₁ : ∀ x ∈ X₁, Q x = 0)
    (hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁) {e₀ : V} (he₀ : e₀ ∈ X₁) (he₀0 : e₀ ≠ 0) :
    ∃ a b : V, IsRootCenter Q H a ∧ IsRootCenter Q H b ∧ polar Q a b ≠ 0 := by
  have hroot₀ : IsRootCenter Q H e₀ :=
    isRootCenter_of_stable hS hX₁C hX₁ (hrad X₁ hX₁C hX₁ hX₁𝒜) he₀ he₀0
  have hQe₀ : Q e₀ = 0 := hX₁ e₀ he₀
  have he₀C : e₀ ∈ C := hX₁C he₀
  obtain ⟨f₀, hf₀C, hQf₀, hef₀⟩ := exists_partner_of_polarNondegOn hS.regular he₀C he₀0 hQe₀
  have hee : polar Q e₀ e₀ = 0 := polar_self_eq_zero hQe₀
  have hff : polar Q f₀ f₀ = 0 := polar_self_eq_zero hQf₀
  have hfe : polar Q f₀ e₀ = 1 := by rw [polar_comm, hef₀]
  by_cases hA : ∃ w ∈ C, polar Q f₀ w = 0 ∧ Q w ≠ 0
  · obtain ⟨w₁, hw₁C, hf₀w₁, hQw₁⟩ := hA
    have hgH : eichler Q f₀ w₁ ∈ H := hS.eichler_mem f₀ hf₀C w₁ hw₁C
    refine ⟨e₀, eichler Q f₀ w₁ e₀, hroot₀, hroot₀.map hS.le_orth hgH, ?_⟩
    have h : polar Q e₀ (eichler Q f₀ w₁ e₀) = -Q w₁ := by
      rw [eichler_apply hQf₀ hf₀w₁]
      simp only [polar_add_right, polar_sub_right, polar_smul_right_eq, hee, hef₀]
      ring
    rw [h]
    exact neg_ne_zero.2 hQw₁
  · push Not at hA
    have hcomp : ∀ c ∈ C, (c - polar Q c f₀ • e₀ - polar Q c e₀ • f₀) ∈ C ∧
        polar Q e₀ (c - polar Q c f₀ • e₀ - polar Q c e₀ • f₀) = 0 ∧
        polar Q f₀ (c - polar Q c f₀ • e₀ - polar Q c e₀ • f₀) = 0 := by
      intro c hc
      refine ⟨C.sub_mem (C.sub_mem hc (C.smul_mem _ he₀C)) (C.smul_mem _ hf₀C), ?_, ?_⟩
      · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hee, hef₀,
          polar_comm Q e₀ c]
        ring
      · rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hfe, hff,
          polar_comm Q f₀ c]
        ring
    have hT : ∀ c ∈ C, polar Q e₀ c = 0 → polar Q f₀ c = 0 → c = 0 := by
      intro c' hc'C h1 h2
      refine hS.regular c' hc'C fun c hcC => ?_
      obtain ⟨hc''C, h3, h4⟩ := hcomp c hcC
      set c'' := c - polar Q c f₀ • e₀ - polar Q c e₀ • f₀ with hc''
      have hQc' : Q c' = 0 := hA c' hc'C h2
      have hQc'' : Q c'' = 0 := hA c'' hc''C h4
      have hsum : Q (c' + c'') = 0 :=
        hA _ (C.add_mem hc'C hc''C) (by rw [polar_add_right, h2, h4, add_zero])
      have hpp : polar Q c' c'' = 0 := by
        rw [polar, hsum, hQc', hQc'']
        ring
      have hc : c = polar Q c f₀ • e₀ + polar Q c e₀ • f₀ + c'' := by
        rw [hc'']
        abel
      rw [hc, polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q c' e₀, polar_comm Q c' f₀, h1, h2, hpp]
      ring
    have hdec : ∀ c ∈ C, c = polar Q c f₀ • e₀ + polar Q c e₀ • f₀ := by
      intro c hc
      obtain ⟨hc''C, h3, h4⟩ := hcomp c hc
      have h := hT _ hc''C h3 h4
      rw [sub_sub, sub_eq_zero] at h
      exact h
    have hstab : ∀ a ∈ 𝒜, ∃ y : K, a f₀ = y • f₀ := by
      intro a ha
      have haO := h𝒜 ha
      have haf := hdec _ (hC𝒜 a ha f₀ hf₀C)
      have h2 : polar Q (a e₀) e₀ = 0 := le_qPerp_of_singular hX₁ he₀ _ (hX₁𝒜 a ha e₀ he₀)
      have h1 := hdec _ (hC𝒜 a ha e₀ he₀C)
      rw [h2, zero_smul, add_zero] at h1
      obtain ⟨lam, hlam⟩ : ∃ lam : K, a e₀ = lam • e₀ := ⟨_, h1⟩
      obtain ⟨x, y, hxy⟩ : ∃ x y : K, a f₀ = x • e₀ + y • f₀ := ⟨_, _, haf⟩
      have hiso : lam * y = 1 := by
        have h := polar_map_of_mem haO e₀ f₀
        rw [hlam, hxy, hef₀, polar_smul_left_eq, polar_add_right, polar_smul_right_eq,
          polar_smul_right_eq, hee, hef₀] at h
        linear_combination h
      have hQ : x * y = 0 := by
        have h := map_of_mem haO f₀
        rw [hxy, hQf₀, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQe₀, hQf₀,
          polar_smul_left_eq, polar_smul_right_eq, hef₀] at h
        linear_combination h
      have hy0 : y ≠ 0 := fun h0 => by
        rw [h0, mul_zero] at hiso
        exact zero_ne_one hiso
      have hx0 : x = 0 := (mul_eq_zero.1 hQ).resolve_right hy0
      exact ⟨y, by rw [hxy, hx0, zero_smul, zero_add]⟩
    set X₂ : Submodule K V := Submodule.span K {f₀} with hX₂
    have hX₂C : X₂ ≤ C := Submodule.span_le.2 (Set.singleton_subset_iff.2 hf₀C)
    have hX₂Q : ∀ x ∈ X₂, Q x = 0 := by
      intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul_eq_sq, hQf₀, mul_zero]
    have hX₂𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₂, a x ∈ X₂ := by
      intro a ha x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨y, hy⟩ := hstab a ha
      rw [map_smul, hy, smul_smul]
      exact X₂.smul_mem _ (Submodule.mem_span_singleton_self f₀)
    have hf₀X₂ : f₀ ∈ X₂ := Submodule.mem_span_singleton_self f₀
    have hf₀0 : f₀ ≠ 0 := by
      intro h0
      rw [h0, polar_zero_right Q e₀] at hef₀
      exact zero_ne_one hef₀
    refine ⟨e₀, f₀, hroot₀,
      isRootCenter_of_stable hS hX₂C hX₂Q (hrad X₂ hX₂C hX₂Q hX₂𝒜) hf₀X₂ hf₀0, ?_⟩
    rw [hef₀]
    exact one_ne_zero

end CFSG.LieType.SeitzGeneration
