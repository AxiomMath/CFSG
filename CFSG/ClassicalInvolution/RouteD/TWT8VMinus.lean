module

public import CFSG.ClassicalInvolution.RouteD.TWT8V

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Planes

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem plane_aniso_of_orth (h2 : (2 : K) ≠ 0) {u v : V} (huv : polar Q u v = 0) {a b : K}
    (hQu : Q u = a) (hQv : Q v = b) (ha : a ≠ 0) (hb : b ≠ 0) (hδ : ¬ IsSquare (-b / a)) :
    Module.finrank K (Submodule.span K {u, v}) = 2 ∧
      ¬ HasSingularVector Q (Submodule.span K {u, v}) := by
  have hQ2 : ∀ s t : K, Q (s • u + t • v) = s ^ 2 * a + t ^ 2 * b := by
    intro s t
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, huv, hQu, hQv]
    ring
  have hind : ∀ s t : K, s • u + t • v = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h1 : polar Q u (s • u + t • v) = 0 := by rw [h, polar_zero_right]
    have h3 : polar Q v (s • u + t • v) = 0 := by rw [h, polar_zero_right]
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, huv, polar_self_eq_two_mul,
      hQu] at h1
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q v u, huv,
      polar_self_eq_two_mul, hQv] at h3
    refine ⟨?_, ?_⟩
    · have : s * (2 * a) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h2 ha)
    · have : t * (2 * b) = 0 := by linear_combination h3
      exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h2 hb)
  have hli : LinearIndependent K ![u, v] := by
    rw [LinearIndependent.pair_iff]
    exact hind
  have hspan : Submodule.span K {u, v} = Submodule.span K (Set.range ![u, v]) := by
    congr 1
    ext x
    simp [eq_comm]
    tauto
  refine ⟨?_, ?_⟩
  · rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]
  · rintro ⟨x, hx, hx0, hQx⟩
    rw [Submodule.mem_span_pair] at hx
    obtain ⟨s, t, rfl⟩ := hx
    rw [hQ2] at hQx
    by_cases ht : t = 0
    · subst ht
      have : s ^ 2 * a = 0 := by simpa using hQx
      have hs : s = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
        · exact absurd h ha
      subst hs
      exact hx0 (by simp)
    · apply hδ
      refine ⟨s / t, ?_⟩
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      field_simp
      linear_combination -hQx

theorem Q_e_add_smul_f (P : HypPair Q) (t : K) : Q (P.e + t • P.f) = t := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, P.Q_e, P.Q_f, P.polar_ef]
  ring

theorem polar_e_add_smul_f (P : HypPair Q) (s t : K) :
    polar Q (P.e + s • P.f) (P.e + t • P.f) = s + t := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P.polar_ee, P.polar_ef, P.polar_fe, P.polar_ff]
  ring

theorem exists_aniso_planes_in_frame (h2 : (2 : K) ≠ 0) (c₃ c₄ : HypPair Q) (o : c₃.Orth c₄) :
    ∃ A A' : Submodule K V, Module.finrank K A = 2 ∧ Module.finrank K A' = 2 ∧
      ¬ HasSingularVector Q A ∧ ¬ HasSingularVector Q A' ∧
      (∀ x ∈ A, ∀ y ∈ A', polar Q x y = 0) ∧ A ⊔ A' = hypPlane c₃ ⊔ hypPlane c₄ := by
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := (ringChar.spec K 2).mpr (by rw [h])
    simpa using this
  obtain ⟨δ, hδ⟩ := FiniteField.exists_nonsquare hchar
  have hδ0 : δ ≠ 0 := fun h => hδ ⟨0, by simp [h]⟩
  set u₁ : V := c₃.e + (1 : K) • c₃.f with hu₁
  set u₂ : V := c₃.e + (-1 : K) • c₃.f with hu₂
  set v₁ : V := c₄.e + (-δ) • c₄.f with hv₁
  set v₂ : V := c₄.e + δ • c₄.f with hv₂
  have hu₁m : u₁ ∈ hypPlane c₃ := Submodule.add_mem _ (e_mem_hypPlane _)
    (Submodule.smul_mem _ _ (f_mem_hypPlane _))
  have hu₂m : u₂ ∈ hypPlane c₃ := Submodule.add_mem _ (e_mem_hypPlane _)
    (Submodule.smul_mem _ _ (f_mem_hypPlane _))
  have hv₁m : v₁ ∈ hypPlane c₄ := Submodule.add_mem _ (e_mem_hypPlane _)
    (Submodule.smul_mem _ _ (f_mem_hypPlane _))
  have hv₂m : v₂ ∈ hypPlane c₄ := Submodule.add_mem _ (e_mem_hypPlane _)
    (Submodule.smul_mem _ _ (f_mem_hypPlane _))
  have o34 := polar_hypPlane_of_orth o
  have o43 : ∀ x ∈ hypPlane c₄, ∀ y ∈ hypPlane c₃, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]
    exact o34 y hy x hx
  have e₁₂ : polar Q u₁ u₂ = 0 := by
    rw [hu₁, hu₂, polar_e_add_smul_f]
    ring
  have e₃₄ : polar Q v₁ v₂ = 0 := by
    rw [hv₁, hv₂, polar_e_add_smul_f]
    ring
  have hA := plane_aniso_of_orth h2 (u := u₁) (v := v₁) (a := 1) (b := -δ) (o34 _ hu₁m _ hv₁m)
    (by rw [hu₁, Q_e_add_smul_f]) (by rw [hv₁, Q_e_add_smul_f]) one_ne_zero (neg_ne_zero.mpr hδ0)
    (by simpa using hδ)
  have hA' := plane_aniso_of_orth h2 (u := u₂) (v := v₂) (a := -1) (b := δ) (o34 _ hu₂m _ hv₂m)
    (by rw [hu₂, Q_e_add_smul_f]) (by rw [hv₂, Q_e_add_smul_f]) (by norm_num) hδ0
    (by simpa using hδ)
  refine ⟨Submodule.span K {u₁, v₁}, Submodule.span K {u₂, v₂}, hA.1, hA'.1, hA.2, hA'.2, ?_, ?_⟩
  · intro x hx y hy
    rw [Submodule.mem_span_pair] at hx hy
    obtain ⟨s, t, rfl⟩ := hx
    obtain ⟨s', t', rfl⟩ := hy
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, e₁₂, e₃₄,
      o34 _ hu₁m _ hv₂m, o43 _ hv₁m _ hu₂m]
    ring
  · apply le_antisymm
    · exact sup_le
        (Submodule.span_le.mpr (by
          rintro x (rfl | rfl)
          · exact Submodule.mem_sup_left hu₁m
          · exact Submodule.mem_sup_right hv₁m))
        (Submodule.span_le.mpr (by
          rintro x (rfl | rfl)
          · exact Submodule.mem_sup_left hu₂m
          · exact Submodule.mem_sup_right hv₂m))
    · have hu₁A : u₁ ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} :=
        Submodule.mem_sup_left (Submodule.subset_span (by simp))
      have hv₁A : v₁ ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} :=
        Submodule.mem_sup_left (Submodule.subset_span (by simp))
      have hu₂A : u₂ ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} :=
        Submodule.mem_sup_right (Submodule.subset_span (by simp))
      have hv₂A : v₂ ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} :=
        Submodule.mem_sup_right (Submodule.subset_span (by simp))
      have he₃ : c₃.e ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} := by
        have : c₃.e = (2 : K)⁻¹ • u₁ + (2 : K)⁻¹ • u₂ := by
          have : (2 : K)⁻¹ • u₁ + (2 : K)⁻¹ • u₂ = ((2 : K)⁻¹ * 2) • c₃.e := by
            rw [hu₁, hu₂]
            module
          rw [this, inv_mul_cancel₀ h2, one_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu₁A) (Submodule.smul_mem _ _ hu₂A)
      have hf₃ : c₃.f ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} := by
        have : c₃.f = (2 : K)⁻¹ • u₁ + (-(2 : K)⁻¹) • u₂ := by
          have : (2 : K)⁻¹ • u₁ + (-(2 : K)⁻¹) • u₂ = ((2 : K)⁻¹ * 2) • c₃.f := by
            rw [hu₁, hu₂]
            module
          rw [this, inv_mul_cancel₀ h2, one_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu₁A) (Submodule.smul_mem _ _ hu₂A)
      have he₄ : c₄.e ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} := by
        have : c₄.e = (2 : K)⁻¹ • v₁ + (2 : K)⁻¹ • v₂ := by
          have : (2 : K)⁻¹ • v₁ + (2 : K)⁻¹ • v₂ = ((2 : K)⁻¹ * 2) • c₄.e := by
            rw [hv₁, hv₂]
            module
          rw [this, inv_mul_cancel₀ h2, one_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv₁A) (Submodule.smul_mem _ _ hv₂A)
      have hf₄ : c₄.f ∈ Submodule.span K {u₁, v₁} ⊔ Submodule.span K {u₂, v₂} := by
        have : c₄.f = (-(2 * δ)⁻¹) • v₁ + ((2 * δ)⁻¹) • v₂ := by
          have h2δ : (2 * δ) ≠ 0 := mul_ne_zero h2 hδ0
          have : (-(2 * δ)⁻¹) • v₁ + ((2 * δ)⁻¹) • v₂ = ((2 * δ)⁻¹ * (2 * δ)) • c₄.f := by
            rw [hv₁, hv₂]
            module
          rw [this, inv_mul_cancel₀ h2δ, one_smul]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv₁A) (Submodule.smul_mem _ _ hv₂A)
      refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
      · rintro x (rfl | rfl)
        · exact he₃
        · exact hf₃
      · rintro x (rfl | rfl)
        · exact he₄
        · exact hf₄

theorem polarNondegOn_of_aniso (h2 : (2 : K) ≠ 0) {P : Submodule K V}
    (hs : ¬ HasSingularVector Q P) : PolarNondegOn Q P := by
  intro x hx h
  by_contra hx0
  apply hs
  refine ⟨x, hx, hx0, ?_⟩
  have h1 := h x hx
  rw [polar_self_eq_two_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left h2

end Planes

section Frames

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {K' : Type} [Field K'] [Algebra K K'] {σ : K' ≃+* K'}

theorem exists_frames_of_aniso_planes (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0)
    {P₁ P₂ P₃ : Submodule K V} (h₁ : Module.finrank K P₁ = 2) (h₂ : Module.finrank K P₂ = 2)
    (h₃ : Module.finrank K P₃ = 2) (hs₁ : ¬ HasSingularVector Q P₁)
    (hs₂ : ¬ HasSingularVector Q P₂) (hs₃ : ¬ HasSingularVector Q P₃)
    (o₁₂ : ∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0) (o₁₃ : ∀ x ∈ P₁, ∀ y ∈ P₃, polar Q x y = 0)
    (o₂₃ : ∀ x ∈ P₂, ∀ y ∈ P₃, polar Q x y = 0) :
    ∃ F₁ F₂ : OFrame Q, F₁.span = P₁ ⊔ P₂ ∧ F₂.span = P₂ ⊔ P₃ := by
  obtain ⟨φ₁, hφ₁, -, hQ₁⟩ := E.exists_normIso h2 h₁ hs₁
  obtain ⟨φ₂, hφ₂, -, hQ₂⟩ := E.exists_normIso h2 h₂ hs₂
  obtain ⟨φ₃, hφ₃, -, hQ₃⟩ := E.exists_normIso h2 h₃ hs₃
  have o12 : ∀ x y, polar Q (φ₁ x) (φ₂ y) = 0 := fun x y => o₁₂ _ (hφ₁ x) _ (hφ₂ y)
  have o13 : ∀ x y, polar Q (φ₁ x) (φ₃ y) = 0 := fun x y => o₁₃ _ (hφ₁ x) _ (hφ₃ y)
  have o23 : ∀ x y, polar Q (φ₂ x) (φ₃ y) = 0 := fun x y => o₂₃ _ (hφ₂ x) _ (hφ₃ y)
  let T : NormTriple Q σ :=
    { φ := ![φ₁, φ₂, φ₃]
      Q_φ := fun j x => by fin_cases j <;> simp [hQ₁, hQ₂, hQ₃]
      orth := fun j k hjk x y => by
        fin_cases j <;> fin_cases k
        · exact absurd rfl hjk
        · exact o12 x y
        · exact o13 x y
        · rw [polar_comm]; exact o12 y x
        · exact absurd rfl hjk
        · exact o23 x y
        · rw [polar_comm]; exact o13 y x
        · rw [polar_comm]; exact o23 y x
        · exact absurd rfl hjk }
  let D := T.toEmbedding E.isUnitary
  obtain ⟨W⟩ := E.isUnitary.nonempty_wittData
  have hnd₁ := polarNondegOn_of_aniso h2 hs₁
  have hnd₂ := polarNondegOn_of_aniso h2 hs₂
  have hnd₃ := polarNondegOn_of_aniso h2 hs₃
  have hdim₁₂ : Module.finrank K ↥(P₁ ⊔ P₂) = 4 := by
    have hd : Disjoint P₁ P₂ := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      exact hnd₁ x hx fun y hy => by rw [polar_comm]; exact o₁₂ y hy x hx'
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hd, h₁, h₂]
  have hdim₂₃ : Module.finrank K ↥(P₂ ⊔ P₃) = 4 := by
    have hd : Disjoint P₂ P₃ := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      exact hnd₂ x hx fun y hy => by rw [polar_comm]; exact o₂₃ y hy x hx'
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint hd, h₂, h₃]
  refine ⟨D.hypFrame E h2 (HypBasis.ofWitt W 2), D.hypFrame E h2 (HypBasis.ofWitt W 0), ?_, ?_⟩
  · refine Frame.frame_span_eq (D.hypFrame_span_le_of_coord E h2 W 2 fun x hx => ?_) hdim₁₂
    show T.incl x ∈ P₁ ⊔ P₂
    rw [T.incl_apply, hx, map_zero, add_zero]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hφ₁ _)) (Submodule.mem_sup_right (hφ₂ _))
  · refine Frame.frame_span_eq (D.hypFrame_span_le_of_coord E h2 W 0 fun x hx => ?_) hdim₂₃
    show T.incl x ∈ P₂ ⊔ P₃
    rw [T.incl_apply, hx]
    have : T.φ 0 0 = 0 := map_zero _
    rw [this, zero_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hφ₂ _)) (Submodule.mem_sup_right (hφ₃ _))

theorem exists_bridge_minus (hodd : Odd (Nat.card K)) (E : QuadExt K K' σ) (c₃ c₄ : HypPair Q)
    (o : c₃.Orth c₄) {Z : Submodule K V} (hZ2 : Module.finrank K Z = 2)
    (hZs : ¬ HasSingularVector Q Z) (hZ₃ : ∀ x ∈ hypPlane c₃, ∀ y ∈ Z, polar Q x y = 0)
    (hZ₄ : ∀ x ∈ hypPlane c₄, ∀ y ∈ Z, polar Q x y = 0) :
    ∃ F₁ F₂ : OFrame Q, BridgeOmega Q F₁.La.range F₂.La.range ∧
      F₁.span ≤ hypPlane c₃ ⊔ hypPlane c₄ ⊔ Z ∧ F₂.span ≤ hypPlane c₃ ⊔ hypPlane c₄ ⊔ Z := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨A, A', hA2, hA'2, hAs, hA's, hAA', hsum⟩ := exists_aniso_planes_in_frame h2 c₃ c₄ o
  have hAle : A ≤ hypPlane c₃ ⊔ hypPlane c₄ := hsum ▸ le_sup_left
  have hA'le : A' ≤ hypPlane c₃ ⊔ hypPlane c₄ := hsum ▸ le_sup_right
  have horthZ : ∀ x ∈ hypPlane c₃ ⊔ hypPlane c₄, ∀ y ∈ Z, polar Q x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, hZ₃ a ha y hy, hZ₄ b hb y hy, add_zero]
  obtain ⟨F₁, F₂, hF₁, hF₂⟩ := exists_frames_of_aniso_planes E h2 hA2 hA'2 hZ2 hAs hA's hZs hAA'
    (fun x hx y hy => horthZ x (hAle hx) y hy) (fun x hx y hy => horthZ x (hA'le hx) y hy)
  refine ⟨F₁, F₂, (bridgeOmega_of_planes hodd (polarNondegOn_of_aniso h2 hAs)
    (polarNondegOn_of_aniso h2 hA's) hA2 hA'2 hZ2 hAA'
    (fun x hx y hy => horthZ x (hAle hx) y hy) (fun x hx y hy => horthZ x (hA'le hx) y hy)
    hF₁ hF₂).1, ?_, ?_⟩
  · rw [hF₁, hsum]
    exact le_sup_left
  · rw [hF₂]
    exact sup_le (hA'le.trans le_sup_left) le_sup_right

end Frames

end CFSG.ClassicalInvolution.RouteD.TWT8
