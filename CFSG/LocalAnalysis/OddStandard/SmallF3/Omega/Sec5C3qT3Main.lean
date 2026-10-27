module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qN1Red
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qT3Cas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem sec5c3q_inv3_ncard_le [FiniteDimensional (ZMod 3) V] (hV : finrank (ZMod 3) V = 6)
    (S : Set (Module.End (ZMod 3) V)) (hsq : ∀ t ∈ S, t * t = 1)
    (hdim : ∀ t ∈ S, finrank (ZMod 3) (LinearMap.range (t - 1)) = 3)
    (hcomm : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t ∨ t * t' = -(t' * t)) : S.ncard ≤ 20 := by
  classical
  haveI := sec5c3q_finite_end (V := V)
  by_cases hall : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t
  · have h := sec5c3q_card_le_choose (fun t : S => (t : Module.End (ZMod 3) V))
      (fun i j => hall i i.2 j j.2) (fun i => hsq i i.2) Subtype.val_injective 3
      (fun i => hdim i i.2)
    rw [hV] at h
    calc S.ncard = Nat.card S := (Nat.card_coe_set_eq S).symm
      _ ≤ Nat.choose 6 3 := h
      _ = 20 := by decide
  · push Not at hall
    obtain ⟨T₁, hT₁, T₂, hT₂, hne⟩ := hall
    have h12 : T₁ * T₂ = -(T₂ * T₁) := (hcomm T₁ hT₁ T₂ hT₂).resolve_left hne
    have := sec5c3q_caseB_ncard_le S hV hsq hdim hcomm hT₁ hT₂ h12
    omega

theorem sec5c3q_neg_dim [FiniteDimensional (ZMod 3) V] (hV : finrank (ZMod 3) V = 6)
    {T : Module.End (ZMod 3) V} (hT : T * T = 1)
    (hd : finrank (ZMod 3) (LinearMap.range (T - 1)) = 3) :
    finrank (ZMod 3) (LinearMap.range (-T - 1)) = 3 := by
  have h1 : -T - 1 = -(T + 1) := by abel
  rw [h1, LinearMap.range_neg]
  have h2 := LinearMap.finrank_range_add_finrank_ker (T + 1)
  rw [← sec5c3q_range_sub_one hT, hd, hV] at h2
  omega

theorem sec5c3q_cs_neg_left {R : Type*} [Ring R] {a b : R}
    (h : a * b = b * a ∨ a * b = -(b * a)) :
    (-a) * b = b * (-a) ∨ (-a) * b = -(b * (-a)) := by
  rcases h with h | h
  · left
    rw [neg_mul, mul_neg, h]
  · right
    rw [neg_mul, mul_neg, neg_neg, h, neg_neg]

theorem sec5c3q_cs_neg_right {R : Type*} [Ring R] {a b : R}
    (h : a * b = b * a ∨ a * b = -(b * a)) :
    a * (-b) = (-b) * a ∨ a * (-b) = -((-b) * a) := by
  rcases h with h | h
  · left
    rw [neg_mul, mul_neg, h]
  · right
    rw [neg_mul, mul_neg, neg_neg, h, neg_neg]

variable {Q : QuadraticForm (ZMod 3) V} [FiniteDimensional (ZMod 3) V]

@[expose] noncomputable def sec5c3q_end (t : OGroup Q) : Module.End (ZMod 3) V :=
  ((t : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)

theorem sec5c3q_end_mul (a b : OGroup Q) :
    sec5c3q_end (a * b) = sec5c3q_end a * sec5c3q_end b := rfl

theorem sec5c3q_end_injective : Function.Injective (sec5c3q_end (Q := Q)) := fun a b h =>
  Subtype.ext (LinearEquiv.toLinearMap_injective h)

theorem sec5c3q_end_piOrth : sec5c3q_end (piOrth Q) = -1 := by
  apply LinearMap.ext
  intro v
  exact coe_piOrth_apply v

theorem sec5c3q_end_invDim (t : OGroup Q) :
    finrank (ZMod 3) (LinearMap.range (sec5c3q_end t - 1)) = invDim t := rfl

theorem sec5c3q_lift_comm {x x' : ProjSim Q} (hxx' : x * x' = x' * x) {t t' : OGroup Q}
    (ht : projOrthToProjSim Q (toProj Q t) = x) (ht' : projOrthToProjSim Q (toProj Q t') = x') :
    sec5c3q_end t * sec5c3q_end t' = sec5c3q_end t' * sec5c3q_end t ∨
      sec5c3q_end t * sec5c3q_end t' = -(sec5c3q_end t' * sec5c3q_end t) := by
  have h1 : projOrthToProjSim Q (toProj Q (t * t')) =
      projOrthToProjSim Q (toProj Q (t' * t)) := by
    rw [map_mul, map_mul, map_mul, map_mul, ht, ht', hxx']
  have h2 : toProj Q (t * t') = toProj Q (t' * t) := projOrthToProjSim_injective h1
  have h3 : (t * t')⁻¹ * (t' * t) ∈ piGroup Q := QuotientGroup.eq.mp h2
  rcases mem_piGroup_iff.mp h3 with h | h
  · left
    have h4 : t * t' = t' * t := inv_mul_eq_one.mp h
    rw [← sec5c3q_end_mul, ← sec5c3q_end_mul, h4]
  · right
    have h4 : t' * t = (t * t') * piOrth Q := inv_mul_eq_iff_eq_mul.mp h
    have h5 : sec5c3q_end t' * sec5c3q_end t = -(sec5c3q_end t * sec5c3q_end t') := by
      calc sec5c3q_end t' * sec5c3q_end t = sec5c3q_end (t' * t) := (sec5c3q_end_mul _ _).symm
        _ = sec5c3q_end ((t * t') * piOrth Q) := by rw [← h4]
        _ = (sec5c3q_end t * sec5c3q_end t') * sec5c3q_end (piOrth Q) := by
          rw [sec5c3q_end_mul, sec5c3q_end_mul]
        _ = -(sec5c3q_end t * sec5c3q_end t') := by rw [sec5c3q_end_piOrth, mul_neg, mul_one]
    rw [h5, neg_neg]

theorem asc82Type3Bound_holds : Asc82Type3Bound := by
  intro V _ _ _ Q _ hV6 _ F hF
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI := sec5c3q_finite_end (V := V)
  have hpos : 0 < finrank (ZMod 3) V := by omega
  set X : Set (ProjSim Q) := {x | x ∈ F ∧ SimHasDim x 3} with hX
  have hex : ∀ x ∈ X, ∃ t : OGroup Q, t * t = 1 ∧ invDim t = 3 ∧
      projOrthToProjSim Q (toProj Q t) = x := fun x hx => hx.2
  choose! L hL using hex
  have hproj : ∀ x ∈ X, ∀ x' ∈ X, toProj Q (L x) = toProj Q (L x') → x = x' := by
    intro x hx x' hx' h
    calc x = projOrthToProjSim Q (toProj Q (L x)) := ((hL x hx).2.2).symm
      _ = projOrthToProjSim Q (toProj Q (L x')) := by rw [h]
      _ = x' := (hL x' hx').2.2
  set A : Set (Module.End (ZMod 3) V) := (fun x => sec5c3q_end (L x)) '' X with hA
  set N : Set (Module.End (ZMod 3) V) := (fun T => -T) '' A with hN
  have hAinj : Set.InjOn (fun x => sec5c3q_end (L x)) X := fun x hx x' hx' h =>
    hproj x hx x' hx' (by rw [sec5c3q_end_injective h])
  have hAcard : A.ncard = X.ncard := hAinj.ncard_image
  have hNcard : N.ncard = A.ncard := Set.ncard_image_of_injective A neg_injective
  have hdisj : Disjoint A N := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨_, ⟨x', hx', rfl⟩, h⟩
    have h1 : sec5c3q_end (L x) = sec5c3q_end (piOrth Q * L x') := by
      rw [sec5c3q_end_mul, sec5c3q_end_piOrth, neg_one_mul]
      exact h.symm
    have h2 : L x = piOrth Q * L x' := sec5c3q_end_injective h1
    have h3 : toProj Q (L x) = toProj Q (L x') := by
      rw [h2, map_mul, toProj_piOrth, one_mul]
    have hxx : x = x' := hproj x hx x' hx' h3
    subst hxx
    exact piOrth_ne_one hpos (right_eq_mul.mp h2)
  set S : Set (Module.End (ZMod 3) V) := A ∪ N with hS
  have hScard : S.ncard = 2 * X.ncard := by
    rw [hS, Set.ncard_union_eq hdisj, hNcard, hAcard]
    ring
  have hsqA : ∀ T ∈ A, T * T = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    show sec5c3q_end (L x) * sec5c3q_end (L x) = 1
    rw [← sec5c3q_end_mul, (hL x hx).1]
    rfl
  have hdimA : ∀ T ∈ A, finrank (ZMod 3) (LinearMap.range (T - 1)) = 3 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (sec5c3q_end_invDim (L x)).trans (hL x hx).2.1
  have hcommA : ∀ T ∈ A, ∀ T' ∈ A, T * T' = T' * T ∨ T * T' = -(T' * T) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    have hx1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hF x hx.1)
    have hx2 : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right (hF x' hx'.1)
    have hxx' : x * x' = x' * x :=
      calc x * x' = (x * x')⁻¹ :=
            (inv_eq_of_mul_eq_one_right (hF (x * x') (F.mul_mem hx.1 hx'.1))).symm
        _ = x'⁻¹ * x⁻¹ := mul_inv_rev x x'
        _ = x' * x := by rw [hx1, hx2]
    exact sec5c3q_lift_comm hxx' (hL x hx).2.2 (hL x' hx').2.2
  have hsq : ∀ T ∈ S, T * T = 1 := by
    rintro T (hT | ⟨a, ha, rfl⟩)
    · exact hsqA T hT
    · show (-a) * (-a) = 1
      rw [neg_mul_neg]
      exact hsqA a ha
  have hdim : ∀ T ∈ S, finrank (ZMod 3) (LinearMap.range (T - 1)) = 3 := by
    rintro T (hT | ⟨a, ha, rfl⟩)
    · exact hdimA T hT
    · exact sec5c3q_neg_dim hV6 (hsqA a ha) (hdimA a ha)
  have hcomm : ∀ T ∈ S, ∀ T' ∈ S, T * T' = T' * T ∨ T * T' = -(T' * T) := by
    rintro T (hT | ⟨a, ha, rfl⟩) T' (hT' | ⟨b, hb, rfl⟩)
    · exact hcommA T hT T' hT'
    · exact sec5c3q_cs_neg_right (hcommA T hT b hb)
    · exact sec5c3q_cs_neg_left (hcommA a ha T' hT')
    · exact sec5c3q_cs_neg_right (sec5c3q_cs_neg_left (hcommA a ha b hb))
  have h20 := sec5c3q_inv3_ncard_le hV6 S hsq hdim hcomm
  omega

theorem asc82E64Kind3_holds : Asc82E64Kind3 := asc82E64Kind3_of asc82Type3Bound_holds

end CFSG.OddStandard.SmallF3.Omega
