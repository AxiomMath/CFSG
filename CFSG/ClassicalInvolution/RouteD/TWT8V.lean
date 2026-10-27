module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false

section Bridge

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

@[expose] def BridgeOmega (Q : QuadraticForm K V) (S₁ S₂ : Subgroup (V ≃ₗ[K] V)) : Prop :=
  S₁ ∈ fundSet Q ∧ S₂ ∈ fundSet Q ∧ S₁ ≠ S₂ ∧ ¬ Commutes S₁ S₂ ∧
    ∀ i₂, IsFundamental Q S₂ i₂ → i₂ ∈ Subgroup.normalizer (S₁ : Set (V ≃ₗ[K] V))

theorem La_neg_one_apply_of_mem_span (h2 : (2 : K) ≠ 0) (F : OFrame Q) {x : V} (hx : x ∈ F.span) :
    F.La (-1) x = -x := by
  have : x ∈ negSpace (F.La (-1)) := by rw [negSpace_La_neg_one h2]; exact hx
  rw [negSpace, Module.End.mem_eigenspace_iff] at this
  simpa using this

theorem La_neg_one_apply_of_mem_perp (h2 : (2 : K) ≠ 0) (F : OFrame Q) {x : V} (hx : x ∈ F.perp) :
    F.La (-1) x = x := by
  have : x ∈ posSpace (F.La (-1)) := by rw [posSpace_La_neg_one h2]; exact hx
  rw [posSpace, Module.End.mem_eigenspace_iff] at this
  simpa using this

theorem La_neg_one_comm_of_stable (h2 : (2 : K) ≠ 0) (F₁ F₂ : OFrame Q)
    (hst : ∀ x ∈ F₁.span, F₂.La (-1) x ∈ F₁.span) :
    F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1) := by
  have hjO : F₂.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := F₂.La_mem_orthogonalGroup _
  have hjj : ∀ x, F₂.La (-1) (F₂.La (-1) x) = x := fun x => by
    have := LinearEquiv.congr_fun F₂.La_neg_one_mul_self x
    simpa using this
  have hperp : ∀ r ∈ F₁.perp, F₂.La (-1) r ∈ F₁.perp := by
    intro r hr
    rw [Frame.mem_perp_iff_forall_incl]
    intro Y
    have h1 : F₁.incl Y ∈ F₁.span := ⟨Y, rfl⟩
    have h3 := hst _ h1
    have h4 := polar_map_of_mem hjO (F₂.La (-1) r) (F₁.incl Y)
    rw [hjj] at h4
    rw [← h4, polar_comm]
    exact Frame.polar_eq_zero_of_mem_perp h3 hr
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ F₁.span ⊔ F₁.perp := by
    rw [(Frame.isCompl_span_perp F₁).sup_eq_top]
    trivial
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [LinearEquiv.mul_apply, map_add]
  rw [La_neg_one_apply_of_mem_span h2 F₁ hs, La_neg_one_apply_of_mem_perp h2 F₁ hr,
    La_neg_one_apply_of_mem_span h2 F₁ (hst s hs), La_neg_one_apply_of_mem_perp h2 F₁ (hperp r hr),
    map_neg]


theorem finrank_inf_planes {P₁ P₂ P₃ : Submodule K V} (hP₁ : PolarNondegOn Q P₁)
    (hP₂ : PolarNondegOn Q P₂) (h₁ : Module.finrank K P₁ = 2) (h₂ : Module.finrank K P₂ = 2)
    (h₃ : Module.finrank K P₃ = 2)
    (o₁₂ : ∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0) (o₁₃ : ∀ x ∈ P₁, ∀ y ∈ P₃, polar Q x y = 0)
    (o₂₃ : ∀ x ∈ P₂, ∀ y ∈ P₃, polar Q x y = 0) :
    Module.finrank K ↥((P₁ ⊔ P₂) ⊓ (P₂ ⊔ P₃)) = 2 := by
  have d₂₃ : Disjoint P₂ P₃ := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact hP₂ x hx fun y hy => by rw [polar_comm]; exact o₂₃ y hy x hx'
  have d₁ : Disjoint P₁ (P₂ ⊔ P₃) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    refine hP₁ x hx fun y hy => ?_
    rw [polar_comm]
    exact polar_zero_of_mem_sup o₁₂ o₁₃ y hy x hx'
  have d₁₂ : Disjoint P₁ P₂ := d₁.mono_right le_sup_left
  have h23 : Module.finrank K ↥(P₂ ⊔ P₃) = 4 := by
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint d₂₃, h₂, h₃]
  have h12 : Module.finrank K ↥(P₁ ⊔ P₂) = 4 := by
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint d₁₂, h₁, h₂]
  have h123 : Module.finrank K ↥(P₁ ⊔ (P₂ ⊔ P₃)) = 6 := by
    rw [Models.OrthogonalPairs.Frame.finrank_sup_of_disjoint d₁, h₁, h23]
  have hsup : (P₁ ⊔ P₂) ⊔ (P₂ ⊔ P₃) = P₁ ⊔ (P₂ ⊔ P₃) := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
        (sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_right))
    · exact sup_le (le_sup_left.trans le_sup_left)
        (sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right))
  have := Submodule.finrank_sup_add_finrank_inf_eq (P₁ ⊔ P₂) (P₂ ⊔ P₃)
  rw [hsup, h123, h12, h23] at this
  omega

theorem bridgeOmega_of_planes (hodd : Odd (Nat.card K)) {P₁ P₂ P₃ : Submodule K V}
    (hP₁ : PolarNondegOn Q P₁) (hP₂ : PolarNondegOn Q P₂) (h₁ : Module.finrank K P₁ = 2)
    (h₂ : Module.finrank K P₂ = 2) (h₃ : Module.finrank K P₃ = 2)
    (o₁₂ : ∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0) (o₁₃ : ∀ x ∈ P₁, ∀ y ∈ P₃, polar Q x y = 0)
    (o₂₃ : ∀ x ∈ P₂, ∀ y ∈ P₃, polar Q x y = 0) {F₁ F₂ : OFrame Q}
    (hF₁ : F₁.span = P₁ ⊔ P₂) (hF₂ : F₂.span = P₂ ⊔ P₃) :
    BridgeOmega Q F₁.La.range F₂.La.range ∧
      F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1) ∧
      Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hdim := finrank_inf_planes hP₁ hP₂ h₁ h₂ h₃ o₁₂ o₁₃ o₂₃
  rw [← hF₁, ← hF₂] at hdim
  have hst : ∀ x ∈ F₁.span, F₂.La (-1) x ∈ F₁.span := by
    intro x hx
    rw [hF₁] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have haF : a ∈ F₂.perp := by
      rw [Frame.mem_perp_iff_forall_incl]
      intro Y
      have : F₂.incl Y ∈ P₂ ⊔ P₃ := by rw [← hF₂]; exact ⟨Y, rfl⟩
      exact polar_zero_of_mem_sup o₁₂ o₁₃ a ha _ this
    have hbF : b ∈ F₂.span := by rw [hF₂]; exact Submodule.mem_sup_left hb
    rw [map_add, La_neg_one_apply_of_mem_perp h2 F₂ haF, La_neg_one_apply_of_mem_span h2 F₂ hbF,
      hF₁]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
      ((P₁ ⊔ P₂).neg_mem (Submodule.mem_sup_right hb))
  have hcomm := La_neg_one_comm_of_stable h2 F₁ F₂ hst
  have hne : F₂.La (-1) ≠ F₁.La (-1) := by
    intro h
    have hs := Frame.span_eq_of_La_neg_one_eq h2 h
    rw [hF₁, hF₂] at hs
    have hP : ∀ x ∈ P₁, x ∈ P₂ ⊔ P₃ := fun x hx => by
      rw [hs]
      exact Submodule.mem_sup_left hx
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ P₁, x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : P₁ = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
      rw [this, finrank_bot] at h₁
      omega
    refine hx0 (hP₁ x hx fun y hy => ?_)
    rw [polar_comm]
    exact polar_zero_of_mem_sup o₁₂ o₁₃ y hy x (hP x hx)
  have hfund₁ := IsFundamental.of_frame F₁
  have hfund₂ := IsFundamental.of_frame F₂
  refine ⟨⟨⟨_, hfund₁⟩, ⟨_, hfund₂⟩, fun h => hne ?_, ?_, ?_⟩, hcomm, hdim⟩
  · exact IsFundamental.involution_unique hodd hfund₂ (h ▸ hfund₁)
  · obtain ⟨x, hx, hx0⟩ : ∃ x ∈ P₂, x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : P₂ = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
      rw [this, finrank_bot] at h₂
      omega
    obtain ⟨y, hy, hxy⟩ := hP₂.exists_polar_ne_zero hx hx0
    refine not_commutes_of_nonorth hodd hfund₁ hfund₂ hne (x := x) (y := y) ?_ ?_ hxy
    · rw [negSpace_La_neg_one h2, hF₁]
      exact Submodule.mem_sup_right hx
    · rw [negSpace_La_neg_one h2, hF₂]
      exact Submodule.mem_sup_left hy
  · intro i₂ hi₂
    have hii : i₂ = F₂.La (-1) := (IsFundamental.involution_unique hodd hfund₂ hi₂).symm
    rw [hii]
    rw [mem_normalizer_iff_even hodd hfund₁ hfund₂ hcomm.symm]
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2]
    rw [hdim]
    exact ⟨1, rfl⟩


theorem bridgeOmega_of_pairs (hodd : Odd (Nat.card K)) (c₀ c₁ c₂ : HypPair Q)
    (o₀₁ : c₀.Orth c₁) (o₀₂ : c₀.Orth c₂) (o₁₂ : c₁.Orth c₂) :
    BridgeOmega Q (mkFrame c₀ c₁ o₀₁).La.range (mkFrame c₁ c₂ o₁₂).La.range ∧
      (mkFrame c₀ c₁ o₀₁).span = hypPlane c₀ ⊔ hypPlane c₁ ∧
      (mkFrame c₁ c₂ o₁₂).span = hypPlane c₁ ⊔ hypPlane c₂ := by
  have hspan₁ : (mkFrame c₀ c₁ o₀₁).span = hypPlane c₀ ⊔ hypPlane c₁ := frame_span_eq _
  have hspan₂ : (mkFrame c₁ c₂ o₁₂).span = hypPlane c₁ ⊔ hypPlane c₂ := frame_span_eq _
  refine ⟨(bridgeOmega_of_planes hodd (polarNondegOn_hypPlane c₀) (polarNondegOn_hypPlane c₁)
    (finrank_hypPlane c₀) (finrank_hypPlane c₁) (finrank_hypPlane c₂)
    (polar_hypPlane_of_orth o₀₁) (polar_hypPlane_of_orth o₀₂) (polar_hypPlane_of_orth o₁₂)
    hspan₁ hspan₂).1, hspan₁, hspan₂⟩

end Bridge

end CFSG.ClassicalInvolution.RouteD.TWT8
