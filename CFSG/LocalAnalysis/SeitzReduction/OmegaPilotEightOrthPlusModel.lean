module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open scoped commutatorElement

section Span

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ P₃ P₄ : HypPair Q}

theorem inW_zero : InW P₁ P₂ (0 : V) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact polar_zero_right _ _

theorem inW_of_mem_spanU₄ (h31 : P₃.Orth P₁) (h32 : P₃.Orth P₂) (h41 : P₄.Orth P₁)
    (h42 : P₄.Orth P₂) {x : V} (hx : x ∈ spanU₄ P₃ P₄) : InW P₁ P₂ x := by
  obtain ⟨a1, a2⟩ := inW_of_orth h31 h32
  obtain ⟨b1, b2⟩ := inW_of_orth h41 h42
  induction hx using Submodule.span_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [a1, b1, a2, b2]
  | zero => exact inW_zero
  | add y z _ _ hy hz => simpa using inW_add_smul hy hz 1 1
  | smul c y _ hy => simpa using inW_add_smul hy hy c 0

theorem mem_spanU₄_of_inW (h₃₄ : P₃.Orth P₄) (h31 : P₃.Orth P₁) (h32 : P₃.Orth P₂)
    (h41 : P₄.Orth P₁) (h42 : P₄.Orth P₂)
    (hcover : ∀ x : V, InW P₁ P₂ x → InW P₃ P₄ x → x = 0) {x : V} (hx : InW P₁ P₂ x) :
    x ∈ spanU₄ P₃ P₄ := by
  have hv : InW P₃ P₄ (x - uPart P₃ P₄ x) := inW_sub_uPart h₃₄ x
  have hu : InW P₁ P₂ (uPart P₃ P₄ x) := inW_of_mem_spanU₄ h31 h32 h41 h42 (uPart_mem_spanU₄ x)
  have hv' : InW P₁ P₂ (x - uPart P₃ P₄ x) := by
    have h := inW_add_smul hx hu 1 (-1)
    simpa [sub_eq_add_neg] using h
  have h0 := hcover _ hv' hv
  rw [sub_eq_zero.mp h0]
  exact uPart_mem_spanU₄ x

theorem inW_flip_iff {x : V} : InW P₁ (flipPair P₂) x ↔ InW P₁ P₂ x := by
  simp only [InW, flipPair_e, flipPair_f]
  tauto

theorem spanU₄_flip : spanU₄ P₁ (flipPair P₂) = spanU₄ P₁ P₂ := by
  simp only [spanU₄, flipPair_e, flipPair_f]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem eq_one_of_fix_spanU₄_of_fixW (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hU : ∀ u ∈ spanU₄ P₁ P₂, g u = u) (hW : ∀ w, InW P₁ P₂ w → g w = w) : g = 1 := by
  refine LinearEquiv.ext fun x => ?_
  calc g x = g ((x - uPart P₁ P₂ x) + uPart P₁ P₂ x) := by rw [sub_add_cancel]
    _ = (x - uPart P₁ P₂ x) + uPart P₁ P₂ x := by
        rw [map_add, hW _ (inW_sub_uPart h₁₂ x), hU _ (uPart_mem_spanU₄ x)]
    _ = (1 : V ≃ₗ[K] V) x := by rw [sub_add_cancel]; rfl

theorem fix_spanU₄_of_fix (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V} (h1 : g P₁.e = P₁.e)
    (h2 : g P₁.f = P₁.f) (h3 : g P₂.e = P₂.e) (h4 : g P₂.f = P₂.f) :
    ∀ u ∈ spanU₄ P₁ P₂, g u = u := by
  intro u hu
  rw [← uPart_eq_of_mem_spanU₄ h₁₂ hu]
  simp only [uPart, map_add, map_smul, h1, h2, h3, h4]

theorem rootLevi_apply_mem_spanU₄ (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgL : g ∈ rootLevi Q P₁ P₂) {u : V} (hu : u ∈ spanU₄ P₁ P₂) : g u ∈ spanU₄ P₁ P₂ := by
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hgL.1.2)
  obtain ⟨k1, k2⟩ := apply_e_eq_coeff (orth_flipPair_flipPair h₁₂)
    (mem_centralizer_singleton_iff.mp hgL.2)
  simp only [flipPair_e, flipPair_f] at k1 k2
  have hmem : ∀ w ∈ ({P₁.e, P₂.e, P₁.f, P₂.f} : Set V), g w ∈ spanU₄ P₁ P₂ := by
    have s1 : P₁.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
    have s2 : P₂.e ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
    have s3 : P₁.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
    have s4 : P₂.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [g1]; exact add_mem (Submodule.smul_mem _ _ s1) (Submodule.smul_mem _ _ s2)
    · rw [g2]; exact add_mem (Submodule.smul_mem _ _ s1) (Submodule.smul_mem _ _ s2)
    · rw [k1]; exact add_mem (Submodule.smul_mem _ _ s3) (Submodule.smul_mem _ _ s4)
    · rw [k2]; exact add_mem (Submodule.smul_mem _ _ s3) (Submodule.smul_mem _ _ s4)
  induction hu using Submodule.span_induction with
  | mem w hw => exact hmem w hw
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem map_comb4_eq (h₁₂ : P₁.Orth P₂) (x y z w : K) :
    Q (x • P₁.e + y • P₁.f + (z • P₂.e + w • P₂.f)) = x * y + z * w := by
  have h21 := h₁₂.symm
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q (x • P₁.e), QuadraticMap.map_add Q (z • P₂.e),
    QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul,
    P₁.Q_e, P₁.Q_f, P₂.Q_e, P₂.Q_f]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    P₁.polar_ef, P₂.polar_ef, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, smul_eq_mul]
  ring

theorem exists_eichler_of_fix_e (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : g P₁.e = P₁.e) (h2 : g P₂.e = P₂.e)
    (hgU : ∀ u ∈ spanU₄ P₁ P₂, g u ∈ spanU₄ P₁ P₂) :
    ∃ γ : K, ∀ u ∈ spanU₄ P₁ P₂, g u = eichler Q P₁.e (γ • P₂.e) u := by
  have h21 := h₁₂.symm
  have s3 : P₁.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  have s4 : P₂.f ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by simp)
  set v := g P₁.f with hv
  set v' := g P₂.f with hv'
  have pv1 : polar Q v P₁.e = 1 := by
    rw [hv, ← h1, polar_map_of_mem hgO]; exact P₁.polar_fe
  have pv2 : polar Q v P₂.e = 0 := by
    rw [hv, ← h2, polar_map_of_mem hgO]; exact h₁₂.fe
  have pw1 : polar Q v' P₁.e = 0 := by
    rw [hv', ← h1, polar_map_of_mem hgO, polar_comm]; exact h₁₂.ef
  have pw2 : polar Q v' P₂.e = 1 := by
    rw [hv', ← h2, polar_map_of_mem hgO]; exact P₂.polar_fe
  have Qv : Q v = 0 := by rw [hv, map_of_mem hgO, P₁.Q_f]
  have Qv' : Q v' = 0 := by rw [hv', map_of_mem hgO, P₂.Q_f]
  have pvv' : polar Q v v' = 0 := by rw [hv, hv', polar_map_of_mem hgO]; exact h₁₂.ff
  have hvU : v ∈ spanU₄ P₁ P₂ := hgU _ s3
  have hv'U : v' ∈ spanU₄ P₁ P₂ := hgU _ s4
  have ev : v = polar Q v P₁.f • P₁.e + polar Q v P₁.e • P₁.f +
      (polar Q v P₂.f • P₂.e + polar Q v P₂.e • P₂.f) := by
    conv_lhs => rw [← uPart_eq_of_mem_spanU₄ h₁₂ hvU]
    rw [uPart]; abel
  have ev' : v' = polar Q v' P₁.f • P₁.e + polar Q v' P₁.e • P₁.f +
      (polar Q v' P₂.f • P₂.e + polar Q v' P₂.e • P₂.f) := by
    conv_lhs => rw [← uPart_eq_of_mem_spanU₄ h₁₂ hv'U]
    rw [uPart]; abel
  have hα : polar Q v P₁.f = 0 := by
    have h := map_comb4_eq (Q := Q) h₁₂ (polar Q v P₁.f) (polar Q v P₁.e) (polar Q v P₂.f)
      (polar Q v P₂.e)
    rw [← ev, Qv, pv1, pv2] at h
    linear_combination -h
  have hβ : polar Q v' P₂.f = 0 := by
    have h := map_comb4_eq (Q := Q) h₁₂ (polar Q v' P₁.f) (polar Q v' P₁.e) (polar Q v' P₂.f)
      (polar Q v' P₂.e)
    rw [← ev', Qv', pw1, pw2] at h
    linear_combination -h
  set γ := polar Q v P₂.f with hγ
  have hv1 : v = P₁.f + γ • P₂.e := by
    conv_lhs => rw [ev]
    rw [hα, pv1, pv2]; module
  have hv2 : v' = P₂.f + polar Q v' P₁.f • P₁.e := by
    conv_lhs => rw [ev']
    rw [hβ, pw1, pw2]; module
  have hαβ : polar Q v' P₁.f = -γ := by
    have h := pvv'
    rw [hv1, hv2] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      P₁.polar_ef, P₂.polar_ef, h₁₂.ff, polar_comm Q P₁.f P₁.e] at h
    rw [polar_comm Q P₂.e P₁.e, h₁₂.ee] at h
    linear_combination h
  have hQw : Q (γ • P₂.e) = 0 := by rw [QuadraticMap.map_smul, P₂.Q_e, smul_zero]
  have hpw : polar Q P₁.e (γ • P₂.e) = 0 := by rw [polar_smul_right_eq, h₁₂.ee, mul_zero]
  refine ⟨γ, ?_⟩
  have E1 : eichler Q P₁.e (γ • P₂.e) P₁.e = P₁.e := eichler_apply_self _ _
  have E2 : eichler Q P₁.e (γ • P₂.e) P₂.e = P₂.e := eichler_apply_of_polar_eq_zero
    (by rw [polar_comm]; exact h₁₂.ee) (by rw [polar_smul_right_eq, P₂.polar_ee, mul_zero])
  have E3 : eichler Q P₁.e (γ • P₂.e) P₁.f = v := by
    rw [eichler_apply P₁.Q_e hpw, hQw, hv1, P₁.polar_fe, polar_smul_right_eq, h₁₂.fe]
    module
  have E4 : eichler Q P₁.e (γ • P₂.e) P₂.f = v' := by
    rw [eichler_apply P₁.Q_e hpw, hQw, hv2, hαβ, polar_comm Q P₂.f P₁.e, h₁₂.ef,
      polar_smul_right_eq, P₂.polar_fe]
    module
  intro u hu
  rw [← uPart_eq_of_mem_spanU₄ h₁₂ hu]
  simp only [uPart, map_add, map_smul, h1, h2, E1, E2, E3, E4, hv, hv']

theorem exists_leviFix_eichler_of_commute (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g)
    (hgU : ∀ u ∈ spanU₄ P₁ P₂, g u ∈ spanU₄ P₁ P₂) :
    ∃ a ∈ leviFix H P₁ P₂, ∃ γ : K, ∀ u ∈ spanU₄ P₁ P₂,
      g u = a (eichler Q P₁.e (γ • P₂.e) u) := by
  obtain ⟨⟨a, ha⟩, haM⟩ := leviCoeff_surjective h₁₂ hE
    ⟨planeCoeff P₁ P₂ g, det_planeCoeff h₁₂ hgO hgc⟩
  have haM' : planeCoeff P₁ P₂ a = planeCoeff P₁ P₂ g := congrArg Subtype.val haM
  obtain ⟨-, haL, -⟩ := mem_leviFix.mp ha
  obtain ⟨a1, a2⟩ := planeCoeff_apply_e h₁₂ (leviFix_commute_e ha)
  obtain ⟨g1, g2⟩ := planeCoeff_apply_e h₁₂ hgc
  rw [haM'] at a1 a2
  have hhO : a⁻¹ * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem haL.1.1) hgO
  have h1 : (a⁻¹ * g) P₁.e = P₁.e := by
    rw [LinearEquiv.mul_apply, g1, ← a1, LinearEquiv.inv_apply_apply']
  have h2 : (a⁻¹ * g) P₂.e = P₂.e := by
    rw [LinearEquiv.mul_apply, g2, ← a2, LinearEquiv.inv_apply_apply']
  have hhU : ∀ u ∈ spanU₄ P₁ P₂, (a⁻¹ * g) u ∈ spanU₄ P₁ P₂ := fun u hu =>
    rootLevi_apply_mem_spanU₄ h₁₂ (inv_mem haL) (hgU u hu)
  obtain ⟨γ, hγ⟩ := exists_eichler_of_fix_e h₁₂ hhO h1 h2 hhU
  refine ⟨a, ha, γ, fun u hu => ?_⟩
  rw [← hγ u hu, LinearEquiv.mul_apply, LinearEquiv.apply_inv_apply']

theorem leviFix_commute_eichler (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)}
    (hE : ∀ u w : V, eichler Q u w ∈ H) {a : V ≃ₗ[K] V} (ha : a ∈ leviFix H P₁ P₂) (γ : K) :
    a * eichler Q P₁.e (γ • P₂.e) = eichler Q P₁.e (γ • P₂.e) * a := by
  have hle : closure (Set.range (fun t : K => eichler Q P₁.e (t • P₂.f)) ∪
      Set.range (fun t : K => eichler Q P₂.e (t • P₁.f))) ≤
      centralizer ({eichler Q P₁.e (γ • P₂.e)} : Set (V ≃ₗ[K] V)) := by
    rw [closure_le]
    have e2f1 : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    · exact rootGroup_commute (eichler_smul_mem_rootGroup_left h₁₂.ef t)
        (eichler_smul_mem_rootGroup_left h₁₂.ee γ)
    · exact rootGroup_commute (eichler_smul_mem_rootGroup_left e2f1 t)
        (eichler_smul_mem_rootGroup_right P₁.Q_e P₂.Q_e h₁₂.ee γ)
  exact mem_centralizer_singleton_iff.mp (hle (leviFix_le_closure h₁₂ hE ha))

theorem leviFix_commute_of_fix (h₁₂ : P₁.Orth P₂) {H : Subgroup (V ≃ₗ[K] V)} {g h : V ≃ₗ[K] V}
    (hg : g ∈ leviFix H P₁ P₂) (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h1 : h P₁.e = P₁.e) (h2 : h P₁.f = P₁.f) (h3 : h P₂.e = P₂.e) (h4 : h P₂.f = P₂.f) :
    g * h = h * g := by
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp hg
  have hfix := fix_spanU₄_of_fix h₁₂ h1 h2 h3 h4
  have hU : ∀ w ∈ ({P₁.e, P₁.f, P₂.e, P₂.f} : Set V), h (g w) = g w := by
    intro w hw
    have hw' : w ∈ spanU₄ P₁ P₂ := Submodule.subset_span (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢; tauto)
    exact hfix _ (rootLevi_apply_mem_spanU₄ h₁₂ hgL hw')
  exact commute_of_fixW_of_fix h₁₂ hgW hhO ⟨h1, h2, h3, h4⟩
    ⟨hU _ (by simp), hU _ (by simp), hU _ (by simp), hU _ (by simp)⟩

end Span

section Agree

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : Submodule K V}

theorem inv_apply_eq_of_agree {f g : V ≃ₗ[K] V} (hfinv : ∀ u ∈ U, f⁻¹ u ∈ U)
    (hfg : ∀ u ∈ U, f u = g u) : ∀ u ∈ U, f⁻¹ u = g⁻¹ u := by
  intro u hu
  apply g.injective
  have h := hfg _ (hfinv u hu)
  rw [LinearEquiv.apply_inv_apply'] at h
  rw [← h, LinearEquiv.apply_inv_apply']

theorem mul_apply_eq_of_agree {f₁ f₂ g₁ g₂ : V ≃ₗ[K] V} (hf₂ : ∀ u ∈ U, f₂ u ∈ U)
    (h₁ : ∀ u ∈ U, f₁ u = g₁ u) (h₂ : ∀ u ∈ U, f₂ u = g₂ u) :
    ∀ u ∈ U, (f₁ * f₂) u = (g₁ * g₂) u := by
  intro u hu
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₁ _ (hf₂ u hu), h₂ u hu]

theorem commutator_apply_eq_of_agree {f₁ f₂ g₁ g₂ : V ≃ₗ[K] V}
    (hf₁' : ∀ u ∈ U, f₁⁻¹ u ∈ U) (hf₂ : ∀ u ∈ U, f₂ u ∈ U) (hf₂' : ∀ u ∈ U, f₂⁻¹ u ∈ U)
    (h₁ : ∀ u ∈ U, f₁ u = g₁ u) (h₂ : ∀ u ∈ U, f₂ u = g₂ u) :
    ∀ u ∈ U, ⁅f₁, f₂⁆ u = ⁅g₁, g₂⁆ u := by
  have i₁ := inv_apply_eq_of_agree hf₁' h₁
  have i₂ := inv_apply_eq_of_agree hf₂' h₂
  have m1 := mul_apply_eq_of_agree hf₂ h₁ h₂
  have m2 := mul_apply_eq_of_agree hf₁' m1 i₁
  have m3 := mul_apply_eq_of_agree hf₂' m2 i₂
  intro u hu
  rw [commutatorElement_def, commutatorElement_def]
  exact m3 u hu

end Agree

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {a₁ a₂ e₁ e₂ : G}
    (h12 : a₁ * e₂ = e₂ * a₁) (h21 : a₂ * e₁ = e₁ * a₂) (he : e₁ * e₂ = e₂ * e₁) :
    ⁅a₁ * e₁, a₂ * e₂⁆ = ⁅a₁, a₂⁆ := by
  have h12' : e₂ * a₁⁻¹ = a₁⁻¹ * e₂ := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h12, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a₁ * e₁, a₂ * e₂⁆ = a₁ * (e₁ * a₂) * e₂ * e₁⁻¹ * a₁⁻¹ * e₂⁻¹ * a₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a₁ * (a₂ * e₁) * e₂ * e₁⁻¹ * a₁⁻¹ * e₂⁻¹ * a₂⁻¹ := by rw [h21]
    _ = a₁ * a₂ * (e₁ * e₂) * e₁⁻¹ * a₁⁻¹ * e₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (e₂ * e₁) * e₁⁻¹ * a₁⁻¹ * e₂⁻¹ * a₂⁻¹ := by rw [he]
    _ = a₁ * a₂ * (e₂ * a₁⁻¹) * e₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (a₁⁻¹ * e₂) * e₂⁻¹ * a₂⁻¹ := by rw [h12']
    _ = ⁅a₁, a₂⁆ := by rw [commutatorElement_def]; group

section Gen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orth_flipPair_left {P P' : HypPair Q} (h : P.Orth P') : (flipPair P).Orth P' :=
  ⟨h.fe, h.ff, h.ee, h.ef⟩

theorem orth_flipPair_right {P P' : HypPair Q} (h : P.Orth P') : P.Orth (flipPair P') :=
  ⟨h.ef, h.ee, h.ff, h.fe⟩

theorem orth_symm {P P' : HypPair Q} (h : P.Orth P') : P'.Orth P :=
  ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe,
    by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩

end Gen

section GroupGen

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_centralizer {H₁ H₂ : Subgroup G}
    (h : H₁ ≤ centralizer (H₂ : Set G)) {x : G} (hx : x ∈ H₁ ⊔ H₂) :
    ∃ y ∈ H₁, ∃ z ∈ H₂, x = y * z := by
  have hcomm : ∀ (a : H₁) (b : H₂), Commute (H₁.subtype a) (H₂.subtype b) := fun a b =>
    (mem_centralizer_iff.mp (h a.2) b b.2).symm
  set μ : H₁ × H₂ →* G := H₁.subtype.noncommCoprod H₂.subtype hcomm with hμ
  have hle : H₁ ⊔ H₂ ≤ μ.range := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨(⟨a, ha⟩, 1), by simp [hμ]⟩
    · intro b hb
      exact ⟨(1, ⟨b, hb⟩), by simp [hμ]⟩
  obtain ⟨⟨y, z⟩, hyz⟩ := hle hx
  exact ⟨y, y.2, z, z.2, hyz.symm⟩

theorem conj_mem_sup_of_forall {H₁ H₂ : Subgroup G} {c : G}
    (h1 : ∀ x ∈ H₁, c * x * c⁻¹ ∈ H₁) (h2 : ∀ x ∈ H₂, c * x * c⁻¹ ∈ H₂) {x : G}
    (hx : x ∈ H₁ ⊔ H₂) : c * x * c⁻¹ ∈ H₁ ⊔ H₂ := by
  have hmap : (H₁ ⊔ H₂).map (MulAut.conj c).toMonoidHom ≤ H₁ ⊔ H₂ := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_ <;> rintro _ ⟨y, hy, rfl⟩
    · exact h1 y hy
    · exact h2 y hy
  exact hmap ⟨x, hx, rfl⟩

theorem conj_mem_of_commute {H : Subgroup G} {c : G} (hc : ∀ x ∈ H, c * x = x * c) :
    ∀ x ∈ H, c * x * c⁻¹ ∈ H := fun x hx => by
  rw [hc x hx, mul_inv_cancel_right]; exact hx

end GroupGen

section Proj

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem mem_map_projHom_iff (hQ' : ∃ v, Q v ≠ 0) {H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    {x : matrixProjectiveDerived Q} :
    x ∈ (H.subgroupOf (orthDerived Q)).map (projHom Q) ↔ projLift hQ' x ∈ H := by
  refine ⟨projLift_mem_of_mem_map hQ', fun h => ?_⟩
  exact ⟨⟨projLift hQ' x, projLift_mem_orthDerived hQ' x⟩, mem_subgroupOf.mpr h,
    projHom_projLift hQ' x⟩

theorem mem_stabTwoBar_iff {n : ℕ} (hQ' : ∃ v, coordinateQuadPlus n K v ≠ 0) {i j : Fin n}
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} :
    x ∈ stabTwoBar K i j ↔ projLift hQ' x ∈ stabTwo K i j :=
  mem_map_projHom_iff hQ'

end Proj

section ModelA

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem le_centralizer_of_model_leviFix (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate) {P₃ : HypPair Q}
    (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃) {y : matrixProjectiveDerived Q}
    (hy : y ∈ leviFixBar ha.hypPair hb.hypPair) (hy1 : y ≠ 1) (hyo : Odd (orderOf y))
    {S R : Subgroup (matrixProjectiveDerived Q)} (hSy : S ≤ centralizer {y})
    (hSgen : ∀ N : Subgroup (matrixProjectiveDerived Q),
      rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃ ∈ N → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S ≤ N)
    (hRz : R ≤ centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃})
    (hRy : R ≤ centralizer {y}) (hRperf : ⁅R, R⁆ = R) :
    S ≤ centralizer (R : Set (matrixProjectiveDerived Q)) := by
  have h₁₂ := ha.orth hb hd
  have hQ' := ha.exists_ne_zero
  set φ := projLiftHom hQ' with hφ
  have hφi := projLiftHom_injective hQ'
  obtain ⟨-, hgL, hgW⟩ := mem_leviFix.mp (projLift_mem_leviFix hQ' hy)
  have hgL' : φ y ∈ rootLevi Q ha.hypPair hb.hypPair := hgL
  have hgm : φ y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hg1 : φ y ≠ 1 := fun h => hy1 (hφi (h.trans (map_one φ).symm))
  have hz : φ (rootPairElt hQ h₁₂ h₁₃ h₂₃) = eichler Q ha.hypPair.e hb.hypPair.e := by
    rw [projLiftHom_apply, rootPairElt, projLift_projHom]
  have hcomm : ∀ {u v : matrixProjectiveDerived Q}, u * v = v * u → φ u * φ v = φ v * φ u :=
    fun h => by rw [← map_mul, ← map_mul, h]
  intro s hs
  rw [mem_centralizer_iff]
  intro r hr
  have key := commute_of_model h₁₂ hgL' hgW hyo hgm hg1 (S := S.map φ) (R := R.map φ)
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hSy hu))))
    (by
      intro N hzN hN
      rw [Subgroup.map_le_iff_le_comap]
      refine hSgen _ (by rw [Subgroup.mem_comap, hz]; exact hzN) ?_
      intro u hu n hn
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hN _ ⟨u, hu, rfl⟩ _ hn)
    (by
      rintro _ ⟨u, -, rfl⟩
      exact Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ' u))
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hz]
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hRz hu))))
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hRy hu))))
    (by rw [← Subgroup.map_commutator, hRperf]) ⟨s, hs, rfl⟩ ⟨r, hr, rfl⟩
  rw [← map_mul, ← map_mul] at key
  exact (hφi key).symm

end ModelA

section Config

variable {K : Type} [Field K]

omit [Field K] in
theorem eq_zero_of_forall_polar_plusPair [Field K] {x : Fin (2 * 4) → K}
    (hx : ∀ k : Fin 4, polar (coordinateQuadPlus 4 K) (plusPair K k).e x = 0 ∧
      polar (coordinateQuadPlus 4 K) (plusPair K k).f x = 0) : x = 0 := by
  funext i
  obtain ⟨s, rfl⟩ := (plusIndexEquiv 4).surjective i
  rcases s with k | k
  · have h := (hx k).2
    rw [IsHypCoord.hypPair_f, (isHypCoord_coordinateQuadPlus k).polar_right] at h
    exact h
  · have h := (hx k).1
    rw [IsHypCoord.hypPair_e, (isHypCoord_coordinateQuadPlus k).polar_left] at h
    exact h

theorem plusB_config {P₄ : HypPair (coordinateQuadPlus 4 K)}
    (hP₄ : P₄ = plusPair K 3 ∨ P₄ = flipPair (plusPair K 3)) :
    (plusPair K 2).Orth P₄ ∧ (plusPair K 0).Orth P₄ ∧ (flipPair (plusPair K 1)).Orth P₄ ∧
      (∀ x, InW (plusPair K 0) (flipPair (plusPair K 1)) x → InW (plusPair K 2) P₄ x → x = 0) ∧
      spanU₄ (plusPair K 2) P₄ = spanU₄ (plusPair K 2) (plusPair K 3) := by
  have hcov : ∀ x, InW (plusPair K 0) (flipPair (plusPair K 1)) x →
      InW (plusPair K 2) (plusPair K 3) x → x = 0 := by
    intro x h1 h2
    rw [inW_flip_iff] at h1
    obtain ⟨a1, a2, a3, a4⟩ := h1
    obtain ⟨b1, b2, b3, b4⟩ := h2
    refine eq_zero_of_forall_polar_plusPair fun k => ?_
    fin_cases k
    exacts [⟨a1, a2⟩, ⟨a3, a4⟩, ⟨b1, b2⟩, ⟨b3, b4⟩]
  rcases hP₄ with rfl | rfl
  · exact ⟨plusPair_orth (by decide), plusPair_orth (by decide),
      orth_flipPair_left (plusPair_orth (by decide)), hcov, rfl⟩
  · exact ⟨plusPair_orth_flip (by decide), plusPair_orth_flip (by decide),
      orth_flipPair_left (plusPair_orth_flip (by decide)),
      fun x h1 h2 => hcov x h1 (inW_flip_iff.mp h2), spanU₄_flip⟩

variable [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def plusZ : matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
  rootPairElt (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (plusPair_orth_flip (K := K) (show (0 : Fin 4) ≠ 1 by decide))
    (plusPair_orth (show (0 : Fin 4) ≠ 2 by decide))
    (orth_flipPair_left (plusPair_orth (show (1 : Fin 4) ≠ 2 by decide)))

theorem projLift_plusZ (hQ' : ∃ v, coordinateQuadPlus 4 K v ≠ 0) :
    projLift hQ' (plusZ K) = eichler (coordinateQuadPlus 4 K) (plusPair K 0).e
      (flipPair (plusPair K 1)).e := by
  rw [plusZ, rootPairElt, projLift_projHom]

omit [CharP K 2] in
theorem plusZ_mem_leviFixBar :
    plusZ K ∈ leviFixBar (plusPair K 0) (plusPair K 1) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have h := (eichler_mem_leviFix (plusPair_orth (K := K) (show (0 : Fin 4) ≠ 1 by decide))
    (eichler_mem_orthDerived hQ hT) 1).1
  rw [one_smul] at h
  exact projHom_mem_leviFixBar h

end Config

section ModelB

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem leviFixBar_commute_stabTwoBar_zero_one {P₂ : HypPair (coordinateQuadPlus 4 K)}
    (hP₂ : P₂ = plusPair K 1 ∨ P₂ = flipPair (plusPair K 1)) {j b : matrixProjectiveDerived
      (coordinateQuadPlus 4 K)} (hj : j ∈ leviFixBar (plusPair K 0) P₂) (hb : b ∈ stabTwoBar K 0 1) :
    j * b = b * j := by
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have hJ := projLift_mem_leviFix hQ' hj
  have hB := (mem_map_projHom_iff hQ').mp hb
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hB
  have hBO : projLift hQ' b ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K) :=
    Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ' b)
  have key : projLift hQ' j * projLift hQ' b = projLift hQ' b * projLift hQ' j := by
    rcases hP₂ with rfl | rfl
    · exact leviFix_commute_of_fix (plusPair_orth (by decide)) hJ hBO b1 b2 b3 b4
    · exact leviFix_commute_of_fix (plusPair_orth_flip (by decide)) hJ hBO b1 b2 b4 b3
  apply projLiftHom_injective hQ'
  rw [map_mul, map_mul]
  exact key

theorem le_centralizer_of_model_plusB (hq : 4 ≤ Nat.card K)
    {P₄ : HypPair (coordinateQuadPlus 4 K)} (hP₄ : P₄ = plusPair K 3 ∨ P₄ = flipPair (plusPair K 3))
    {y : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hy : y ∈ leviFixBar (plusPair K 2) P₄)
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y))
    {S R : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hSy : S ≤ centralizer {y})
    (hSgen : ∀ N : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)), plusZ K ∈ N →
      (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S ≤ N)
    (hRz : R ≤ centralizer {plusZ K}) (hRy : R ≤ centralizer {y}) (hRperf : ⁅R, R⁆ = R) :
    S ≤ centralizer (R : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  classical
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have hE := eichler_mem_orthDerived hQ hT
  obtain ⟨h24, h04, h14, hcover, hspan⟩ := plusB_config hP₄
  have h₁₂ : (plusPair K 0).Orth (flipPair (plusPair K 1)) := plusPair_orth_flip (by decide)
  have h01 : (plusPair K 0).Orth (plusPair K 1) := plusPair_orth (by decide)
  have h02 : (plusPair K 0).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h12 : (flipPair (plusPair K 1)).Orth (plusPair K 2) :=
    orth_flipPair_left (plusPair_orth (by decide))
  have h23 : (plusPair K 2).Orth (plusPair K 3) := plusPair_orth (by decide)
  have h03 : (plusPair K 0).Orth (plusPair K 3) := plusPair_orth (by decide)
  have h13 : (flipPair (plusPair K 1)).Orth (plusPair K 3) :=
    orth_flipPair_left (plusPair_orth (by decide))
  have hWiff : ∀ x, InW (plusPair K 0) (flipPair (plusPair K 1)) x ↔
      x ∈ spanU₄ (plusPair K 2) P₄ := fun x =>
    ⟨mem_spanU₄_of_inW h24 (orth_symm h02) (orth_symm h12) (orth_symm h04) (orth_symm h14) hcover,
      inW_of_mem_spanU₄ (orth_symm h02) (orth_symm h12) (orth_symm h04) (orth_symm h14)⟩
  have hUiff : ∀ x, InW (plusPair K 2) P₄ x ↔
      x ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) := fun x =>
    ⟨mem_spanU₄_of_inW h₁₂ h02 h04 h12 h14 (fun x h1 h2 => hcover x h2 h1),
      inW_of_mem_spanU₄ h02 h04 h12 h14⟩
  set φ := projLiftHom hQ' with hφ
  have hφi := projLiftHom_injective hQ'
  obtain ⟨-, hYL, hYW⟩ := mem_leviFix.mp (projLift_mem_leviFix hQ' hy)
  have hYL' : φ y ∈ rootLevi (coordinateQuadPlus 4 K) (plusPair K 2) P₄ := hYL
  have hYW' : ∀ x, InW (plusPair K 2) P₄ x → φ y x = x := hYW
  have hYm : φ y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hY1 : φ y ≠ 1 := fun h => hy1 (hφi (h.trans (map_one φ).symm))
  have hcommφ : ∀ {u v : matrixProjectiveDerived (coordinateQuadPlus 4 K)}, u * v = v * u →
      φ u * φ v = φ v * φ u := fun h => by rw [← map_mul, ← map_mul, h]
  have hcY : ∀ {x}, x ∈ centralizer ({y} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) →
      φ x * φ y = φ y * φ x := fun hx => hcommφ (mem_centralizer_singleton_iff.mp hx)
  have hpresW : ∀ g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K), g * φ y = φ y * g →
      ∀ x, InW (plusPair K 0) (flipPair (plusPair K 1)) x →
        InW (plusPair K 0) (flipPair (plusPair K 1)) (g x) := fun g hg x hx =>
    (hWiff _).2 (apply_mem_spanU₄_of_commute h24 hYL' hYW' hyo hYm hY1 hg ((hWiff x).1 hx))
  have hpresU : ∀ g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K), g * φ y = φ y * g →
      ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
        g u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) := fun g hg u hu =>
    (hUiff _).1 (inW_apply_of_commute h24 hYL' hYW' hyo hYm hY1 hg ((hUiff u).2 hu))
  have hfixW : ∀ x ∈ stabTwoBar K 2 3, ∀ w, InW (plusPair K 0) (flipPair (plusPair K 1)) w →
      φ x w = w := by
    intro x hx w hw
    obtain ⟨⟨x1, x2⟩, x3, x4⟩ := (mem_map_projHom_iff hQ').mp hx
    have hw' := (hWiff w).1 hw
    rw [hspan] at hw'
    exact fix_spanU₄_of_fix h23 x1 x2 x3 x4 w hw'
  obtain ⟨a1, a2⟩ := inW_of_orth (orth_symm h02) (orth_symm h12)
  obtain ⟨b1, b2⟩ := inW_of_orth (orth_symm h03) (orth_symm h13)
  have hS1 : S ≤ stabTwoBar K 2 3 := by
    refine hSgen _ ?_ ?_
    · rw [mem_stabTwoBar_iff hQ', projLift_plusZ hQ']
      exact ⟨⟨eichler_apply_of_inW a1, eichler_apply_of_inW a2⟩, eichler_apply_of_inW b1,
        eichler_apply_of_inW b2⟩
    · intro s hs n hn
      rw [mem_stabTwoBar_iff hQ']
      have hsi : (φ s)⁻¹ * φ y = φ y * (φ s)⁻¹ := by
        rw [← map_inv]; exact hcY (hSy (inv_mem hs))
      have key : ∀ w, InW (plusPair K 0) (flipPair (plusPair K 1)) w → φ (s * n * s⁻¹) w = w := by
        intro w hw
        have hw' := hpresW _ hsi w hw
        rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          hfixW n hn _ hw', LinearEquiv.apply_inv_apply']
      exact ⟨⟨key _ a1, key _ a2⟩, key _ b1, key _ b2⟩
  have hJ0A : leviFixBar (plusPair K 0) (plusPair K 1) ≤
      centralizer (leviFixBar (plusPair K 0) (flipPair (plusPair K 1)) :
        Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :=
    leviFixBar_le_centralizer_flip h01 hQ hT
  have hS2 : S ≤ leviFixBar (plusPair K 0) (plusPair K 1) ⊔ stabTwoBar K 0 1 := by
    refine hSgen _ (mem_sup_left plusZ_mem_leviFixBar) ?_
    intro s hs n hn
    obtain ⟨j, hj, a, ha, hja⟩ := exists_mul_of_mem_stabTwoBar hq (show (2 : Fin 4) ≠ 3 by decide)
      (show (0 : Fin 4) ≠ 1 by decide) (by decide) (by decide) (by decide) (by decide) (hS1 hs)
    have hj1 : ∀ x ∈ leviFixBar (plusPair K 0) (plusPair K 1), j * x * j⁻¹ ∈
        leviFixBar (plusPair K 0) (plusPair K 1) := fun x hx =>
      mul_mem (mul_mem hj hx) (inv_mem hj)
    have hj2 : ∀ x ∈ stabTwoBar K 0 1, j * x * j⁻¹ ∈ stabTwoBar K 0 1 :=
      conj_mem_of_commute fun x hx => leviFixBar_commute_stabTwoBar_zero_one (Or.inl rfl) hj hx
    have ha1 : ∀ x ∈ leviFixBar (plusPair K 0) (plusPair K 1), a * x * a⁻¹ ∈
        leviFixBar (plusPair K 0) (plusPair K 1) :=
      conj_mem_of_commute fun x hx => mem_centralizer_iff.mp (hJ0A hx) a ha
    have ha2 : ∀ x ∈ stabTwoBar K 0 1, a * x * a⁻¹ ∈ stabTwoBar K 0 1 :=
      conj_mem_of_commute fun x hx => leviFixBar_commute_stabTwoBar_zero_one (Or.inr rfl) ha hx
    have h1 := conj_mem_sup_of_forall ha1 ha2 hn
    have h2 := conj_mem_sup_of_forall hj1 hj2 h1
    rw [hja, show j * a * n * (j * a)⁻¹ = j * (a * n * a⁻¹) * j⁻¹ by group]
    exact h2
  have hS3 : S ≤ leviFixBar (plusPair K 0) (plusPair K 1) := by
    intro s hs
    obtain ⟨j, hj, b, hb, hjb⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (H₁ := leviFixBar (plusPair K 0) (plusPair K 1)) (H₂ := stabTwoBar K 0 1)
      (fun x hx => mem_centralizer_iff.mpr fun c hc =>
        (leviFixBar_commute_stabTwoBar_zero_one (Or.inl rfl) hx hc).symm) (hS2 hs)
    obtain ⟨-, -, hjW⟩ := mem_leviFix.mp (projLift_mem_leviFix hQ' hj)
    have hsW := hfixW _ (hS1 hs)
    have hbW : ∀ w, InW (plusPair K 0) (flipPair (plusPair K 1)) w → φ b w = w := by
      intro w hw
      have h1 := hsW w hw
      rw [hjb, map_mul, LinearEquiv.mul_apply] at h1
      have h2 : φ j w = w := hjW w (inW_flip_iff.mp hw)
      exact (φ j).injective (h1.trans h2.symm)
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := (mem_map_projHom_iff hQ').mp hb
    have hbU := fix_spanU₄_of_fix h01 c1 c2 c3 c4
    rw [← spanU₄_flip (P₁ := plusPair K 0) (P₂ := plusPair K 1)] at hbU
    have hb1 : φ b = 1 := eq_one_of_fix_spanU₄_of_fixW h₁₂ hbU hbW
    have hb1' : b = 1 := hφi (hb1.trans (map_one φ).symm)
    rw [hjb, hb1', mul_one]
    exact hj
  have hpres_r : ∀ r ∈ R, ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
      φ r u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) := fun r hr =>
    hpresU _ (hcY (hRy hr))
  have hpres_rinv : ∀ r ∈ R, ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
      (φ r)⁻¹ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) := fun r hr u hu => by
    rw [← map_inv]; exact hpres_r _ (inv_mem hr) u hu
  have hdec : ∀ r ∈ R, ∃ a ∈ leviFix (orthDerived (coordinateQuadPlus 4 K)) (plusPair K 0)
      (flipPair (plusPair K 1)), ∃ γ : K, ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
        φ r u = (a * eichler (coordinateQuadPlus 4 K) (plusPair K 0).e
          (γ • (flipPair (plusPair K 1)).e)) u := by
    intro r hr
    have hgO : φ r ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K) :=
      Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ' r)
    have hgc : φ r * eichler (coordinateQuadPlus 4 K) (plusPair K 0).e (flipPair (plusPair K 1)).e =
        eichler (coordinateQuadPlus 4 K) (plusPair K 0).e (flipPair (plusPair K 1)).e * φ r := by
      have h := hcommφ (mem_centralizer_singleton_iff.mp (hRz hr))
      rwa [show φ (plusZ K) = eichler (coordinateQuadPlus 4 K) (plusPair K 0).e
        (flipPair (plusPair K 1)).e from projLift_plusZ hQ'] at h
    obtain ⟨a, ha, γ, hγ⟩ := exists_leviFix_eichler_of_commute h₁₂ hE hgO hgc (hpres_r r hr)
    exact ⟨a, ha, γ, fun u hu => by rw [LinearEquiv.mul_apply]; exact hγ u hu⟩
  let HA : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    { carrier := {r | ∃ a ∈ leviFix (orthDerived (coordinateQuadPlus 4 K)) (plusPair K 0)
        (flipPair (plusPair K 1)), ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
          φ r u = a u}
      mul_mem' := by
        rintro r₁ r₂ ⟨c₁, hc₁, e₁⟩ ⟨c₂, hc₂, e₂⟩
        refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, fun u hu => ?_⟩
        rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, e₂ u hu,
          e₁ _ (rootLevi_apply_mem_spanU₄ h₁₂ (mem_leviFix.mp hc₂).2.1 hu)]
      one_mem' := ⟨1, one_mem _, fun u _ => by rw [map_one]⟩
      inv_mem' := by
        rintro r ⟨c, hc, e⟩
        refine ⟨c⁻¹, inv_mem hc, fun u hu => ?_⟩
        have hcu : c⁻¹ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) :=
          rootLevi_apply_mem_spanU₄ h₁₂ (inv_mem (mem_leviFix.mp hc).2.1) hu
        rw [map_inv]
        apply (φ r).injective
        rw [LinearEquiv.apply_inv_apply', e _ hcu, LinearEquiv.apply_inv_apply'] }
  have hRA : R ≤ HA := by
    rw [← hRperf, Subgroup.commutator_le]
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨c₁, hc₁, γ₁, e₁⟩ := hdec r₁ hr₁
    obtain ⟨c₂, hc₂, γ₂, e₂⟩ := hdec r₂ hr₂
    refine ⟨⁅c₁, c₂⁆, by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂), fun u hu => ?_⟩
    have key := commutator_apply_eq_of_agree (hpres_rinv r₁ hr₁) (hpres_r r₂ hr₂)
      (hpres_rinv r₂ hr₂) e₁ e₂ u hu
    have hid := commutatorElement_mul_mul_of_commute
      (leviFix_commute_eichler h₁₂ hE hc₁ γ₂) (leviFix_commute_eichler h₁₂ hE hc₂ γ₁)
      (rootGroup_commute (eichler_smul_mem_rootGroup_left h₁₂.ee γ₁)
        (eichler_smul_mem_rootGroup_left h₁₂.ee γ₂))
    change φ ⁅r₁, r₂⁆ u = ⁅c₁, c₂⁆ u
    rw [map_commutatorElement, key, hid]
  have hfl : leviFix (orthDerived (coordinateQuadPlus 4 K)) (plusPair K 0) (plusPair K 1) ≤
      centralizer (leviFix (orthDerived (coordinateQuadPlus 4 K)) (plusPair K 0)
        (flipPair (plusPair K 1)) : Set ((Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) :=
    leviFix_le_centralizer_flip h01 hE hE
  intro s hs
  rw [mem_centralizer_iff]
  intro r hr
  obtain ⟨c, hc, hcr⟩ := hRA hr
  have hsJ := projLift_mem_leviFix hQ' (hS3 hs)
  obtain ⟨-, hsL, hsW'⟩ := mem_leviFix.mp hsJ
  have hsW : ∀ x, InW (plusPair K 0) (plusPair K 1) x → φ s x = x := hsW'
  have hsc : φ s * c = c * φ s := (mem_centralizer_iff.mp (hfl hsJ) c hc).symm
  have hrW := hpresW _ (hcY (hRy hr))
  have hsU : ∀ u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)),
      φ s u ∈ spanU₄ (plusPair K 0) (flipPair (plusPair K 1)) := by
    intro u hu
    rw [spanU₄_flip] at hu ⊢
    exact rootLevi_apply_mem_spanU₄ h01 hsL hu
  have hfin : φ r * φ s = φ s * φ r := by
    refine LinearEquiv.ext fun x => ?_
    have hw := inW_sub_uPart h₁₂ x
    have hu := uPart_mem_spanU₄ (P₁ := plusPair K 0) (P₂ := flipPair (plusPair K 1)) x
    have hcs := LinearEquiv.congr_fun hsc (uPart (plusPair K 0) (flipPair (plusPair K 1)) x)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hcs
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      eq_sub_uPart_add (P₁ := plusPair K 0) (P₂ := flipPair (plusPair K 1)) x,
      map_add, map_add, map_add, map_add, hsW _ (inW_flip_iff.mp hw),
      hsW _ (inW_flip_iff.mp (hrW _ hw)), hcr _ (hsU _ hu), hcr _ hu, hcs]
  apply hφi
  rw [map_mul, map_mul]
  exact hfin

end ModelB

end CFSG.SeitzReduction.OmegaPilot
