module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap CFSG.Open CFSG.ClassicalGroups.PCoreSection
  CFSG.RankThree.OrthogonalInvolutions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commSpace_eichler_le_span (u w : V) :
    commSpace (eichler Q u w) ≤ Submodule.span K {u, w} := by
  intro y hy
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_apply h.1 h.2]
    have e : x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u - x =
        polar Q x u • w + (-(polar Q x w + Q w * polar Q x u)) • u := by module
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [eichler_of_not h, LinearEquiv.coe_one, id, sub_self]
    exact Submodule.zero_mem _

theorem span_le_commSpace_eichler [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (hli : LinearIndependent K ![u, w]) :
    Submodule.span K {u, w} ≤ commSpace (eichler Q u w) := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ hli
  have h00 : polar Q u (g 0) = 1 := by simpa using hg 0 0
  have h01 : polar Q u (g 1) = 0 := by simpa using hg 0 1
  have h10 : polar Q w (g 0) = 0 := by simpa using hg 1 0
  have h11 : polar Q w (g 1) = 1 := by simpa using hg 1 1
  have hu1 : u ∈ commSpace (eichler Q u w) := by
    have hmem := sub_mem_commSpace (eichler Q u w) (g 1)
    rw [eichler_apply hu hw, polar_comm Q (g 1) u, polar_comm Q (g 1) w, h01, h11] at hmem
    have e : g 1 + (0 : K) • w - (1 + Q w * 0) • u - g 1 = -u := by module
    rw [e] at hmem
    simpa using Submodule.neg_mem _ hmem
  have hw1 : w ∈ commSpace (eichler Q u w) := by
    have hmem := sub_mem_commSpace (eichler Q u w) (g 0)
    rw [eichler_apply hu hw, polar_comm Q (g 0) u, polar_comm Q (g 0) w, h00, h10] at hmem
    have e : g 0 + (1 : K) • w - (0 + Q w * 1) • u - g 0 = w - Q w • u := by module
    rw [e] at hmem
    have := Submodule.add_mem _ hmem (Submodule.smul_mem _ (Q w) hu1)
    simpa using this
  refine Submodule.span_le.mpr ?_
  rintro z (rfl | rfl)
  · exact hu1
  · exact hw1

theorem even_finrank_commSpace_eichler [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (u w : V) :
    Even (finrank K (commSpace (eichler Q u w))) := by
  have hone : ∀ {g : V ≃ₗ[K] V}, g = 1 → Even (finrank K (commSpace g)) := by
    rintro g rfl
    have : commSpace (1 : V ≃ₗ[K] V) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
      rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]
    rw [this, finrank_bot]
    exact ⟨0, rfl⟩
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  swap
  · exact hone (eichler_of_not h)
  by_cases hli : LinearIndependent K ![u, w]
  · have heq : commSpace (eichler Q u w) = Submodule.span K {u, w} :=
      le_antisymm (commSpace_eichler_le_span u w) (span_le_commSpace_eichler hQ h.1 h.2 hli)
    rw [heq]
    have := finrank_span_eq_card hli
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Fintype.card_fin] at this
    rw [this]
    exact even_two
  · refine hone ?_
    rw [LinearIndependent.pair_iff] at hli
    push Not at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    by_cases ht : t = 0
    · subst ht
      have hs : s ≠ 0 := fun hs => hne hs rfl
      rw [zero_smul, add_zero] at hst
      have hu0 : u = 0 := (smul_eq_zero.mp hst).resolve_left hs
      rw [hu0]
      exact eichler_zero_left Q w
    · have hw : w = (-(t⁻¹ * s)) • u := by
        have h1 : t • w = -(s • u) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
        calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(t⁻¹ * s)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
      have := eichler_add_smul_self (Q := Q) h.1 0 (-(t⁻¹ * s))
      rw [zero_add, ← hw, eichler_zero_right] at this
      exact this

theorem elementaryGroup_le_omegaGroup [FiniteDimensional K V] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) : elementaryGroup Q ≤ omegaGroup Q hQ := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨u, w, -, -, rfl⟩
  exact ⟨eichler_mem_orthogonalGroup Q u w, even_finrank_commSpace_eichler hQ u w⟩

theorem linearIndependent_of_polar_eq_one {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (h : polar Q u u' = 1) : LinearIndependent K ![u, u'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (polar Q u) hst
  have h2 := congrArg (polar Q u') hst
  have hu'u : polar Q u' u = 1 := by rw [polar_comm, h]
  simp only [polar_add_right, polar_smul_right_eq, polar_self_eq_zero hu, polar_self_eq_zero hu',
    h, hu'u, polar_zero_right] at h1 h2
  exact ⟨by linear_combination h2, by linear_combination h1⟩

theorem finrank_span_pair_eq_two {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (h : polar Q u u' = 1) : Module.finrank K (Submodule.span K {u, u'}) = 2 := by
  have := finrank_span_eq_card (linearIndependent_of_polar_eq_one hu hu' h)
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at this
  exact this

theorem Lom_eq_pCoreOf_pointStabilizer_four [FiniteDimensional K V] [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 4) {u : V} (hu : u ≠ 0)
    (hQu : Q u = 0) : Lom Q u = pCoreOf 2 (pointStabilizer Q u) := by
  haveI : Finite V := Module.finite_of_finite K
  refine le_antisymm (Lom_le_pCoreOf_pointStabilizer u) fun t ht => ?_
  have htS : t ∈ pointStabilizer Q u := pCoreOf_le 2 _ ht
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_pCoreOf 2 (pointStabilizer Q u) ⟨t, ht⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨c, hc⟩ := htS
  have hc1 : c = 1 := eq_one_of_apply_eq_smul (isLinearAction_Gom Q) hk hu hc
  rw [hc1, one_smul] at hc
  obtain ⟨Pr, hPr⟩ := exists_hypPair hQ hQu hu
  have huu' : polar Q u Pr.f = 1 := by rw [← hPr]; exact Pr.polar_ef
  obtain ⟨s, hs, h, -, hhu, hhu', hth⟩ := exists_mem_rootGroup_mul_eq hQu Pr.Q_f
    (by rw [huu']; exact one_ne_zero) (elementaryGroup_le_orthogonalGroup Q t.2) hc
  let s' : Gom Q := ⟨s, rootGroup_le_elementaryGroup Q u hs⟩
  have hs' : s' ∈ Lom Q u := mem_Lom.mpr hs
  let h' : Gom Q := s'⁻¹ * t
  have hh'eq : (h' : V ≃ₗ[K] V) = h := by
    show s⁻¹ * (t : V ≃ₗ[K] V) = h
    rw [hth, inv_mul_cancel_left]
  have hh'T : h' ∈ pCoreOf 2 (pointStabilizer Q u) :=
    mul_mem (inv_mem (Lom_le_pCoreOf_pointStabilizer u hs')) ht
  have hh'u : h'.app u = u := by
    show (h' : V ≃ₗ[K] V) u = u
    rw [hh'eq]
    exact hhu
  have hh'u' : h'.app Pr.f = Pr.f := by
    show (h' : V ≃ₗ[K] V) Pr.f = Pr.f
    rw [hh'eq]
    exact hhu'
  let H₀ : Subgroup (Gom Q) :=
    { carrier := {g | g.app u = u ∧ g.app Pr.f = Pr.f}
      one_mem' := ⟨rfl, rfl⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨by rw [Gom.app_mul, hb.1, ha.1], by rw [Gom.app_mul, hb.2, ha.2]⟩
      inv_mem' := fun {a} ha =>
        ⟨by have := Gom.app_inv_app a u; rwa [ha.1] at this,
          by have := Gom.app_inv_app a Pr.f; rwa [ha.2] at this⟩ }
  have hA : Module.finrank K (Submodule.span K {u, Pr.f}) = 2 :=
    finrank_span_pair_eq_two hQu Pr.Q_f huu'
  have hW₀dim : Module.finrank K
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, Pr.f})) = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hA]
  have hP : ∀ g ∈ pCoreOf 2 (pointStabilizer Q u) ⊓ H₀,
      ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, Pr.f}),
        g.app x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, Pr.f}) := by
    intro g hg x hx
    obtain ⟨hgu, hgf⟩ := hg.2
    obtain ⟨hxu, hxf⟩ := mem_orth_span_pair_iff.mp hx
    refine mem_orth_span_pair_iff.mpr ⟨?_, ?_⟩
    · have := Gom.polar_app g u x
      rwa [hgu, hxu] at this
    · have := Gom.polar_app g Pr.f x
      rwa [hgf, hxf] at this
  have hne : (⊥ : Submodule K V) ≠
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, Pr.f}) := by
    intro hbot
    have : Module.finrank K
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, Pr.f})) = 0 := by
      rw [← hbot, finrank_bot]
    omega
  obtain ⟨x, hxW, hx0, hxfix⟩ := exists_fixed_mem_of_isPGroup (isLinearAction_Gom Q)
    (T := pCoreOf 2 (pointStabilizer Q u) ⊓ H₀) ((isPGroup_pCoreOf 2 _).to_le inf_le_left)
    (L := ⊥) bot_le hP
    (fun g _ y hy => by rw [(Submodule.mem_bot K).mp hy, Gom.app_zero]; exact Submodule.zero_mem _)
    hne
  have hh'x : h'.app x = x := by
    have := hxfix h' ⟨hh'T, hh'u, hh'u'⟩
    rwa [Submodule.mem_bot, sub_eq_zero] at this
  have hxne : x ≠ 0 := fun h0 => hx0 (by rw [h0]; exact Submodule.zero_mem _)
  have hdisj : Disjoint (Submodule.span K {u, Pr.f}) (Submodule.span K {x}) := by
    rw [Submodule.disjoint_def]
    intro y hyA hyB
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyB
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hyA
    obtain ⟨hxu, hxf⟩ := mem_orth_span_pair_iff.mp hxW
    have h1 := congrArg (polar Q u) hab
    have h2 := congrArg (polar Q Pr.f) hab
    have hfu : polar Q Pr.f u = 1 := by rw [polar_comm, huu']
    simp only [polar_add_right, polar_smul_right_eq, polar_self_eq_zero hQu,
      polar_self_eq_zero Pr.Q_f, huu', hfu, hxu, hxf, mul_zero, zero_add, add_zero] at h1 h2
    have ha : a = 0 := by linear_combination h2
    have hb : b = 0 := by linear_combination h1
    rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]
  have hsup : Module.finrank K
      ↥(Submodule.span K {u, Pr.f} ⊔ Submodule.span K {x}) = 3 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {u, Pr.f})
      (Submodule.span K {x})
    rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton hxne, hA] at h1
    omega
  have hfix : Submodule.span K {u, Pr.f} ⊔ Submodule.span K {x} ≤
      fixSpace (h' : V ≃ₗ[K] V) := by
    refine sup_le (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro y (rfl | rfl)
      · exact mem_fixSpace.mpr hh'u
      · exact mem_fixSpace.mpr hh'u'
    · rintro y rfl
      exact mem_fixSpace.mpr hh'x
  have hle := Submodule.finrank_mono hfix
  have hdimsum := finrank_commSpace_add_finrank_fixSpace (h' : V ≃ₗ[K] V)
  have heven : Even (Module.finrank K (commSpace (h' : V ≃ₗ[K] V))) :=
    (elementaryGroup_le_omegaGroup hQ h'.2).2
  have hone : (h' : V ≃ₗ[K] V) = 1 := by
    by_contra hne1
    have := one_le_finrank_commSpace hne1
    obtain ⟨r, hr⟩ := heven
    omega
  have hts : t = s' := (inv_mul_eq_one.mp (Subtype.ext hone)).symm
  rw [hts]
  exact hs'

theorem Lom_eq_pCoreOf_pointStabilizer_of_four_le [FiniteDimensional K V] [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0)
    (hQu : Q u = 0) : Lom Q u = pCoreOf 2 (pointStabilizer Q u) := by
  rcases Nat.lt_or_ge (Module.finrank K V) 5 with h | h
  · exact Lom_eq_pCoreOf_pointStabilizer_four hQ (by omega) hu hQu
  · exact Lom_eq_pCoreOf_pointStabilizer hQ h hu hQu

end CFSG.ClassicalGroups.Orthogonal
