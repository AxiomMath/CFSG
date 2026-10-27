module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHR7iii

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

section Fix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_fixed_ne_zero_of_isPGroup_of_le [CharP K 2] [Finite V]
    (N : Subgroup (V ≃ₗ[K] V)) (hN : IsPGroup 2 N) {U : Submodule K V} (hU : U ≠ ⊥)
    (hP : ∀ g ∈ N, ∀ v ∈ U, g v ∈ U) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ g ∈ N, g u = u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heU, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  let act : MulAction N U :=
    { smul := fun g p => ⟨(g : V ≃ₗ[K] V) p, hP g g.2 p p.2⟩
      one_smul := fun p => Subtype.ext rfl
      mul_smul := fun g h p => Subtype.ext rfl }
  have h2 : 2 ∣ Nat.card U := by
    have hord : addOrderOf (⟨e, heU⟩ : U) = 2 := by
      apply addOrderOf_eq_prime
      · apply Subtype.ext
        change (2 : ℕ) • e = 0
        rw [two_nsmul, ← two_smul K e, CharTwo.two_eq_zero, zero_smul]
      · intro h0
        exact he (congrArg Subtype.val h0)
    rw [← hord]
    exact addOrderOf_dvd_natCard _
  have h0 : (0 : U) ∈ MulAction.fixedPoints N U := fun g => Subtype.ext (map_zero _)
  obtain ⟨u, hu, hu0⟩ := hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point U h2 h0
  refine ⟨u, u.2, fun h => hu0 (Subtype.ext h.symm), fun g hg => ?_⟩
  exact congrArg Subtype.val (hu ⟨g, hg⟩)

end Fix

section Frame

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {Q : QuadraticForm K (ι → K)}

theorem IsHypCoord.eichler_single_sub {c c' e e' : ι} (hc : IsHypCoord Q c c')
    (he : IsHypCoord Q e e') (hce : PairDisjoint c c' e e') (x : ι → K) :
    eichler Q (Pi.single c 1) (Pi.single e 1) x - x =
      x c' • Pi.single e 1 - x e' • Pi.single c 1 := by
  have hpol : polar Q (Pi.single c 1) (Pi.single e 1) = 0 := by
    rw [hc.polar_left, Pi.single_eq_of_ne hce.left_ne_right.symm]
  rw [eichler_apply hc.map_left hpol, he.map_left, zero_mul, add_zero,
    polar_comm Q x (Pi.single c 1), hc.polar_left, polar_comm Q x (Pi.single e 1), he.polar_left]
  abel

theorem frame_mem_of_eichler_invariant {c c' e e' : ι} (hc : IsHypCoord Q c c')
    (he : IsHypCoord Q e e') (hce : PairDisjoint c c' e e') {U : Submodule K (ι → K)}
    (h₁ : ∀ x ∈ U, eichler Q (Pi.single c 1) (Pi.single e 1) x ∈ U)
    (h₂ : ∀ x ∈ U, eichler Q (Pi.single c 1) (Pi.single e' 1) x ∈ U)
    (h₃ : ∀ x ∈ U, eichler Q (Pi.single c' 1) (Pi.single e 1) x ∈ U)
    (h₄ : ∀ x ∈ U, eichler Q (Pi.single c' 1) (Pi.single e' 1) x ∈ U)
    {x : ι → K} (hx : x ∈ U) (hx0 : x c ≠ 0 ∨ x c' ≠ 0 ∨ x e ≠ 0 ∨ x e' ≠ 0) :
    Pi.single c 1 ∈ U ∧ Pi.single c' 1 ∈ U ∧ Pi.single e 1 ∈ U ∧ Pi.single e' 1 ∈ U := by
  have n1 : c ≠ c' := hc.ne
  have n2 : e ≠ e' := he.ne
  have n3 : c ≠ e := hce.left_ne_left.symm
  have n4 : c' ≠ e := hce.left_ne_right.symm
  have n5 : c ≠ e' := hce.right_ne_left.symm
  have n6 : c' ≠ e' := hce.right_ne_right.symm
  have d₁ : ∀ y ∈ U, y c' • Pi.single e 1 - y e' • Pi.single c 1 ∈ U := fun y hy => by
    rw [← hc.eichler_single_sub he hce]
    exact U.sub_mem (h₁ y hy) hy
  have d₂ : ∀ y ∈ U, y c' • Pi.single e' 1 - y e • Pi.single c 1 ∈ U := fun y hy => by
    rw [← hc.eichler_single_sub he.symm hce.swap_right]
    exact U.sub_mem (h₂ y hy) hy
  have d₃ : ∀ y ∈ U, y c • Pi.single e 1 - y e' • Pi.single c' 1 ∈ U := fun y hy => by
    rw [← hc.symm.eichler_single_sub he hce.swap_left]
    exact U.sub_mem (h₃ y hy) hy
  have d₄ : ∀ y ∈ U, y c • Pi.single e' 1 - y e • Pi.single c' 1 ∈ U := fun y hy => by
    rw [← hc.symm.eichler_single_sub he.symm hce.swap_left.swap_right]
    exact U.sub_mem (h₄ y hy) hy
  have hsm : ∀ (t : K) (v : ι → K), t ≠ 0 → t • v ∈ U → v ∈ U := fun t v ht h => by
    have := U.smul_mem t⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have stepA : ∀ y ∈ U, y c ≠ 0 → Pi.single c' 1 ∈ U := by
    intro y hy hyc
    have h := d₄ _ (d₃ y hy)
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne n3,
      Pi.single_eq_of_ne n1, Pi.single_eq_of_ne n4.symm, smul_eq_mul, mul_zero, mul_one,
      sub_zero, zero_smul, zero_sub] at h
    rw [← neg_smul] at h
    exact hsm _ _ (neg_ne_zero.mpr hyc) h
  have stepB : ∀ y ∈ U, y c' ≠ 0 → Pi.single c 1 ∈ U := by
    intro y hy hyc
    have h := d₂ _ (d₁ y hy)
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne n4,
      Pi.single_eq_of_ne n1.symm, Pi.single_eq_of_ne n3.symm, smul_eq_mul, mul_zero, mul_one,
      sub_zero, zero_smul, zero_sub] at h
    rw [← neg_smul] at h
    exact hsm _ _ (neg_ne_zero.mpr hyc) h
  have hc' : Pi.single c' (1 : K) ∈ U := by
    rcases hx0 with h | h | h | h
    · exact stepA x hx h
    · exact stepA _ (stepB x hx h) (by simp)
    · refine stepA _ (d₂ x hx) ?_
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne n5,
        smul_eq_mul, mul_zero, mul_one, zero_sub]
      exact neg_ne_zero.mpr h
    · refine stepA _ (d₁ x hx) ?_
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne n3,
        smul_eq_mul, mul_zero, mul_one, zero_sub]
      exact neg_ne_zero.mpr h
  have hcU : Pi.single c (1 : K) ∈ U := stepB _ hc' (by simp)
  have hE : Pi.single e (1 : K) ∈ U := by
    have h := d₃ _ hcU
    simpa [Pi.single_eq_of_ne n5.symm] using h
  have hE' : Pi.single e' (1 : K) ∈ U := by
    have h := d₄ _ hcU
    simpa [Pi.single_eq_of_ne n3.symm] using h
  exact ⟨hcU, hc', hE, hE'⟩

end Frame

section OTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem rootLeviBar_normal_isPGroup_eq_bot_of_frame (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {c c' e e' : Fin d} (hc : IsHypCoord Q c c') (he : IsHypCoord Q e e')
    (hce : PairDisjoint c c' e e') (hac : PairDisjoint a a' c c') (hae : PairDisjoint a a' e e')
    (hbc : PairDisjoint b b' c c') (hbe : PairDisjoint b b' e e')
    (hall : ∀ s : Fin d, s = a ∨ s = a' ∨ s = b ∨ s = b' ∨ s = c ∨ s = c' ∨ s = e ∨ s = e')
    (N : Subgroup (rootLeviBar Q hi.hypPair hj.hypPair))
    (hNn : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₁₂ := hi.orth hj hd
  have hρ := projHom_injective (Q := Q) hi.exists_ne_zero
  set N' : Subgroup (matrixProjectiveDerived (Q)) := N.map (Subgroup.subtype _)
    with hN'
  have hN'le : N' ≤ rootLeviBar (Q) hi.hypPair hj.hypPair := map_subtype_le N
  have hN'2 : IsPGroup 2 N' := hN2.map _
  have hN'norm : ∀ m ∈ rootLeviBar (Q) hi.hypPair hj.hypPair, ∀ x ∈ N',
      m * x * m⁻¹ ∈ N' := by
    rintro m hm _ ⟨⟨x', hx'M⟩, hx'N, rfl⟩
    exact ⟨⟨m, hm⟩ * ⟨x', hx'M⟩ * ⟨m, hm⟩⁻¹, hNn.conj_mem _ hx'N _, rfl⟩
  set Nl := N'.comap (projHom (Q)) with hNl
  have hNl2 : IsPGroup 2 Nl := hN'2.comap_of_injective _ hρ
  have hNlM : ∀ X ∈ Nl, ((X : orthDerived _) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      rootLevi _ hi.hypPair hj.hypPair := by
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := hN'le hX
    rw [hρ hYX] at hY
    exact mem_subgroupOf.mp hY
  have hNlconj : ∀ m : orthDerived (Q),
      (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi _ hi.hypPair hj.hypPair →
      ∀ X ∈ Nl, m⁻¹ * X * m ∈ Nl := by
    intro m hm X hX
    have hmM : projHom _ m ∈ rootLeviBar (Q) hi.hypPair hj.hypPair :=
      ⟨m, mem_subgroupOf.mpr hm, rfl⟩
    change projHom _ (m⁻¹ * X * m) ∈ N'
    have h := hN'norm _ (inv_mem hmM) _ hX
    rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at h
  set Nlin := Nl.map (orthDerived (Q)).subtype with hNlin
  have hNlin2 : IsPGroup 2 Nlin := hNl2.map _
  have hP : ∀ g ∈ Nlin, ∀ v ∈ Submodule.span K {hi.hypPair.e, hj.hypPair.e},
      g v ∈ Submodule.span K {hi.hypPair.e, hj.hypPair.e} := by
    rintro _ ⟨X, hX, rfl⟩ v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ (mem_centralizer_singleton_iff.mp (hNlM X hX).1.2)
    set g := ((X : orthDerived (Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K))
      with hgdef
    refine Submodule.mem_span_pair.mpr
      ⟨a * polar (Q) (g hj.hypPair.f) hj.hypPair.e -
        b * polar (Q) (g hi.hypPair.f) hj.hypPair.e,
      b * polar (Q) (g hi.hypPair.f) hi.hypPair.e -
        a * polar (Q) (g hj.hypPair.f) hi.hypPair.e, ?_⟩
    simp only [Subgroup.coe_subtype, map_add, map_smul]
    rw [h1, h2]
    module
  obtain ⟨u, huP, hu0, hu⟩ := exists_fixed_ne_zero_of_isPGroup Nlin hNlin2 hi.hypPair.e_ne_zero hP
  have hinv : ∀ m : orthDerived (Q),
      (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi _ hi.hypPair hj.hypPair →
      ∀ v, (∀ g ∈ Nlin, g v = v) → ∀ g ∈ Nlin,
        g ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
          (m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v := by
    rintro m hm v hv _ ⟨X, hX, rfl⟩
    have h := hv _ ⟨m⁻¹ * X * m, hNlconj m hm X hX, rfl⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      LinearEquiv.mul_apply] at h ⊢
    calc (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
          ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
        (m : (Fin d → K) ≃ₗ[K] (Fin d → K))
          (((m : (Fin d → K) ≃ₗ[K] (Fin d → K)))⁻¹
            ((X : (Fin d → K) ≃ₗ[K] (Fin d → K))
              ((m : (Fin d → K) ≃ₗ[K] (Fin d → K)) v))) := by
          rw [LinearEquiv.apply_inv_apply']
      _ = _ := by rw [h]
  have hsub : ∀ v w, (∀ g ∈ Nlin, g v = v) → (∀ g ∈ Nlin, g w = w) →
      ∀ g ∈ Nlin, g (v - w) = v - w := fun v w hv hw g hg => by rw [map_sub, hv g hg, hw g hg]
  have hsmul : ∀ (c : K) v, c ≠ 0 → (∀ g ∈ Nlin, g (c • v) = c • v) → ∀ g ∈ Nlin, g v = v :=
    fun c v hc hv g hg => by
      have h := hv g hg
      rw [map_smul] at h
      exact smul_right_injective _ hc h
  have hx1 : eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f) ∈
      orthDerived (Q) := eichler_mem_orthDerived hQ hT _ _
  have hy1 : eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f) ∈
      orthDerived (Q) := eichler_mem_orthDerived hQ hT _ _
  have hxM := eichler_smul_f_mem_rootLevi h₁₂ (1 : K)
  have hyM := eichler_smul_f_mem_rootLevi' h₁₂ (1 : K)
  have hFx := hinv ⟨_, hx1⟩ hxM
  have hFy := hinv ⟨_, hy1⟩ hyM
  have hx_e : ∀ c d : K, eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f)
      (c • hi.hypPair.e + d • hj.hypPair.e) - (c • hi.hypPair.e + d • hj.hypPair.e) =
        (-d) • hi.hypPair.e := by
    intro c d
    rw [map_add, map_smul, map_smul, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₁₂]
    module
  have hy_e : ∀ c d : K, eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f)
      (c • hi.hypPair.e + d • hj.hypPair.e) - (c • hi.hypPair.e + d • hj.hypPair.e) =
        (-c) • hj.hypPair.e := by
    intro c d
    rw [map_add, map_smul, map_smul, eichler_smul_f_apply_e, eichler_smul_f_apply_e' h₁₂.symm]
    module
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp huP
  have hFe : (∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e) ∧
      ∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e := by
    have he₁ : (∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e) →
        ∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e := by
      intro h1
      have h := hsub _ _ (hFy _ h1) h1
      have e : eichler (Q) hj.hypPair.e ((1 : K) • hi.hypPair.f)
          hi.hypPair.e - hi.hypPair.e = (-1 : K) • hj.hypPair.e := by
        have := hy_e 1 0
        simpa using this
      exact hsmul (-1) _ (neg_ne_zero.mpr one_ne_zero) (by rw [← e]; exact h)
    have he₂ : (∀ g ∈ Nlin, g hj.hypPair.e = hj.hypPair.e) →
        ∀ g ∈ Nlin, g hi.hypPair.e = hi.hypPair.e := by
      intro h2
      have h := hsub _ _ (hFx _ h2) h2
      have e : eichler (Q) hi.hypPair.e ((1 : K) • hj.hypPair.f)
          hj.hypPair.e - hj.hypPair.e = (-1 : K) • hi.hypPair.e := by
        have := hx_e 0 1
        simpa using this
      exact hsmul (-1) _ (neg_ne_zero.mpr one_ne_zero) (by rw [← e]; exact h)
    by_cases hβ : β = 0
    · have hα : α ≠ 0 := by
        rintro rfl
        apply hu0
        rw [hβ]
        simp
      have h := hsub _ _ (hFy _ hu) hu
      rw [hy_e] at h
      have h2 := hsmul (-α) _ (neg_ne_zero.mpr hα) h
      exact ⟨he₂ h2, h2⟩
    · have h := hsub _ _ (hFx _ hu) hu
      rw [hx_e] at h
      have h1 := hsmul (-β) _ (neg_ne_zero.mpr hβ) h
      exact ⟨h1, he₁ h1⟩
  have hfixN : ∀ g ∈ Nlin, g (Pi.single a 1) = Pi.single a 1 ∧
      g (Pi.single a' 1) = Pi.single a' 1 ∧ g (Pi.single b 1) = Pi.single b 1 ∧
      g (Pi.single b' 1) = Pi.single b' 1 := by
    rintro _ ⟨X, hXNl, rfl⟩
    have hXM := hNlM X hXNl
    have hg : ((X : orthDerived _) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ Nlin :=
      ⟨X, hXNl, rfl⟩
    have h1 := hFe.1 _ hg
    have h2 := hFe.2 _ hg
    obtain ⟨hf1, hf2⟩ := apply_e_of_commute (orth_flipPair_flipPair h₁₂)
      (mem_centralizer_singleton_iff.mp hXM.2)
    simp only [flipPair_e, flipPair_f, h1, h2, hi.hypPair.polar_ef, hj.hypPair.polar_ef,
      one_smul] at hf1 hf2
    rw [polar_comm _ hj.hypPair.e hi.hypPair.f, h₁₂.fe, zero_smul, sub_zero] at hf1
    rw [h₁₂.ef, zero_smul, sub_zero] at hf2
    exact ⟨h1, hf1, h2, hf2⟩
  have hgO : ∀ g ∈ Nlin, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨X, -, rfl⟩
    exact Subgroup.commutator_le_self _ X.2
  have hWinv : ∀ g ∈ Nlin, ∀ v ∈ perpSub K a a' ⊓ perpSub K b b',
      g v ∈ perpSub K a a' ⊓ perpSub K b b' := by
    intro g hg v hv
    obtain ⟨h1, h2, h3, h4⟩ := hfixN g hg
    exact ⟨hi.apply_mem_perpSub (hgO g hg) ⟨h1, h2⟩ hv.1,
      hj.apply_mem_perpSub (hgO g hg) ⟨h3, h4⟩ hv.2⟩
  have hsW : ∀ s : Fin d, s ≠ a → s ≠ a' → s ≠ b → s ≠ b' →
      (Pi.single s (1 : K) : Fin d → K) ∈ perpSub K a a' ⊓ perpSub K b b' :=
    fun s h1 h2 h3 h4 => ⟨single_mem_perpSub h1 h2, single_mem_perpSub h3 h4⟩
  have hcW := hsW c hac.left_ne_left hac.left_ne_right hbc.left_ne_left hbc.left_ne_right
  have hc'W := hsW c' hac.right_ne_left hac.right_ne_right hbc.right_ne_left hbc.right_ne_right
  have heW := hsW e hae.left_ne_left hae.left_ne_right hbe.left_ne_left hbe.left_ne_right
  have he'W := hsW e' hae.right_ne_left hae.right_ne_right hbe.right_ne_left hbe.right_ne_right
  have hW0 : perpSub K a a' ⊓ perpSub K b b' ≠ ⊥ := by
    intro h
    have h0 := h ▸ hcW
    rw [Submodule.mem_bot] at h0
    have := congrFun h0 c
    simp at this
  obtain ⟨w₀, hw₀W, hw₀0, hw₀⟩ := exists_fixed_ne_zero_of_isPGroup_of_le Nlin hNlin2 hW0 hWinv
  let U : Submodule K (Fin d → K) :=
    { carrier := {v | ∀ g ∈ Nlin, g v = v}
      add_mem' := fun {v w} hv hw g hg => by rw [map_add, hv g hg, hw g hg]
      zero_mem' := fun g _ => map_zero g
      smul_mem' := fun t v hv g hg => by rw [map_smul, hv g hg] }
  have hUE : ∀ x y : Fin d → K, x ∈ perpSub K a a' ⊓ perpSub K b b' →
      y ∈ perpSub K a a' ⊓ perpSub K b b' → ∀ v ∈ U, eichler Q x y v ∈ U := by
    intro x y hx hy v hv
    have hEO : eichler Q x y ∈ orthDerived Q := eichler_mem_orthDerived hQ hT x y
    have hS1 := hi.eichler_mem_stabSub hx.1 hy.1
    have hS2 := hj.eichler_mem_stabSub hx.2 hy.2
    have hEM : eichler Q x y ∈ rootLevi Q hi.hypPair hj.hypPair :=
      mem_rootLevi_of_fix (Subgroup.commutator_le_self _ hEO) hS1.1 hS1.2 hS2.1 hS2.2
    exact hinv ⟨_, hEO⟩ hEM v hv
  have hx0 : w₀ c ≠ 0 ∨ w₀ c' ≠ 0 ∨ w₀ e ≠ 0 ∨ w₀ e' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    apply hw₀0
    funext s
    rcases hall s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw₀W.1.1
    · exact hw₀W.1.2
    · exact hw₀W.2.1
    · exact hw₀W.2.2
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  obtain ⟨hUc, hUc', hUe, hUe'⟩ := frame_mem_of_eichler_invariant hc he hce
    (hUE _ _ hcW heW) (hUE _ _ hcW he'W) (hUE _ _ hc'W heW) (hUE _ _ hc'W he'W)
    (U := U) (x := w₀) hw₀ hx0
  have hone : ∀ g ∈ Nlin, g = 1 := by
    intro g hg
    obtain ⟨h1, h2, h3, h4⟩ := hfixN g hg
    have hs : ∀ s : Fin d, g (Pi.single s 1) = Pi.single s 1 := by
      intro s
      rcases hall s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact hUc g hg
      · exact hUc' g hg
      · exact hUe g hg
      · exact hUe' g hg
    have hlin : (g : (Fin d → K) →ₗ[K] (Fin d → K)) = LinearMap.id := by
      refine LinearMap.pi_ext fun s t => ?_
      have hst : (Pi.single s t : Fin d → K) = t • Pi.single s 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hst, LinearMap.map_smul, LinearEquiv.coe_coe, hs s, LinearMap.id_apply]
    exact LinearEquiv.ext fun v => by
      have := LinearMap.congr_fun hlin v
      simpa using this
  have hN'bot : N' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨X, rfl⟩ := projHom_surjective _ x
    have hXNl : X ∈ Nl := hx
    have hX1 : X = 1 := Subtype.ext (hone _ ⟨X, hXNl, rfl⟩)
    rw [hX1, map_one]
    exact one_mem _
  exact (Subgroup.map_eq_bot_iff_of_injective N (Subgroup.subtype_injective _)).mp hN'bot

end OTwo

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_compl_pair_fin_four {i j : Fin 4} (hij : i ≠ j) :
    ∃ k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      ∀ s : Fin 4, s = i ∨ s = j ∨ s = k ∨ s = l := by
  revert i j
  decide

theorem plusLevi_normal_isPGroup_eq_bot_four {i j : Fin 4} (hij : i ≠ j)
    (N : Subgroup (plusLevi K i j)) (hNn : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨k, l, hik, hil, hjk, hjl, hkl, hall⟩ := exists_compl_pair_fin_four hij
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  refine rootLeviBar_normal_isPGroup_eq_bot_of_frame (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hij) hQ hT
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus l) (pairDisjoint_plus hkl)
    (pairDisjoint_plus hik) (pairDisjoint_plus hil) (pairDisjoint_plus hjk) (pairDisjoint_plus hjl)
    (fun s => ?_) N hNn hN2
  obtain ⟨t, rfl⟩ := (plusIndexEquiv 4).surjective s
  rcases t with t | t <;> rcases hall t with rfl | rfl | rfl | rfl <;> simp

theorem plusFourLeviInput_holds : PlusFourLeviInput := by
  intro K _ _ _ hq i j hij
  exact ⟨commutator_stabTwoBar_four hq hij, plusLevi_normal_isPGroup_eq_bot_four hij⟩

end Four

end CFSG.SeitzReduction.OmegaPilot
