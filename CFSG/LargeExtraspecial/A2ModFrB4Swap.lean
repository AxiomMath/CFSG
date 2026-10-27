module

public import CFSG.LargeExtraspecial.A2ModFrB4
public import CFSG.LargeExtraspecial.A2ModFrB5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint
open scoped commutatorElement

section J

variable {K : Type} [Field K] {b c : K}

noncomputable def jFour : spinGroup (quadMinus 4 K b c) :=
  wSwap (b := b) (c := c) (by decide : (0 : Fin (4 - 1)) ≠ 1) *
    (minusFrame 4 b c).shortWeyl 2 true

theorem spinAction_jFour_vec (h2 : (2 : K) = 0) (m : Fin (4 - 1)) (r : Bool) :
    spinAction (quadMinus 4 K b c) (jFour (b := b) (c := c)) (minusVec 4 m r) =
      minusVec 4 m (!r) := by
  have e := (minusFrame 4 b c).spinAction_shortWeyl_vec 2 true m r
  simp only [minusFrame_vec, longWeylSign_eq_one h2, one_smul] at e
  rw [jFour, map_mul, LinearEquiv.mul_apply, e, spinAction_wSwap_vec h2]
  fin_cases m <;> simp [shortWeylBool]

theorem jFour_conj_lr (h2 : (2 : K) = 0) {i j : Fin (4 - 1)} (hij : i ≠ j) (s t : Bool) :
    jFour * lr 4 b c hij s t * jFour⁻¹ = lr 4 b c hij (!s) (!t) := by
  have hi := spinAction_jFour_vec (b := b) (c := c) h2 i s
  have hj := spinAction_jFour_vec (b := b) (c := c) h2 j t
  rw [← one_smul K (minusVec 4 i (!s))] at hi
  rw [← one_smul K (minusVec 4 j (!t))] at hj
  rw [lr, (minusFrame 4 b c).conj_longRoot _ hij s t hij (!s) (!t) hi hj, one_mul, one_mul]

end J

@[expose] def elemTvEight : Set (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  {elemTv 0 1, elemTv 1 0, elemTv 1 2, elemTv 2 1, elemTv 1 3, elemTv 3 1, elemTv 2 3, elemTv 3 2}

theorem closure_elemTv_eight_eq_top : Subgroup.closure elemTvEight = ⊤ := by
  set H := Subgroup.closure elemTvEight with hH
  have hmem : ∀ x ∈ elemTvEight, x ∈ H := fun x hx => Subgroup.subset_closure hx
  have hcomm : ∀ {a b : SpecialLinearGroup (Fin 4) (ZMod 2)}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H :=
    fun ha hb => by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have h01 : elemTv 0 1 ∈ H := hmem _ (by simp [elemTvEight])
  have h10 : elemTv 1 0 ∈ H := hmem _ (by simp [elemTvEight])
  have h12 : elemTv 1 2 ∈ H := hmem _ (by simp [elemTvEight])
  have h21 : elemTv 2 1 ∈ H := hmem _ (by simp [elemTvEight])
  have h13 : elemTv 1 3 ∈ H := hmem _ (by simp [elemTvEight])
  have h31 : elemTv 3 1 ∈ H := hmem _ (by simp [elemTvEight])
  have h23 : elemTv 2 3 ∈ H := hmem _ (by simp [elemTvEight])
  have h32 : elemTv 3 2 ∈ H := hmem _ (by simp [elemTvEight])
  have h02 : elemTv 0 2 ∈ H := by
    rw [elemTv_eq_commutator (l := 1) (by decide) (by decide) (by decide)]
    exact hcomm h01 h12
  have h20 : elemTv 2 0 ∈ H := by
    rw [elemTv_eq_commutator (l := 1) (by decide) (by decide) (by decide)]
    exact hcomm h21 h10
  have h03 : elemTv 0 3 ∈ H := by
    rw [elemTv_eq_commutator (l := 1) (by decide) (by decide) (by decide)]
    exact hcomm h01 h13
  have h30 : elemTv 3 0 ∈ H := by
    rw [elemTv_eq_commutator (l := 1) (by decide) (by decide) (by decide)]
    exact hcomm h31 h10
  have hall : ∀ (i j : Fin 4) (hij : i ≠ j), elemTv i j ∈ H := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | assumption
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, a⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · rw [show SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 from
      Subtype.ext (by rw [SpecialLinearGroup.transvection_coe, single_zero, add_zero]; rfl)]
    exact H.one_mem
  · rw [← elemTv_eq_transvection hij]
    exact hall i j hij

section Klein

variable {K : Type} [Field K] [Finite K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
include hirr hK

theorem jFour_conj_kleinZ (g : SpecialLinearGroup (Fin 4) (ZMod 2)) :
    jFour * kleinZ b c hirr hK g * jFour⁻¹ = kleinZ b c hirr hK (tinv g) := by
  have h2 := two_eq_zero_of_card hK
  set f₁ : SpecialLinearGroup (Fin 4) (ZMod 2) →* spinGroup (quadMinus 4 K b c) :=
    (MulAut.conj (jFour (b := b) (c := c))).toMonoidHom.comp (kleinZ b c hirr hK)
  set f₂ : SpecialLinearGroup (Fin 4) (ZMod 2) →* spinGroup (quadMinus 4 K b c) :=
    (kleinZ b c hirr hK).comp tinv
  have hc : ∀ x, f₁ x = jFour * kleinZ b c hirr hK x * jFour⁻¹ := fun x => rfl
  have hd : ∀ x, f₂ x = kleinZ b c hirr hK (tinv x) := fun x => rfl
  have hf : f₁ = f₂ := by
    refine MonoidHom.eq_of_eqOn_dense closure_elemTv_eight_eq_top ?_
    intro x hx
    simp only [elemTvEight, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [hc, hd]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tinv_tv, kleinZ_E01 hirr hK, jFour_conj_lr h2, kleinZ_E10 hirr hK]
      rfl
    · rw [tinv_tv, kleinZ_E10 hirr hK, jFour_conj_lr h2, kleinZ_E01 hirr hK]
      rfl
    · rw [tinv_tv, kleinZ_E12 hirr hK, jFour_conj_lr h2, kleinZ_E21 hirr hK, lr_swap h2]
      rfl
    · rw [tinv_tv, kleinZ_E21 hirr hK, jFour_conj_lr h2, kleinZ_E12 hirr hK, lr_swap h2]
      rfl
    · rw [tinv_tv, kleinZ_E13 hirr hK, jFour_conj_lr h2, kleinZ_E31 hirr hK, lr_swap h2]
      rfl
    · rw [tinv_tv, kleinZ_E31 hirr hK, jFour_conj_lr h2, kleinZ_E13 hirr hK, lr_swap h2]
      rfl
    · rw [tinv_tv, kleinZ_E23 hirr hK, jFour_conj_lr h2, kleinZ_E32 hirr hK, lr_swap h2]
      rfl
    · rw [tinv_tv, kleinZ_E32 hirr hK, jFour_conj_lr h2, kleinZ_E23 hirr hK, lr_swap h2]
      rfl
  have := congrArg (fun f => f g) hf
  simpa only [hc, hd] using this

end Klein

section Strong

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem exists_isPointMaps_or_finrank_le_six {Ψ : SpecialLinearGroup (Fin 4) (ZMod 2) →* X}
    (hA' : A2Action (transvectionSet 4 (ZMod 2)) Q (ρ.comp Ψ)) (J : X)
    (hJ : ∀ v φ : Fin 4 → ZMod 2, φ ⬝ᵥ v = 0 → Ψ (tv φ v) = J * Ψ (tv v φ) * J⁻¹) :
    (∃ P Pd, IsPointMaps (ρ.comp Ψ) Q P Pd) ∨
      finrank (ZMod 2) (commSpaceOf (ρ.comp Ψ) ⊤) ≤ 6 := by
  set e : Fin 4 → ZMod 2 := Pi.single 0 1 with he_def
  have he : e ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hAB : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g) := by
    rintro ⟨P, hP0, hP⟩
    refine ⟨ρ J P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun g hg hg1 => ?_⟩
    obtain ⟨v, hv, rfl⟩ := mem_hyperplaneGroup.mp hg
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hg1 (tv_zero_left _)
    have hve : v ⬝ᵥ e = 0 := by rwa [dotProduct_comm]
    have hmem := apply_mem_commSpace_conj ρ J
      (hP (tv e v) (tv_mem_pointGroup e v) (tv_ne_one he hv0 hve))
    rw [← hJ e v hve] at hmem
    exact hmem
  have hBA : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g) := by
    rintro ⟨P, hP0, hP⟩
    refine ⟨ρ J P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun g hg hg1 => ?_⟩
    obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp hg
    have hφ0 : φ ≠ 0 := by
      rintro rfl
      exact hg1 (tv_zero_right _)
    have heφ : e ⬝ᵥ φ = 0 := by rwa [dotProduct_comm]
    have hmem := apply_mem_commSpace_conj ρ J
      (hP (tv φ e) (tv_mem_hyperplaneGroup φ e) (tv_ne_one hφ0 he heφ))
    rw [← hJ φ e heφ] at hmem
    exact hmem
  by_cases hc : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) ∧
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)
  · obtain ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      exists_pointMaps_of_concurrent hA' le_rfl he he hc.1 hc.2
    exact Or.inl ⟨P, Pd, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩
  · have hnA := fun hcA => hc ⟨hcA, hAB hcA⟩
    have hnB := fun hcB => hc ⟨hBA hcB, hcB⟩
    have h1 := (hA'.common_point_or_finrank_le_three (A := pointGroup e)
      forall_mem_pointGroup_mem_transvectionSet).resolve_left hnA
    have h2 := (hA'.common_point_or_finrank_le_three (A := hyperplaneGroup e)
      forall_mem_hyperplaneGroup_mem_transvectionSet).resolve_left hnB
    have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ.comp Ψ) (0 : Fin 4)
    rw [← he_def] at h3
    exact Or.inr (by omega)

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem finrank_commSpaceOf_top_le_eight (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (Ψ : spinGroup (quadMinus 4 K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {i₀ j₀ : Fin (4 - 1)} (h₀ : i₀ ≠ j₀)
    (hmem : Ψ (lr 4 b c h₀ true false) ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  have h2 := two_eq_zero_of_card hK
  have hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D := fun x hx g => hDc g x hx
  have hall := fun {i j : Fin (4 - 1)} (hij : i ≠ j) (s t : Bool) =>
    map_lr_mem Ψ hcls le_rfl hirr hK h₀ hmem hij s t
  set Ψ₄ := Ψ.comp (kleinZ b c hirr hK) with hΨ₄_def
  have hΨ₄ : ∀ g ∈ transvectionSet 4 (ZMod 2), Ψ₄ g ∈ D := by
    intro g hg
    obtain ⟨v, φ, hv, hφ, h, rfl⟩ := mem_transvectionSet.mp hg
    have hc : IsConj (elemTv (2 : Fin 4) 1) (tv v φ) :=
      isConj_tv (Pi.single_ne_zero_iff.mpr one_ne_zero) (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (single_dotProduct_single_of_ne (by decide)) hv hφ h
    have hc' := MonoidHom.map_isConj Ψ₄ hc
    rw [hΨ₄_def, MonoidHom.comp_apply, kleinZ_E21 hirr hK] at hc'
    exact mem_of_isConj_of_conj_mem hDc (hall _ _ _) hc'
  have hA' := (hA.comp_sl (by norm_num) hΨ₄).2
  have hJ : ∀ v φ : Fin 4 → ZMod 2, φ ⬝ᵥ v = 0 →
      Ψ₄ (tv φ v) = Ψ jFour * Ψ₄ (tv v φ) * (Ψ jFour)⁻¹ := by
    intro v φ _
    rw [hΨ₄_def, MonoidHom.comp_apply, MonoidHom.comp_apply, ← tinv_tv,
      ← jFour_conj_kleinZ hirr hK, map_mul, map_mul, map_inv]
  have htop : Ψ₄.range ⊔ Subgroup.zpowers (Ψ (extra le_rfl hirr planeOne)) ⊔
      Subgroup.zpowers (Ψ (extra le_rfl hirr planeTwo)) = ⊤ := by
    have e := congrArg (Subgroup.map Ψ) (range_kleinZ_sup_eq_top hirr hK)
    rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      ← MonoidHom.range_comp, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj] at e
    exact e
  have hδ : Ψ (xδ (b := b) (c := c) (le_rfl : 4 ≤ 4)) = Ψ₄ (elemTv 0 3) := by
    rw [hΨ₄_def, MonoidHom.comp_apply, kleinZ_E03 hirr hK, xδ,
      lr_eq_of_eq (iC_ne_iA le_rfl) (by decide : (0 : Fin (4 - 1)) ≠ 1) (by decide) (by decide)]
  have hμ : Ψ (lr 4 b c (iC_ne_iA (le_rfl : 4 ≤ 4)).symm true false) = Ψ₄ (elemTv 2 1) := by
    rw [hΨ₄_def, MonoidHom.comp_apply, kleinZ_E21 hirr hK,
      lr_eq_of_eq (iC_ne_iA le_rfl).symm (by decide : (1 : Fin (4 - 1)) ≠ 0) (by decide)
        (by decide)]
  have hδH : Ψ (xδ (b := b) (c := c) (le_rfl : 4 ≤ 4)) ∈ Ψ₄.range := by
    rw [hδ]
    exact ⟨_, rfl⟩
  have hμH : Ψ (lr 4 b c (iC_ne_iA (le_rfl : 4 ≤ 4)).symm true false) ∈ Ψ₄.range := by
    rw [hμ]
    exact ⟨_, rfl⟩
  have hextra : ∀ p : Fin 2 → K, Ψ (extra le_rfl hirr p) ∈ D := fun p =>
    map_conj_mem Ψ hcls (hall _ _ _) _
  have hcoll₁ : ∀ p : Fin 2 → K,
      Ψ (extra le_rfl hirr p) * Ψ (xδ (b := b) (c := c) le_rfl) ∈ D := fun p => by
    rw [← map_mul, extra_mul_xδ le_rfl hirr h2]
    exact map_conj_mem Ψ hcls (hall _ _ _) _
  have hcoll₂ : ∀ p : Fin 2 → K,
      Ψ (extra le_rfl hirr p) * Ψ (lr 4 b c (iC_ne_iA le_rfl).symm true false) ∈ D :=
    fun p => by
      rw [← map_mul, extra_mul_lrAC le_rfl hirr h2]
      exact map_conj_mem Ψ hcls (hall _ _ _) _
  rcases exists_isPointMaps_or_finrank_le_six hA' (Ψ jFour) hJ with ⟨P, Pd, hP⟩ | hle
  ·
    have L₁ : commSpace (ρ (Ψ (xδ (b := b) (c := c) le_rfl))) =
        Submodule.span (ZMod 2) {P (Pi.single 0 1), Pd (Pi.single 3 1)} := by
      rw [hδ, ← MonoidHom.comp_apply ρ Ψ₄]
      exact hP.commSpace_tv _ _ (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (Pi.single_ne_zero_iff.mpr one_ne_zero) (single_dotProduct_single_of_ne (by decide))
    have L₂ : commSpace (ρ (Ψ (lr 4 b c (iC_ne_iA le_rfl).symm true false))) =
        Submodule.span (ZMod 2) {P (Pi.single 2 1), Pd (Pi.single 1 1)} := by
      rw [hμ, ← MonoidHom.comp_apply ρ Ψ₄]
      exact hP.commSpace_tv _ _ (Pi.single_ne_zero_iff.mpr one_ne_zero)
        (Pi.single_ne_zero_iff.mpr one_ne_zero) (single_dotProduct_single_of_ne (by decide))
    have hdisj := span_inf_span_eq_bot hP.injective hP.injective_dual hP.range_inf_range
      (single_ne_single (by decide : (0 : Fin 4) ≠ 2))
      (single_ne_single (by decide : (3 : Fin 4) ≠ 1))
    have hline : ∀ p : Fin 2 → K,
        commSpace (ρ (Ψ (extra le_rfl hirr p))) ≤ commSpaceOf ρ Ψ₄.range := by
      intro p
      have m₁ := hA.inf_commSpace_ne_bot (hextra p) (hall _ _ _) (hcoll₁ p)
      have m₂ := hA.inf_commSpace_ne_bot (hextra p) (hall _ _ _) (hcoll₂ p)
      rw [L₁] at m₁
      rw [L₂] at m₂
      refine (le_sup_of_inf_ne_bot_of_inf_eq_bot (hA.isTypeA (hextra p)).2.2.2.1 m₁ m₂
        hdisj).trans (sup_le ?_ ?_)
      · rw [← L₁]
        exact commSpace_le_commSpaceOf ρ hδH
      · rw [← L₂]
        exact commSpace_le_commSpaceOf ρ hμH
    have heq : commSpaceOf ρ ⊤ = commSpaceOf ρ Ψ₄.range := by
      rw [← htop, commSpaceOf_sup_zpowers, commSpaceOf_sup_zpowers, sup_eq_left.mpr (hline _),
        sup_eq_left.mpr (hline _)]
    rw [heq, commSpaceOf_range, hP.finrank_commSpaceOf_top]
  ·
    rw [← commSpaceOf_range] at hle
    have e₁ := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := Ψ₄.range)
      (hextra planeOne) (hall _ _ _) hδH (hcoll₁ planeOne)
    have e₂ := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
      (H := Ψ₄.range ⊔ Subgroup.zpowers (Ψ (extra le_rfl hirr planeOne))) (hextra planeTwo)
      (hall _ _ _) (Subgroup.mem_sup_left hδH) (hcoll₁ planeTwo)
    rw [htop] at e₂
    omega

end Strong

end CFSG.LargeExtraspecial.A2Mod.FrB
