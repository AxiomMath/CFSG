module

public import CFSG.LargeExtraspecial.AS35YUSL4
public import CFSG.LargeExtraspecial.A2ModFrBFinal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YU

open Module Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint A2Mod A2Mod.FrB
open scoped commutatorElement

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {K : Type} [Field K] [Finite K] {b c : K}

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
  rcases exists_isPointMaps_or_finrank_le_six hA' with ⟨P, Pd, hP⟩ | hle
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


theorem frame_finrank_commSpaceOf_top_le_eight {n : ℕ} (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) (hn : n = 4) (hK : Nat.card K = 2)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (Ψ : spinGroup (quadMinus n K b c) →* X)
    (hsurj : Function.Surjective Ψ) {i₀ : Fin (n - 1)} (hi₀ : i₀.val + 1 < n - 1) {d : X}
    (hd : d ∈ D)
    (hmem : ((minusDatum n hirr).rootGroup (Pi.single i₀ 1)).map Ψ = Subgroup.zpowers d) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  subst hn
  have h := map_lr_eq_of_map_rootGroup hirr hK Ψ hi₀ (hA.ne_one hd) (hA.mul_self hd) hmem
  exact finrank_commSpaceOf_top_le_eight hirr hK Ψ hsurj hDc hA _ (h ▸ hd)

end CFSG.LargeExtraspecial.AS35YU
