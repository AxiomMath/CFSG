module

public import CFSG.LargeExtraspecial.A2ModFrBKlein
public import CFSG.LargeExtraspecial.A2ModFrBGen
public import CFSG.LieType.Universal.SpinOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint
open scoped commutatorElement

section Lines

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem le_sup_of_inf_ne_bot_of_inf_eq_bot {ℓ L₁ L₂ : Submodule (ZMod 2) V}
    (hℓ : finrank (ZMod 2) ℓ = 2) (h₁ : ℓ ⊓ L₁ ≠ ⊥) (h₂ : ℓ ⊓ L₂ ≠ ⊥) (h₁₂ : L₁ ⊓ L₂ = ⊥) :
    ℓ ≤ L₁ ⊔ L₂ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp h₁
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp h₂
  rw [Submodule.mem_inf] at hx hy
  have hxy : x ≠ y := fun h => hx0 (by
    have : x ∈ L₁ ⊓ L₂ := Submodule.mem_inf.mpr ⟨hx.2, h ▸ hy.2⟩
    rwa [h₁₂, Submodule.mem_bot] at this)
  rw [Grid.eq_span_of_mem hℓ hx.1 hy.1 hx0 hy0 hxy, Submodule.span_le]
  rintro z (rfl | rfl)
  · exact Submodule.mem_sup_left hx.2
  · exact Submodule.mem_sup_right hy.2

theorem span_inf_span_eq_bot {n : ℕ} {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V}
    (hP : Function.Injective P) (hPd : Function.Injective Pd)
    (hPP : LinearMap.range P ⊓ LinearMap.range Pd = ⊥) {v v' φ φ' : Fin n → ZMod 2}
    (hv : v ≠ v') (hφ : φ ≠ φ') :
    Submodule.span (ZMod 2) {P v, Pd φ} ⊓ Submodule.span (ZMod 2) {P v', Pd φ'} = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hz₁, hz₂⟩ := Submodule.mem_inf.mp hz
  obtain ⟨a, b', rfl⟩ := Submodule.mem_span_pair.mp hz₁
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hz₂
  have hmem : P (a • v - c • v') ∈ LinearMap.range P ⊓ LinearMap.range Pd := by
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self P _, d • φ' - b' • φ, ?_⟩
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, map_smul]
    rw [← sub_eq_zero] at hcd ⊢
    rw [← hcd]
    abel
  rw [hPP, Submodule.mem_bot, ← map_zero P] at hmem
  have h1 : a • v = c • v' := sub_eq_zero.mp (hP hmem)
  have h2 : b' • φ = d • φ' := by
    have e : Pd (b' • φ - d • φ') = P (c • v' - a • v) := by
      rw [map_sub, map_sub, map_smul, map_smul, map_smul, map_smul]
      rw [← sub_eq_zero] at hcd ⊢
      have e' : b' • Pd φ - d • Pd φ' - (c • P v' - a • P v) =
          -(c • P v' + d • Pd φ' - (a • P v + b' • Pd φ)) := by abel
      rw [e', hcd, neg_zero]
    have hmem' : Pd (b' • φ - d • φ') ∈ LinearMap.range P ⊓ LinearMap.range Pd :=
      Submodule.mem_inf.mpr ⟨⟨_, e.symm⟩, LinearMap.mem_range_self Pd _⟩
    rw [hPP, Submodule.mem_bot, ← map_zero Pd] at hmem'
    exact sub_eq_zero.mp (hPd hmem')
  have key : ∀ {x y : Fin n → ZMod 2} {s t : ZMod 2}, x ≠ y → s • x = t • y → s • x = 0 := by
    intro x y s t hxy h
    rcases zmodTwo_eq_zero_or_one s with rfl | rfl
    · exact zero_smul _ _
    · rcases zmodTwo_eq_zero_or_one t with rfl | rfl
      · rwa [zero_smul] at h
      · rw [one_smul, one_smul] at h
        exact absurd h hxy
  rw [Submodule.mem_bot, ← map_smul, ← map_smul, key hv h1, key hφ h2, map_zero, map_zero,
    add_zero]

end Lines

section Partner

variable {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem extra_mul_lrAC (h2 : (2 : K) = 0) (p : Fin 2 → K) :
    extra hn hirr p * lr n b c (iC_ne_iA hn).symm true false =
      (twShortRoot n hirr (iB hn) true (.ofAdd p) * lr n b c (iC_ne_iB hn).symm true false) *
        lr n b c (iA_ne_iB hn) true false *
        (twShortRoot n hirr (iB hn) true (.ofAdd p) *
          lr n b c (iC_ne_iB hn).symm true false)⁻¹ := by
  rw [extra]
  set tw := twShortRoot n hirr (iB hn) true (.ofAdd p)
  set ℓ := lr n b c (iA_ne_iB hn) true false
  set g := lr n b c (iC_ne_iB hn).symm true false
  set μ := lr n b c (iC_ne_iA hn).symm true false
  have hμtw : Commute μ tw :=
    commute_longRoot_twShortRoot_of_ne n hirr (iC_ne_iA hn).symm (iA_ne_iB hn).symm
      (iC_ne_iB hn).symm true false true 1 p
  have hℓμ : Commute ℓ μ := HypFrame.commute_longRoot_longRoot_left _ _ _ _ _ _ _ _
  have hcomm := commutator_lr (b := b) (c := c) (iC_ne_iB hn) (iA_ne_iB hn).symm
    (iC_ne_iA hn) false true true
  rw [Bool.not_true, lr_swap h2 (iC_ne_iB hn) false true,
    lr_swap h2 (iA_ne_iB hn).symm false true, lr_swap h2 (iC_ne_iA hn) false true] at hcomm
  have e : g * ℓ * g⁻¹ = μ * ℓ := by
    rw [mul_mul_inv_eq_commutatorElement_mul, hcomm]
  calc tw * ℓ * tw⁻¹ * μ = tw * ℓ * (tw⁻¹ * μ) := by group
    _ = tw * ℓ * (μ * tw⁻¹) := by rw [hμtw.inv_right.eq]
    _ = tw * (ℓ * μ) * tw⁻¹ := by group
    _ = tw * (μ * ℓ) * tw⁻¹ := by rw [hℓμ.eq]
    _ = tw * (g * ℓ * g⁻¹) * tw⁻¹ := by rw [e]
    _ = tw * g * ℓ * (tw * g)⁻¹ := by group

end Partner

section Four

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {K : Type} [Field K] [Finite K] {b c : K}

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_of_isConj_of_conj_mem (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D) {x y : X} (hx : x ∈ D)
    (hxy : IsConj x y) : y ∈ D := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  exact hDc g x hx

theorem range_leviZ_le_range_kleinZ (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) :
    (leviZ 4 b c le_rfl hirr hK).range ≤ (kleinZ b c hirr hK).range := by
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup
      (ι := Fin (4 - 1)) (F := ZMod 2))) := by
    rw [SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, j, hij, a⟩, rfl⟩ := hx
    rw [TransvectionStruct.toSpecialLinearGroup_mk]
    rcases zmodTwo_eq_zero_or_one a with rfl | rfl
    · rw [show SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 from
        Subtype.ext (by rw [SpecialLinearGroup.transvection_coe, single_zero, add_zero]; rfl),
        map_one]
      exact one_mem _
    · rw [← elemTv_eq_transvection hij, leviZ_elemTv_eq_lr 4 le_rfl hirr hK hij]
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact ⟨_, kleinZ_E12 hirr hK⟩
        | exact ⟨_, kleinZ_E21 hirr hK⟩
        | exact ⟨_, kleinZ_E13 hirr hK⟩
        | exact ⟨_, kleinZ_E31 hirr hK⟩
        | exact ⟨_, kleinZ_E23 hirr hK⟩
        | exact ⟨_, kleinZ_E32 hirr hK⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

omit [Finite K] in
theorem lr_eq_of_eq {n : ℕ} {i j i' j' : Fin (n - 1)} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (s t : Bool) : lr n b c hij s t = lr n b c hij' s t := by
  subst hi hj
  rfl

theorem range_kleinZ_sup_eq_top (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    (kleinZ b c hirr hK).range ⊔ Subgroup.zpowers (extra le_rfl hirr planeOne) ⊔
      Subgroup.zpowers (extra le_rfl hirr planeTwo) = ⊤ := by
  rw [eq_top_iff, ← genB_eq_top le_rfl hirr hK]
  have hA : nodeA b c (le_rfl : 4 ≤ 4) ∈ (kleinZ b c hirr hK).range := by
    rw [nodeA, lr_eq_of_eq (iA_ne_iB le_rfl) (by decide : (1 : Fin (4 - 1)) ≠ 2) (by decide)
      (by decide)]
    exact ⟨_, kleinZ_E01 hirr hK⟩
  have hB : nodeB b c (le_rfl : 4 ≤ 4) ∈ (kleinZ b c hirr hK).range := by
    rw [nodeB, lr_eq_of_eq (iA_ne_iB le_rfl) (by decide : (1 : Fin (4 - 1)) ≠ 2) (by decide)
      (by decide)]
    exact ⟨_, kleinZ_E10 hirr hK⟩
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) (le_sup_right.trans le_sup_left)) le_sup_right
  · exact (range_leviZ_le_range_kleinZ hirr hK).trans (le_sup_left.trans le_sup_left)
  · exact (Subgroup.zpowers_le.mpr hA).trans (le_sup_left.trans le_sup_left)
  · exact (Subgroup.zpowers_le.mpr hB).trans (le_sup_left.trans le_sup_left)

theorem finrank_commSpaceOf_top_le_nine (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (Ψ : spinGroup (quadMinus 4 K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {i₀ j₀ : Fin (4 - 1)} (h₀ : i₀ ≠ j₀)
    (hmem : Ψ (lr 4 b c h₀ true false) ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 9 := by
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
  rcases exists_isPointMaps_or_finrank_le hA' le_rfl with ⟨P, Pd, hP⟩ | hle
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
    norm_num
  ·
    rw [← commSpaceOf_range] at hle
    have e₁ := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := Ψ₄.range)
      (hextra planeOne) (hall _ _ _) hδH (hcoll₁ planeOne)
    have e₂ := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
      (H := Ψ₄.range ⊔ Subgroup.zpowers (Ψ (extra le_rfl hirr planeOne))) (hextra planeTwo)
      (hall _ _ _) (Subgroup.mem_sup_left hδH) (hcoll₁ planeTwo)
    rw [htop] at e₂
    omega

end Four

end CFSG.LargeExtraspecial.A2Mod.FrB
