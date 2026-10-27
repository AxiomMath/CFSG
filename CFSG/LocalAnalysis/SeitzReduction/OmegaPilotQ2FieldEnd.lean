module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBounds

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT incl)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed)

section Plus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_plusFieldGlobal (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F))
    (hgen : ∀ Φ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G,
      (∀ x, Φ (fieldEmbed ι n (by omega) x) = ((e.symm x : L) : G)) → Φ.range ≤ G₀)
    (h : G) (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) :
    CFSG.conjugate G₀ h = G₀ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨f, hf1, hKc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus (by omega) hf1 hKc e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  set Ψ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G :=
    (MulAut.conj h⁻¹).toMonoidHom.comp (G₀.subtype.comp ψ₀.symm.toMonoidHom) with hΨ
  have hinj : Function.Injective Ψ :=
    (MulAut.conj h⁻¹).injective.comp (G₀.subtype_injective.comp ψ₀.symm.injective)
  have hrange : Ψ.range = CFSG.conjugate G₀ h := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₀.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htM)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  have hC := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
  have hCt : (fixedSubgroup β).map Ψ ≤ centralizer ({t} : Set G) := by
    rw [← hC]
    exact inf_le_right
  rcases involution_cases_omegaPlus hn hσ hββ with ⟨s, hs1, hsβ⟩ | ⟨ψ', hψ'⟩ |
      ⟨k, _, _, _, b, c, hirr, hk, N, hNβ, hNperf, ⟨eN⟩⟩
  ·
    exfalso
    apply omegaPlusLinearInvolutionInput_holds hn K F hFK s hs1
    rw [hsβ]
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt hCt
    rwa [Subgroup.card_map_of_injective hinj] at hdvd
  ·
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_fieldEmbed_eq hset.standardSetting hOut hn e htC ht ι hfix
      hinj hβ hψ'
    have hle : CFSG.conjugate G₀ h ≤ G₀ := by
      rw [← hrange, ← hΦr]
      exact hgen Φ hΦ
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  ·
    exfalso
    have hkK : Nat.card k = Nat.card K :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hk.trans hFK)
    have hNt : N.map Ψ ≤ centralizer ({t} : Set G) := (Subgroup.map_mono hNβ).trans hCt
    have hNperf' : ⁅N.map Ψ, N.map Ψ⁆ = N.map Ψ := by
      rw [← Subgroup.map_commutator, hNperf]
    have hNL : N.map Ψ ≤ L := std_perfect_le hset.standardSetting hOut htC ht hNperf' hNt
    have h1 : Nat.card (N.map Ψ) ≤ Nat.card L := Subgroup.card_le_of_le hNL
    rw [Subgroup.card_map_of_injective hinj, Nat.card_congr eN.toEquiv,
      Nat.card_congr e.toEquiv] at h1
    exact absurd h1 (not_le.2 (card_coordinatePlus_lt_card_coordinateMinus (by omega) hkK hirr))

theorem false_of_plusFieldGlobal (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (htN : t ∈ normalizer (G₀ : Set G))
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F))
    (hgen : ∀ Φ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G,
      (∀ x, Φ (fieldEmbed ι n (by omega) x) = ((e.symm x : L) : G)) → Φ.range ≤ G₀) :
    False := by
  have huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) →
      g ∈ normalizer (G₀ : Set G) :=
    F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
      conjugate_eq_of_plusFieldGlobal hset hn e ht hKt ι hσ hfix ψ₀ hgen h htM
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨f, hf1, hKc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus (by omega) hf1 hKc e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  set Ψ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G :=
    G₀.subtype.comp ψ₀.symm.toMonoidHom with hΨ
  have hinj : Function.Injective Ψ := G₀.subtype_injective.comp ψ₀.symm.injective
  have hrange : Ψ.range = G₀ := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ₀.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htN)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  have hC := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
  have hCt : (fixedSubgroup β).map Ψ ≤ centralizer ({t} : Set G) := by
    rw [← hC]
    exact inf_le_right
  rcases involution_cases_omegaPlus hn hσ hββ with ⟨s, hs1, hsβ⟩ | ⟨ψ', hψ'⟩ |
      ⟨k, _, _, _, b, c, hirr, hk, N, hNβ, hNperf, ⟨eN⟩⟩
  ·
    apply omegaPlusLinearInvolutionInput_holds hn K F hFK s hs1
    rw [hsβ]
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt hCt
    rwa [Subgroup.card_map_of_injective hinj] at hdvd
  ·
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_fieldEmbed_eq hset.standardSetting hOut hn e htC ht ι hfix
      hinj hβ hψ'
    have hLG : L ≤ G₀ := by
      intro l hl
      have h1 := hΦ (e ⟨l, hl⟩)
      rw [MulEquiv.symm_apply_apply] at h1
      rw [← hrange, ← hΦr]
      exact ⟨_, h1⟩
    have hψ : MulAut.congr (ψ₀.trans ψ') (G₀.normalizerMonoidHom ⟨t, htN⟩) =
        fieldAutT (coordinateQuadPlus n F) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ) := by
      rw [← hψ']
      refine MulEquiv.ext fun x => ?_
      have hx := hβ (ψ'.symm x)
      simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype] at hx
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
        MulAut.mul_apply, MulAut.inv_apply]
      congr 1
      apply ψ₀.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply G₀ htN, hx]
    exact false_of_fieldRow_omegaPlus_of_unique omegaPlusAutNormalFormInput_holds hset hn ht hKt
      hLG htN hσ (ψ₀.trans ψ') hψ huniq
  ·
    have hkK : Nat.card k = Nat.card K :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hk.trans hFK)
    have hNt : N.map Ψ ≤ centralizer ({t} : Set G) := (Subgroup.map_mono hNβ).trans hCt
    have hNperf' : ⁅N.map Ψ, N.map Ψ⁆ = N.map Ψ := by
      rw [← Subgroup.map_commutator, hNperf]
    have hNL : N.map Ψ ≤ L := std_perfect_le hset.standardSetting hOut htC ht hNperf' hNt
    have h1 : Nat.card (N.map Ψ) ≤ Nat.card L := Subgroup.card_le_of_le hNL
    rw [Subgroup.card_map_of_injective hinj, Nat.card_congr eN.toEquiv,
      Nat.card_congr e.toEquiv] at h1
    exact absurd h1 (not_le.2 (card_coordinatePlus_lt_card_coordinateMinus (by omega) hkK hirr))

end Plus

section Minus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_minusFieldGlobal (hset : SeitzSetting G L) {n : ℕ} (hn : 6 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G}
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus n F (by omega)
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)))
    (hgen : ∀ Φ : matrixProjectiveDerived (coordinateQuadMinus n F (by omega)
        ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
        ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)) →* G,
      (∀ x, Φ (incl ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange (by omega)
          (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
          (minusCongr ι.rangeRestrictFieldEquiv (by omega) b c x)) = ((e.symm x : L) : G)) →
        Φ.range ≤ G₀)
    (h : G) (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) :
    CFSG.conjugate G₀ h = G₀ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨f, hf1, hKc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_minus (by omega) hf1 hKc hirr e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * s +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) ≠ 0 := by
    intro s hs h0
    apply hirr₀ ⟨s, (hσk s).2 hs⟩
    apply Subtype.ext
    simpa using h0
  set Ψ := (MulAut.conj h⁻¹).toMonoidHom.comp (G₀.subtype.comp ψ₀.symm.toMonoidHom) with hΨ
  have hinj : Function.Injective Ψ :=
    (MulAut.conj h⁻¹).injective.comp (G₀.subtype_injective.comp ψ₀.symm.injective)
  have hrange : Ψ.range = CFSG.conjugate G₀ h := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₀.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htM)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  by_cases hc : ∃ ψ' : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F _
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F))),
      ψ' * β * ψ'⁻¹ = fieldAutT _ σ (coordinateQuadMinus_fieldMap_of_fixed (by omega)
        ((hσk (ι.rangeRestrictFieldEquiv b)).1 (ι.rangeRestrictFieldEquiv b).2)
        ((hσk (ι.rangeRestrictFieldEquiv c)).1 (ι.rangeRestrictFieldEquiv c).2))
  ·
    obtain ⟨ψ', hψ'⟩ := hc
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_incl_minus_eq hset.standardSetting hOut
      (by omega : 5 ≤ n) hσk (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c) hirr₀
      (e.trans (minusCongr ι.rangeRestrictFieldEquiv (n := n) (by omega) b c)) htC ht hinj hβ
      hψ'
    have hle : CFSG.conjugate G₀ h ≤ G₀ := by
      rw [← hrange, ← hΦr]
      refine hgen Φ (fun x => ?_)
      have h1 := hΦ (e.symm x)
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  ·
    exfalso
    simp only [not_exists] at hc
    apply omegaMinusInvolutionCentralizerInput_holds (n := n) (by omega) (by omega) K F σ hσ hFK
      b c hirr _ _ ((hσk (ι.rangeRestrictFieldEquiv b)).1 (ι.rangeRestrictFieldEquiv b).2)
      ((hσk (ι.rangeRestrictFieldEquiv c)).1 (ι.rangeRestrictFieldEquiv c).2) hirrF β hββ hc
    have hC' := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt (X := Ψ.range ⊓ centralizer ({t} : Set G)) inf_le_right
    rwa [hC', Subgroup.card_map_of_injective hinj] at hdvd

theorem false_of_minusFieldGlobal (hset : SeitzSetting G L) {n : ℕ} (hn : 6 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (htN : t ∈ normalizer (G₀ : Set G))
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (ι b) (ι c)))
    (hgen : ∀ Φ : matrixProjectiveDerived (coordinateQuadMinus n F (by omega) (ι b) (ι c)) →* G,
      (∀ x, Φ (minusFieldEmbed ι (by omega) b c x) = ((e.symm x : L) : G)) → Φ.range ≤ G₀) :
    False := by
  have hb := RingHom.rangeRestrictFieldEquiv_apply_coe ι b
  have hc := RingHom.rangeRestrictFieldEquiv_apply_coe ι c
  set E := minusEqEquiv (F := F) (n := n) (by omega) hb hc with hE
  set ψ₁ := ψ₀.trans E.symm with hψ₁
  have hgen₁ : ∀ Φ : matrixProjectiveDerived (coordinateQuadMinus n F (by omega)
        ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
        ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F)) →* G,
      (∀ x, Φ (incl ι.fieldRange (isExtension_coordinateQuadMinus ι.fieldRange (by omega)
          (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
          (minusCongr ι.rangeRestrictFieldEquiv (by omega) b c x)) = ((e.symm x : L) : G)) →
        Φ.range ≤ G₀ := by
    intro Φ hΦ
    have h1 := hgen (Φ.comp E.symm.toMonoidHom) (fun x => by
      have hx : minusFieldEmbed ι (by omega) b c x = E (incl ι.fieldRange
          (isExtension_coordinateQuadMinus ι.fieldRange (by omega)
            (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c))
          (minusCongr ι.rangeRestrictFieldEquiv (by omega) b c x)) := rfl
      rw [MonoidHom.comp_apply, hx, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hΦ x)
    rwa [MonoidHom.range_comp, MonoidHom.range_eq_top.2 E.symm.surjective,
      ← MonoidHom.range_eq_map] at h1
  have huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) →
      g ∈ normalizer (G₀ : Set G) :=
    F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
      conjugate_eq_of_minusFieldGlobal hset hn hirr e ht hKt ι hσ hfix ψ₁ hgen₁ h htM
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨f, hf1, hKc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_minus (by omega) hf1 hKc hirr e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * s +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) ≠ 0 := by
    intro s hs h0
    apply hirr₀ ⟨s, (hσk s).2 hs⟩
    apply Subtype.ext
    simpa using h0
  have hβ' := (hσk (ι.rangeRestrictFieldEquiv b)).1 (ι.rangeRestrictFieldEquiv b).2
  have hγ' := (hσk (ι.rangeRestrictFieldEquiv c)).1 (ι.rangeRestrictFieldEquiv c).2
  set Ψ := G₀.subtype.comp ψ₁.symm.toMonoidHom with hΨ
  have hinj : Function.Injective Ψ := G₀.subtype_injective.comp ψ₁.symm.injective
  have hrange : Ψ.range = G₀ := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 ψ₁.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htN)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  by_cases hcj : ∃ ψ' : MulAut (matrixProjectiveDerived (coordinateQuadMinus n F _
      ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F)
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F))),
      ψ' * β * ψ'⁻¹ = fieldAutT _ σ (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ' hγ')
  ·
    obtain ⟨ψ', hψ'⟩ := hcj
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_incl_minus_eq hset.standardSetting hOut
      (by omega : 5 ≤ n) hσk (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c) hirr₀
      (e.trans (minusCongr ι.rangeRestrictFieldEquiv (n := n) (by omega) b c)) htC ht hinj hβ
      hψ'
    have hLG : L ≤ G₀ := by
      intro l hl
      rw [← hrange, ← hΦr]
      exact ⟨_, hΦ ⟨l, hl⟩⟩
    have hψ : MulAut.congr (ψ₁.trans ψ') (G₀.normalizerMonoidHom ⟨t, htN⟩) =
        fieldAutT _ σ (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ' hγ') := by
      rw [← hψ']
      refine MulEquiv.ext fun x => ?_
      have hx := hβ (ψ'.symm x)
      simp only [hΨ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype] at hx
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
        MulAut.mul_apply, MulAut.inv_apply]
      congr 1
      apply ψ₁.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply G₀ htN, hx]
    exact omegaMinusFieldRowEndInput_holds G L hset n hn t ht hKt G₀ hLG htN F σ hσ _ _ hβ' hγ'
      hirrF (ψ₁.trans ψ') hψ huniq
  ·
    simp only [not_exists] at hcj
    apply omegaMinusInvolutionCentralizerInput_holds (n := n) (by omega) (by omega) K F σ hσ hFK
      b c hirr _ _ hβ' hγ' hirrF β hββ hcj
    have hC' := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt (X := Ψ.range ⊓ centralizer ({t} : Set G)) inf_le_right
    rwa [hC', Subgroup.card_map_of_injective hinj] at hdvd

end Minus

end CFSG.SeitzReduction.OmegaPilot
