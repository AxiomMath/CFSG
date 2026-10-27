module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldCTGenMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT incl)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus
  coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem false_of_minusFieldRowEnd_of_five_le {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n) {t : G} (ht : orderOf t = 2)
    (G₀ : Subgroup G) (htN : t ∈ normalizer (G₀ : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F) (hσ : orderOf σ = 2)
    {β γ : F} (hβ : σ β = β) (hγ : σ γ = γ) (hirr : ∀ s : F, σ s = s → s ^ 2 + β * s + γ ≠ 0)
    (ψ : G₀ ≃* matrixProjectiveDerived (coordinateQuadMinus n F (by omega) β γ))
    (hψ : MulAut.congr ψ (G₀.normalizerMonoidHom ⟨t, htN⟩) =
        fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
          (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  have : IsSimpleGroup G := hset.1
  obtain ⟨E, hE2, hEInn, hEσ⟩ := omegaMinusGraphCoordinateInput_holds F n hn β γ σ hσ hβ hγ hirr
  have : E.Normal := Subgroup.normal_of_index_eq_two hE2
  have : E.FiniteIndex := ⟨by rw [hE2]; norm_num⟩
  have hρt : F4Pilot.normalizerMulAut ψ ⟨t, htN⟩ =
      fieldAutT (coordinateQuadMinus n F (by omega) β γ) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hβ hγ) := hψ
  have hQ : ¬ 4 ∣ Nat.card (MulAut (matrixProjectiveDerived
      (coordinateQuadMinus n F _ β γ)) ⧸ E) := by
    change ¬ 4 ∣ E.index
    rw [hE2]
    decide
  refine EPilot.false_of_simple_of_mulAut_hom ψ htN ht huniq (QuotientGroup.mk' E) hQ
    (fun x => (QuotientGroup.eq_one_iff _).2 (hEInn x)) ?_
  rw [hρt]
  exact fun h => hEσ ((QuotientGroup.eq_one_iff _).1 h)

section MinusFive

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_minusFieldGlobal_of_five_le (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n)
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

theorem false_of_minusFieldGlobal_of_five_le (hset : SeitzSetting G L) {n : ℕ} (hn : 5 ≤ n)
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
      conjugate_eq_of_minusFieldGlobal_of_five_le hset hn hirr e ht hKt ι hσ hfix ψ₁ hgen₁ h htM
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
    exact false_of_minusFieldRowEnd_of_five_le hset hn ht G₀ htN σ hσ hβ' hγ'
      hirrF (ψ₁.trans ψ') hψ huniq
  ·
    simp only [not_exists] at hcj
    apply omegaMinusInvolutionCentralizerInput_holds (n := n) (by omega) (by omega) K F σ hσ hFK
      b c hirr _ _ hβ' hγ' hirrF β hββ hcj
    have hC' := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt (X := Ψ.range ⊓ centralizer ({t} : Set G)) inf_le_right
    rwa [hC', Subgroup.card_map_of_injective hinj] at hdvd

end MinusFive

section MinusGenFive

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem iSup_perfectCore_centralizer_anisoTorus_eq_top_of_three_le {r f : ℕ} (hr : 3 ≤ r)
    {c : K} (hirr : ∀ s : K, s ^ 2 + 1 * s + c ≠ 0) (ι : K →+* F) {α : F}
    (hα : α ^ 2 + ι 1 * α + ι c = 0) (hαα : α ≠ -ι 1 - α) (hFf : Nat.card F = 2 ^ f)
    (hF : 4 ≤ Nat.card F) :
    ⨆ y : matrixProjectiveDerived (coordinateQuadMinus (r + 1) K (by omega) 1 c),
      perfectCore (centralizer ((((anisoTorus (K := K) (by omega) 1 c).map
        (MulAut.conj y).toMonoidHom).map (minusFieldEmbed ι (by omega) 1 c) :
          Subgroup (matrixProjectiveDerived
            (coordinateQuadMinus (r + 1) F (by omega) (ι 1) (ι c)))) :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 1) F (by omega) (ι 1) (ι c))))) =
      ⊤ := by
  have hn : 1 ≤ r + 1 := by omega
  refine iSup_perfectCore_centralizer_eq_top_of_mulEquiv (by omega) hFf hF
    (minusPlusProjEquiv hn hα hαα) _ fun j => ?_
  by_cases hj : j.val + 2 ≤ r
  · refine ⟨1, rationalNode_le_centralizer_of_le_suppBar _ j
      (P := Finset.univ.filter fun x : Fin (r + 1) => x.val = r) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      omega
    · rintro _ ⟨x, hx, rfl⟩
      rw [map_conj_one_eq] at hx
      exact minusPlusProjEquiv_mem_suppBar hn hα hαα (minusPlusLin_hM_aniso hn hαα)
        (map_minusFieldEmbed_suppBar_le ι hn 1 c _
          (map_mono (anisoTorus_le_suppBar hn one_ne_zero hirr) hx))
  · refine ⟨projHom _ ⟨minusSwapLin hn (by omega) c,
        minusSwapLin_mem_orthDerived hn hr hirr⟩,
      rationalNode_le_centralizer_of_le_suppBar _ j
        (P := Finset.univ.filter fun x : Fin (r + 1) => x.val < 2) ?_ ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      rw [mem_plusNodeSet] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      omega
    · rintro _ ⟨x, hx, rfl⟩
      exact minusPlusProjEquiv_mem_suppBar hn hα hαα (minusPlusLin_hM_low hn _ _)
        (map_minusFieldEmbed_suppBar_le ι hn 1 c _
          (map_mono (map_conj_anisoTorus_le_suppBar hn hr hirr) hx))

end MinusGenFive


section MinusTen

@[expose] def OmegaMinusTwoTenFieldGlobalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal →
        ∀ (htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))
          (Kc : Subgroup (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) :
              Set G) ⧸ oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))),
          IsComponent Kc →
          OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) Kc 4 1 →
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))
                ⟨t, htX⟩)).toMonoidHom = Kc →
          LieModel Kc .POmegaPlus 4 2 2 →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 4 ∧
            Nonempty (anisoNeighbourJoin L (modelToG e (anisoTorus (K := K) (by norm_num) b c)) ≃*
              matrixProjectiveDerived (coordinateQuadPlus 5 F))


theorem omegaMinusTwoTenFieldLieInput_of_global (hglob : OmegaMinusTwoTenFieldGlobalInput) :
    OmegaMinusTwoTenFieldLieInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F', _, _, _, hF'4, ⟨ψ'⟩⟩ :=
    hglob G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF4 : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2, pow_one]) hσ
      hfix]
    norm_num
  obtain ⟨χ⟩ := nonempty_plusModel_mulEquiv_of_card_eq (F := F) (F' := F')
    (by rw [hF'4, hF4]) (n := 5) (by norm_num)
  have hβ : σ (ι b) = ι b := (hfix (ι b)).2 ⟨b, rfl⟩
  have hγ : σ (ι c) = ι c := (hfix (ι c)).2 ⟨c, rfl⟩
  have hirrF : ∀ s : F, σ s = s → s ^ 2 + ι b * s + ι c ≠ 0 := by
    intro s hs h0
    obtain ⟨k, rfl⟩ := (hfix s).1 hs
    apply hirr k
    apply ι.injective
    rw [map_add, map_add, map_mul, map_pow, map_zero]
    exact h0
  obtain ⟨α, hα, -, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirrF
  have hαα : α ≠ -ι b - α := root_ne_other_of_ne_zero hβ0
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hXL := UnitaryPilot.modelToG_le e (anisoTorus (K := K) (by norm_num) b c)
  refine false_of_minusFieldGlobal_of_five_le hset (le_refl 5) hirr e ht hKt ι hσ hfix
    (mem_normalizer_anisoNeighbourJoin hXL htC)
    ((ψ'.trans χ).trans (minusPlusProjEquiv (r := 4) (by norm_num) hα hαα).symm)
    (fun Φ hΦ => ?_)
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  obtain ⟨α', hα'⟩ := exists_root_of_card_eq_sq ι (by rw [hF4, hK2]; norm_num) hirr
  have hb0 : ι 1 ≠ 0 := by rw [map_one]; exact one_ne_zero
  exact range_le_anisoNeighbourJoin e (minusFieldEmbed ι (by norm_num) 1 c) _
    (iSup_perfectCore_centralizer_anisoTorus_eq_top_of_three_le (r := 4) (f := 2) (by norm_num)
      hirr ι hα' (root_ne_other_of_ne_zero hb0) (by rw [hF4]; norm_num) (by omega)) hΦ

end MinusTen


end CFSG.SeitzReduction.OmegaPilot
