module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.OuterFixedBasic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThree
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.ThreeD4
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar (fixSub)

theorem exists_fixed_E9_of_autFix_pair {X : Type} [Group X] [Finite X] {α : MulAut X}
    (h : ∃ u v : CFSG.RankThree.PartTwo.Sec4.autFix α, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧
      u * v = v * u ∧ v ∉ zpowers u) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e := by
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := h
  obtain ⟨hE, hE9⟩ := isElemAbelian_card_sup_zpowers_of_pair hu1 hu3 hv3 huv hvu
  obtain ⟨hE', hE9'⟩ := isElemAbelian_card_map_of_E9 (CFSG.RankThree.PartTwo.Sec4.autFix α).subtype
    (Subgroup.subtype_injective _) hE hE9
  refine ⟨_, hE', hE9', ?_⟩
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem five_le_of_prime_ne_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  omega

section Fixed


theorem exists_E9_fixed_conj_fieldActor {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    [Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    (hpair : ∃ u v : fixSub (fieldActor (t := TwistTag.D4) σ σ), u ≠ 1 ∧ u ^ 3 = 1 ∧
      v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ zpowers u)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : fieldActor (t := TwistTag.D4) σ σ s = s) (hs3 : s ^ 3 = 1) :
    ∃ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ e ∈ E, (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) e = e := by
  set δ₀ := fieldActor (t := TwistTag.D4) σ σ with hδ₀
  by_cases hs1 : s = 1
  · subst hs1
    obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := hpair
    obtain ⟨hE, hE9⟩ := isElemAbelian_card_sup_zpowers_of_pair hu1 hu3 hv3 huv hvu
    obtain ⟨hE', hE9'⟩ :=
      isElemAbelian_card_map_of_E9 (fixSub δ₀).subtype (Subgroup.subtype_injective _) hE hE9
    refine ⟨_, hE', hE9', ?_⟩
    rintro _ ⟨y, -, rfl⟩
    rw [map_one, one_mul]
    exact y.2
  · obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := hpair
    have hE9C := CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.e9Closed_of_commuting hu1 hu3 hv3
      huv hvu
    obtain ⟨z, hz3, hsz, hzs⟩ := hE9C ⟨s, hs⟩ (Subtype.ext (by rw [Subgroup.coe_pow]; exact hs3))
      (fun h => hs1 (congrArg Subtype.val h))
    have hz3' : (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ 3 = 1 := by
      have := congrArg Subtype.val hz3
      rwa [Subgroup.coe_pow] at this
    have hsz' : s * (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = z * s :=
      congrArg Subtype.val hsz
    have hzs' : (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∉ zpowers s := by
      intro h
      apply hzs
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    have hfs : (MulAut.conj s * δ₀) s = s := by
      rw [MulAut.mul_apply, hs, MulAut.conj_apply, mul_inv_cancel_right]
    have hfz : (MulAut.conj s * δ₀) z = z := by
      rw [MulAut.mul_apply, show δ₀ z = z from z.2, MulAut.conj_apply, hsz',
        mul_inv_cancel_right]
    obtain ⟨E, hEH, hE, hE9⟩ := exists_E9_le_of_pair
      (H := CFSG.RankThree.PartOne.CTP.fixedSubgroup (MulAut.conj s * δ₀)) hfs hfz hs1 hs3 hz3'
      hsz' hzs'
    exact ⟨E, hE, hE9, fun e he => hEH he⟩

end Fixed

section Two


theorem outerFixesE9_triality_two {n : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    OuterFixesE9 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hK2 := CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.ringChar_eq_two_of_card hK
  intro α hα3 hαo
  apply exists_fixed_E9_of_autFix_pair
  rcases CFSG.RankThree.PartTwo.Sec8.kF82D4OuterClasses_of_lang
      CFSG.RankThree.PartTwo.Sec8.kF82D4LangCoset_holds n K σ hK hσ α hα3 hαo with
    hstd | ⟨γ, y, hγ, hγy, hy, hαγ⟩
  · exact CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.exists_pair_autFix_of_isStdGraphFieldConj
      hK2 σ hstd
  · rw [hαγ]
    exact CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.exists_pair_autFix_mul_conj hK2 σ hγ hγy hy

end Two

section Odd


theorem outerFixesE9_triality_odd {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    OuterFixesE9 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hδ3 := CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_fieldActor_pow_three K hK σ hσ
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 hp hf K hK
  have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
  have hord3 : orderOf σ = 3 := hσσ' ▸ hord
  have hK' : Nat.card K = p ^ (f * 3) := by rw [hK, ← pow_mul]
  obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hp (by omega) hK' σ
  rw [hord3, Nat.mul_div_cancel _ (by norm_num)] at hcard
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, hcard]
    have : 3 ≤ p ^ f := le_trans (by omega) (Nat.le_self_pow (by omega) p)
    exact_mod_cast this
  have hpair : ∃ u v : fixSub (fieldActor (t := TwistTag.D4) σ σ), u ≠ 1 ∧ u ^ 3 = 1 ∧
      v ^ 3 = 1 ∧ u * v = v * u ∧ v ∉ zpowers u := by
    let ι := (Subgroup.equivMapOfInjective (fixSub (fieldActor (t := TwistTag.D4) σ σ))
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
        (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Timmesfeld.CrossChar.map_fixSub_fieldActor_self
        σ hσ3))
    let φ := ι.trans (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk3)
    exact CFSG.RankThree.PartTwo.Sec8.Item8KFactsProof.exists_pair_of_injective
      φ.symm.toMonoidHom φ.symm.injective
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.g2_exists_e9 (fixSubfield σ))
  have key : ∀ (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      β = MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ → β ^ 3 = 1 →
      ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        fieldActor (t := TwistTag.D4) σ σ s = s ∧ s ^ 3 = 1 ∧
        β = (MulAut.conj y)⁻¹ * (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) *
          MulAut.conj y := by
    intro β g hβ hβ3
    have hnorm := CFSG.GH74.GLS.Stage2.OddAut.normSeq_eq_one_of_pow_eq_one hZ hδ3 (hβ ▸ hβ3)
    obtain ⟨y, s, hs, hs3, hys⟩ :=
      CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.threeD4FixedNF_holds
        p f hp hp5 hf K hK σ hσ g hnorm
    refine ⟨y, s, hs, hs3, ?_⟩
    rw [hβ, ← hys]
    group
  refine outerFixesE9_of_descent fun α hα3 hαo => ?_
  obtain ⟨g, hαg | hαg⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_eq_conj_mul_fieldActor_self_of_pow_three hp hf
      hK σ hσ α hα3 hαo
  · obtain ⟨y, s, hs, hs3, hβ⟩ := key α g hαg hα3
    exact ⟨(MulAut.conj y)⁻¹, _, by rw [hβ, inv_inv],
      exists_E9_fixed_conj_fieldActor σ hpair hs hs3⟩
  · have hα3' : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα3, inv_one]
    obtain ⟨y, s, hs, hs3, hβ⟩ := key α⁻¹ g hαg hα3'
    obtain ⟨E, hE, hE9, hEfix⟩ := exists_E9_fixed_conj_fieldActor σ hpair hs hs3
    refine ⟨(MulAut.conj y)⁻¹, (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)⁻¹, ?_, E, hE,
      hE9, fun e he => ?_⟩
    · rw [← inv_inv α, hβ]
      group
    · rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact (hEfix e he).symm

end Odd

section Index


theorem outerFixedAt_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hp3 : q.p ≠ 3) : OuterFixedAt ⟨.trialityD4 q, hv⟩ := by
  refine outerFixedAt_of_model fun G _ _ e => ?_
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨φ⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  refine ⟨_, _, ?_, ⟨e.trans φ⟩⟩
  by_cases hp2 : q.p = 2
  · have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hp2]
    have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ, hp2]
    exact outerFixesE9_triality_two σ hK' hσ'
  · exact outerFixesE9_triality_odd q.prime_p (five_le_of_prime_ne_two_three q.prime_p hp2 hp3)
      q.exponent_pos hK σ hσ

end Index

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
