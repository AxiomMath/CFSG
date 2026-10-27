module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightGraphRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLinearRow

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open LinearFlag CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

theorem spTwoLinearEvenSecondClass_of_three_le :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .linearEven) → NsRowGlobal e t .linearEven →
        ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
          ¬ IsCharacteristicP 2
            (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)) := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt _ hglob g hg hchar
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨F, _, _, _, ε, H, hF, he⟩ :=
    exists_coords_nsLinearEven hset hK hn e ht hKt hglob htN
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  set θw := (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθw
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hαw : MulAut.congr ε θw * MulAut.congr ε θw = 1 := by
    rw [← map_mul, hθw, normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg, map_one]
  have hdw : Nat.card (fixedSubgroup (MulAut.congr ε θw)) ∣
      2 * (Nat.card (StatedSp (n + 1) K) * 1) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg
  obtain ⟨H₂, C₂, hc₂, he₂⟩ := exists_graph_normal_form_of_card_dvd (K := K)
    (by omega : 3 ≤ n + 1) le_rfl hF' hKc (Or.inl rfl) hαw hdw
  rcases hc₂ with h1 | ⟨-, hJ₂⟩
  ·
    have hC1 : C₂ = 1 := Units.ext h1
    rw [hC1, map_one, one_mul] at he₂
    have hsh := nsPartnerShape_of_iType hset hK hn e ht hKt hglob htN hF ε H₂ he₂
    have hLS : L ≤ nsGlobal e := le_nsGlobal hK hn e
    have htZ : t ∉ centralizer (nsGlobal e : Set G) := by
      intro htZ
      apply ((hglob.2 htN).1)
      refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
      rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
    have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
    exact false_of_nsPartnerShape hset hK hn e ht hKt htN hodd
      (cosetInnConjInput_nsLinearEven hset hK hn e ht hKt hglob htN)
      (nsCosetCardInput_nsLinearEven hset hK hn e ht hKt hglob htN) hg hsh
  ·
    rw [← LinearPilot.mulAut_congr_eq_mul] at he₂
    have Φ := (fixedSubgroupCongrEquiv ε θw).trans ((MulEquiv.subgroupCongr
      (congrArg fixedSubgroup he₂)).trans (fixedSubgroupCongrEquiv (conjAut _ F H₂) _).symm)
    exact not_isCharacteristicP_fixedSubgroup_blockSwapJ_two hF (by omega) hJ₂
      (isCharacteristicP_of_mulEquiv Φ hchar)

theorem spTwoLinearEvenSecondClassEightInput_holds : SpTwoLinearEvenSecondClassEightInput :=
  fun G _ _ L hset K _ _ _ hK e t ht hKt hroot hglob g hg =>
    spTwoLinearEvenSecondClass_of_three_le G L hset 3 K hK le_rfl e t ht hKt hroot hglob g hg

theorem spTwoUnitaryEvenSecondClassQuot_of_three_le :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .unitaryEven) → NsRowGlobalQuot e t .unitaryEven →
        ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
          ¬ IsCharacteristicP 2
            (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩)) := by
  intro G _ _ L hset n K _ _ _ hK hm e t ht hKt _ hglob g hg hchar
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  have hperf : Group.IsPerfect (nsGlobal e) := hglob.1.1.1
  have hZ : Odd (Nat.card (center (nsGlobal e))) := hglob.1.2.1
  have hty' : LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU (2 * (n + 1)) 2 1 := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSU (2 * (n + 1)) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have hq : ¬(2 * (n + 1) = 3 ∧ 2 ^ 1 = 2) := by omega
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * (n + 1))) K') :
      Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K'), orderOf y = 2 →
      1 * (n + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * (n + 1))) K') :
          Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K'))))).factorization 2 := by
    intro y hy
    set φ := CFSG.ComponentClassification.OutcomeLocal.primeFormOneEquiv h (2 * (n + 1))
    have h1 := unitaryEvenInnerTwoPart_holds 1 K' h (n + 1) (by omega) (φ y)
      (by rw [MulEquiv.orderOf_eq, hy])
    rw [card_centralizer_map_mulEquiv] at h1
    have h0 : (1 : ℕ).factorization 2 = 0 := by simp
    rw [h0]
    simp only [one_mul] at h1 ⊢
    omega
  have hy0 := exists_orderOf_eq_two_quot_nsGlobal hK hm e ht hKt hZ ψ
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  have hαw : MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
      MulAut.congr ψ (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
    rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
  have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ
      (centerQuotAction (nsGlobal e) ⟨g⁻¹ * t * g, hg⟩)))).factorization 2 ≤
        1 * (n + 1) ^ 2 + 1 + (1 : ℕ).factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
      (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
  obtain ⟨C₀, hC₀, hc, θ, he⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
  rcases hc with h1 | ⟨r, hr, hJ⟩
  ·
    have hC1 : C₀ = 1 := Units.ext h1
    subst hC1
    rw [LinearPilot.mulAut_congr_eq_mul] at he
    have hsh := nsPartnerShapeOn_of_iType_quot hK hm e ht hglob htN h ψ θ he
    have htZ : t ∉ centralizer (nsGlobal e : Set G) := by
      intro htZ
      apply (hglob.2 htN).1
      refine ⟨1, MulEquiv.ext fun q => ?_⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center (nsGlobal e)) q
      rw [map_one, MulAut.one_apply, centerQuotAction_apply_mk]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← mem_centralizer_iff.1 htZ y y.2,
        mul_inv_cancel_right]
    have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
    exact false_of_nsPartnerShapeQuot hset hK hm e ht hKt hLS hZ htN hodd
      (fun h' hh γ hγ =>
        mem_normalizer_nsGlobal_of_conj_centerQuotAction hset hK hm e ht hKt hperf hZ htN hh γ hγ)
      (fun k P hP hPc => (F4Pilot.le_centralizerPerfectCore hP hPc).trans
        (centralizerPerfectCore_nsTorusSp_le_nsGlobal e k))
      (cosetInnConjInput_nsUnitaryQuot hm e ht hglob htN)
      (spCosetCardOn_nsUnitaryQuot hK hm e ht hglob htN) hg hsh
  ·
    obtain rfl : r = n + 1 := by omega
    have : CharP h.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
    have : Finite h.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
    have hF2 : Nat.card h.fixedField = 2 := by rw [h.card_fixedField, pow_one]
    have Φ := (fixedSubgroupCongrEquiv ψ _).trans ((MulEquiv.subgroupCongr
      (congrArg fixedSubgroup he)).trans (fixedSubgroupCongrEquiv θ _).symm)
    have hrange := range_uModelP (by omega) hq hC₀ hJ
    set E := (MonoidHom.ofInjective (uModelP_injective (by omega) hJ)).trans
      (MulEquiv.subgroupCongr hrange) with hE
    have : IsSimpleGroup (StatedSp (n + 1) h.fixedField) :=
      isSimpleGroup_statedSp_two hF2 (by omega)
    have : IsSimpleGroup (fixedSubgroup (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h))) :=
      E.symm.isSimpleGroup_congr.2 this
    have hy : orderOf (E (nsElt (K := h.fixedField) (⟨0, by omega⟩ : Fin (n + 1)))) = 3 := by
      rw [MulEquiv.orderOf_eq, orderOf_nsElt]
    exact not_isCharacteristicP_two_of_isSimpleGroup hy (isCharacteristicP_of_mulEquiv Φ hchar)

theorem spTwoUnitaryEvenSecondClassQuotEightInput_holds :
    SpTwoUnitaryEvenSecondClassQuotEightInput :=
  fun G _ _ L hset K _ _ _ hK e t ht hKt hroot hglob g hg =>
    spTwoUnitaryEvenSecondClassQuot_of_three_le G L hset 3 K hK le_rfl e t ht hKt hroot hglob g hg

end CFSG.SeitzReduction.SymplecticPilot
