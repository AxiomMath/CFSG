module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotPartnerRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (blockSwapJ)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.Quasithin (perfectCore map_perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open scoped commutatorElement

section Coords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_coords_linearEven_quot (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (ε : spGlobal e ⧸ center (spGlobal e) ≃* projectiveSL (2 * n) F) (H C : GL (Fin (2 * n)) F),
      Nat.card F = 2 ^ f ∧
      (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = UnitaryHigher.blockSwapJ (2 * n) n ∧
      MulAut.congr ε (centerQuotAction (spGlobal e) ⟨t, htN⟩) =
        conjAut (2 * n) F H * (conjAut (2 * n) F C * dualAut (2 * n) F) *
          (conjAut (2 * n) F H)⁻¹ ∧
      LieModel (fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F)) .PSp n 2 f := by
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * n) 2 f := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSL (2 * n) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set ε : spGlobal e ⧸ center (spGlobal e) ≃* projectiveSL (2 * n) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * n) F).symm with hεdef
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  have hθθ : MulAut.congr ε θt * MulAut.congr ε θt = 1 := by
    rw [← map_mul, hθt, centerQuotAction_mul_self ht htN, map_one]
  have hdvd : Nat.card (fixedSubgroup (MulAut.congr ε θt)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) ht htN).trans
      (card_fixedSubgroup_dvd_of_mem hset (by omega) hKc e ht hKt htN)
  obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    (by omega) hF hKc (Or.inl rfl) hθθ hdvd
  have hfixt : LieModel (fixedSubgroup θt) .PSp n 2 f := (hglob.2 htN).2
  have hfix' : LieModel (fixedSubgroup (MulAut.congr ε θt)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θt) hfixt
  rw [he, ← LinearPilot.mulAut_congr_eq_mul] at hfix'
  have hfixC : LieModel (fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv (conjAut (2 * n) F H) _).symm
      hfix'
  rcases hc with h1 | ⟨-, hJ⟩
  · exact absurd hfixC (not_lieModel_PSp_fixedSubgroup_dualAut_one (by omega) hF (by omega)
      (even_two_mul n) h1)
  · exact ⟨F, inferInstance, inferInstance, inferInstance, ε, H, C, hF, hJ, he, hfixC⟩

theorem exists_graph_coords_of_equiv_quot (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven) (htN : t ∈ normalizer (spGlobal e : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (ε : spGlobal e ⧸ center (spGlobal e) ≃* projectiveSL (2 * n) F) :
    ∃ H₁ : GL (Fin (2 * n)) F,
      MulAut.congr ε (centerQuotAction (spGlobal e) ⟨t, htN⟩) =
        conjAut (2 * n) F H₁ * (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F) *
          (conjAut (2 * n) F H₁)⁻¹ := by
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  have hθθ : MulAut.congr ε θt * MulAut.congr ε θt = 1 := by
    rw [← map_mul, hθt, centerQuotAction_mul_self ht htN, map_one]
  have hdvd : Nat.card (fixedSubgroup (MulAut.congr ε θt)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) ht htN).trans
      (card_fixedSubgroup_dvd_of_mem hset (by omega) hKc e ht hKt htN)
  obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    (by omega) hF hKc (Or.inl rfl) hθθ hdvd
  have hfixt : LieModel (fixedSubgroup θt) .PSp n 2 f := (hglob.2 htN).2
  have hfix' : LieModel (fixedSubgroup (MulAut.congr ε θt)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θt) hfixt
  rw [he, ← LinearPilot.mulAut_congr_eq_mul] at hfix'
  have hfixC : LieModel (fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv (conjAut (2 * n) F H) _).symm
      hfix'
  rcases hc with h1 | ⟨-, hJ⟩
  · exact absurd hfixC (not_lieModel_PSp_fixedSubgroup_dualAut_one (by omega) hF (by omega)
      (even_two_mul n) h1)
  · obtain rfl : C = spBlockSwapGL n F := Units.ext (hJ.trans coe_spBlockSwapGL.symm)
    exact ⟨H, he⟩

end Coords

theorem spGraphCosetInnQuotInput_linearEven : SpGraphCosetInnQuotInput .linearEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, hfixC⟩ :=
    exists_coords_linearEven_quot hset hn hKc hf e ht hKt hglob htN
  have hmod := cosetInnConjInput_blockSwapJ (by omega) hF (by omega) rfl hJ hfixC
  apply cosetInnConjInput_of_congr ε
  rw [he, ← LinearPilot.mulAut_congr_eq_mul]
  exact cosetInnConjInput_congr _ hmod

theorem spGraphCosetCardQuotInput_linearEven_of_shape (hsh : SpLinearSecondClassShapeQuotInput) :
    SpGraphCosetCardQuotInput .linearEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN y hy2
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, hfixC⟩ :=
    exists_coords_linearEven_quot hset hn hKc hf e ht hKt hglob htN
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  obtain ⟨g, hg⟩ := proj_surjective (2 * n) F (ε y)
  set A : GL (Fin (2 * n)) F := SpecialLinearGroup.toGL g * H * C *
    GeneralLinearGroup.inverseTranspose H⁻¹ with hA
  have hδ : conjAut (2 * n) F (GeneralLinearGroup.inverseTranspose H⁻¹) * dualAut (2 * n) F =
      dualAut (2 * n) F * (conjAut (2 * n) F H)⁻¹ := by
    rw [← dualAut_mul_conjAut, map_inv]
  have hyA : MulAut.congr ε (MulAut.conj y * θt) = conjAut (2 * n) F A * dualAut (2 * n) F := by
    calc MulAut.congr ε (MulAut.conj y * θt) =
        conjAut (2 * n) F (SpecialLinearGroup.toGL g) * (conjAut (2 * n) F H *
          (conjAut (2 * n) F C * dualAut (2 * n) F) * (conjAut (2 * n) F H)⁻¹) := by
          rw [map_mul, congr_conj_eq_conj_apply, he, ← hg, ← conjAut_toGL]
      _ = conjAut (2 * n) F (SpecialLinearGroup.toGL g) * conjAut (2 * n) F H *
          conjAut (2 * n) F C * (dualAut (2 * n) F * (conjAut (2 * n) F H)⁻¹) := by group
      _ = conjAut (2 * n) F (SpecialLinearGroup.toGL g) * conjAut (2 * n) F H *
          conjAut (2 * n) F C * (conjAut (2 * n) F (GeneralLinearGroup.inverseTranspose H⁻¹) *
            dualAut (2 * n) F) := by rw [hδ]
      _ = conjAut (2 * n) F A * dualAut (2 * n) F := by
          rw [hA, map_mul, map_mul, map_mul]
          group
  have hA2 : (conjAut (2 * n) F A * dualAut (2 * n) F) ^ 2 = 1 := by
    rw [sq, ← hyA, ← map_mul, hy2, map_one]
  obtain ⟨-, ⟨H', C', -, hconj, hC'⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by omega) hF (by omega) A hA2
  rcases hC' with ⟨hC'1, -⟩ | ⟨r', hr', hC'J, -⟩
  · right
    have hC1 : C' = 1 := Units.ext hC'1
    rw [hC1, map_one, one_mul] at hconj
    obtain ⟨x₀, η, p, -, -, -, -, -, -, hcard, -⟩ :=
      hsh G L hset n f K hn hKc hf e t ht hKt hroot hglob htN _ F hF ε H' (hyA.trans hconj)
    exact ⟨p, hcard.le⟩
  · left
    obtain rfl : n = r' := by omega
    have hCC' : C' = C := Units.ext (hC'J.trans hJ.symm)
    subst hCC'
    refine exists_mulAut_mul_eq_of_congr ε
      (γ := conjAut (2 * n) F H' * (conjAut (2 * n) F H)⁻¹) ?_
    rw [hyA, hconj, he]
    group

theorem spLinearSecondClassShapeQuotInput_holds : SpLinearSecondClassShapeQuotInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN α F _ _ hF ε H he
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨H₁, hH₁⟩ := exists_graph_coords_of_equiv_quot hset hn hKc hf e ht hKt hglob htN hF ε
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set p : Fin (m + 1) := 0 with hp
  set zP := spModelPSL (m + 1) F (siegDiag F p 1) with hzP
  set β := conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) * dualAut (2 * (m + 1)) F with hβ
  obtain ⟨H', hconj, -⟩ := exists_normalForm_conj_siegDiag (by omega) hF (by omega) p
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  set σ : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, hF]) with hσ
  set Φ : projectiveSL (2 * (m + 1)) F ≃* spGlobal e ⧸ center (spGlobal e) :=
    ((conjAut (2 * (m + 1)) F H')⁻¹ : MulAut (projectiveSL (2 * (m + 1)) F)).trans
      ((conjAut (2 * (m + 1)) F H).trans ε.symm) with hΦ
  have hΦcongr : ∀ γ : MulAut (projectiveSL (2 * (m + 1)) F), MulAut.congr Φ γ =
      MulAut.congr ε.symm (conjAut (2 * (m + 1)) F H * (conjAut (2 * (m + 1)) F H')⁻¹ * γ *
        (conjAut (2 * (m + 1)) F H' * (conjAut (2 * (m + 1)) F H)⁻¹)) := by
    intro γ
    rw [hΦ, mulAut_congr_trans_apply, mulAut_congr_trans_apply, LinearPilot.mulAut_congr_eq_mul,
      LinearPilot.mulAut_congr_eq_mul, inv_inv]
    simp only [mul_assoc]
  have hαΦ : α = MulAut.congr Φ (MulAut.conj zP * β) := by
    rw [hconj, hΦcongr]
    have h1 : conjAut (2 * (m + 1)) F H * (conjAut (2 * (m + 1)) F H')⁻¹ *
        (conjAut (2 * (m + 1)) F H' * dualAut (2 * (m + 1)) F * (conjAut (2 * (m + 1)) F H')⁻¹) *
          (conjAut (2 * (m + 1)) F H' * (conjAut (2 * (m + 1)) F H)⁻¹) =
        MulAut.congr ε α := by
      rw [he]
      group
    rw [h1, mulAut_congr_symm_congr_apply]
  set ψ : StatedSp (m + 1) K →* spGlobal e ⧸ center (spGlobal e) :=
    Φ.toMonoidHom.comp ((spModelPSL (m + 1) F).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* F) (m + 1))) with hψ
  have hψinj : Function.Injective ψ :=
    Φ.injective.comp ((spModelPSL_injective (by omega)).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1)))
  have hψz : ψ (siegDiag K p 1) = Φ zP := by
    simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, statedSpMap_siegDiag]
    rfl
  set η : MulAut (spGlobal e ⧸ center (spGlobal e)) := MulAut.congr Φ β with hη
  refine spPartnerShapeOn_of_embedding hK4 (by omega : 1 ≤ m) (η := η) ψ hψinj p ?_ ?_ ?_ ?_
  · rw [hψz, hαΦ, map_mul, congr_conj_eq_conj_apply]
  · rw [hψz, hη]
    change Φ (β (Φ.symm (Φ zP))) = Φ zP
    rw [MulEquiv.symm_apply_apply, hβ, hzP,
      conjAut_dualAut_spModelPSL (by omega) coe_spBlockSwapGL]
  · refine exists_mulAut_mul_eq_of_congr ε
      (γ := conjAut (2 * (m + 1)) F H * (conjAut (2 * (m + 1)) F H')⁻¹ *
        (conjAut (2 * (m + 1)) F H₁)⁻¹) ?_
    rw [hH₁, hη, hΦcongr, mulAut_congr_congr_symm_apply]
    group
  · rw [hαΦ, LinearPilot.fixedSubgroup_congr_eq_map,
      fixedSubgroup_conj_siegDiag_mul_graph (by omega) hF (by omega) p, hψ,
      ← Subgroup.map_map, ← Subgroup.map_map, map_statedSpMap_centralizer_siegDiag σ p]

theorem commutator_sup_center_le {M : Type*} [Group M] (S : Subgroup M) :
    ⁅S ⊔ center M, S ⊔ center M⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨b, hb, d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hc' := mem_center_iff.mp hc
  have hd' := mem_center_iff.mp hd
  have key : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
        = a * c * b * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by
        have e1 : c * b = b * c := (hc' b).symm
        have e2 : d * c⁻¹ = c⁻¹ * d := (mem_center_iff.mp (inv_mem hc)) d
        have e4 : d * a⁻¹ = a⁻¹ * d := (hd' a⁻¹).symm
        have e5 : d * d⁻¹ = 1 := mul_inv_cancel d
        calc a * c * b * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹
            = a * b * (c * (d * c⁻¹)) * a⁻¹ * d⁻¹ * b⁻¹ := by rw [mul_assoc a c b, e1]; group
          _ = a * b * d * a⁻¹ * d⁻¹ * b⁻¹ := by rw [e2]; group
          _ = a * b * a⁻¹ * (d * d⁻¹) * b⁻¹ := by rw [mul_assoc (a * b) d a⁻¹, e4]; group
          _ = a * b * a⁻¹ * b⁻¹ := by rw [e5, mul_one]
  rw [key, commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem spLongPieceQuotInput_linearEven : SpLongPieceQuotInput .linearEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, -⟩ :=
    exists_coords_linearEven_quot hset hn hKc hf e ht hKt hglob htN
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hF4 : 4 ≤ Nat.card F := (LinearPilot.four_le_card_iff_two_le hF).2 hf
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  have hLG : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  set π : spGlobal e →* spGlobal e ⧸ center (spGlobal e) :=
    QuotientGroup.mk' (center (spGlobal e)) with hπ
  set L₀ : Subgroup (spGlobal e) := L.subgroupOf (spGlobal e) with hL₀
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  set σ : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, hF]) with hσ
  set Φ : projectiveSL (2 * n) F ≃* spGlobal e ⧸ center (spGlobal e) :=
    (conjAut (2 * n) F H).trans ε.symm with hΦ
  have hfix : fixedSubgroup θt = (spModelPSL n F).range.map Φ.toMonoidHom := by
    rw [fixedSubgroup_eq_map_of_congr ε he, ← range_spModelPSL (by omega) hF (by omega) hJ,
      Subgroup.map_map]
    rfl
  have hπLinj : Function.Injective (π.comp (Subgroup.inclusion hLG)) :=
    injective_mk_comp_inclusion hLG ht hKt hZ
  have hrangeL : (π.comp (Subgroup.inclusion hLG)).range = L₀.map π := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hL₀fix : L₀ ≤ fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨t, htN⟩) := by
    intro y hy
    change (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ y = y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have h1 : (y : G) * t = t * y := mem_centralizer_iff.1 htC y (mem_subgroupOf.1 hy)
    rw [← h1, mul_inv_cancel_right]
  have hLbfix : L₀.map π = fixedSubgroup θt := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.map_mono hL₀fix).trans
      (map_mk_fixedSubgroup_le _ htN)) ?_
    rw [← hrangeL, ← Nat.card_congr (MonoidHom.ofInjective hπLinj).toEquiv, hfix,
      Subgroup.card_map_of_injective Φ.injective, Nat.card_congr e.toEquiv,
      card_statedSp_eq_of_ringEquiv σ,
      ← Nat.card_congr (MonoidHom.ofInjective (spModelPSL_injective (n := n) (F := F)
        (by omega))).toEquiv]
  set ψ : StatedSp n K →* spGlobal e ⧸ center (spGlobal e) :=
    Φ.toMonoidHom.comp ((spModelPSL n F).comp (statedSpMap (σ : K →+* F) n)) with hψ
  have hψinj : Function.Injective ψ :=
    Φ.injective.comp ((spModelPSL_injective (by omega)).comp (statedSpMap_injective _ n))
  have hψrange : ψ.range = L₀.map π := by
    rw [hLbfix, hfix, hψ, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (statedSpMap_surjective σ), ← MonoidHom.range_eq_map]
  set ψ' : StatedSp n K ≃* (L₀.map π) :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange) with hψ'
  set ιL : L ≃* (L₀.map π) :=
    (MonoidHom.ofInjective hπLinj).trans (MulEquiv.subgroupCongr hrangeL) with hιL
  set φ : StatedSp n K ≃* L := ψ'.trans ιL.symm with hφ
  have hφψ : ∀ x, π (Subgroup.inclusion hLG (φ x)) = ψ x := by
    intro x
    have h1 : ιL (φ x) = ψ' x := ιL.apply_symm_apply (ψ' x)
    exact congrArg Subtype.val h1
  obtain ⟨s, τ, hsτ⟩ := F4Pilot.exists_eq_conj_mul_fieldSp (by omega : 3 ≤ n) (φ.trans e)
  set u : StatedSp n K := (fieldSp n K τ).symm s⁻¹ with hu
  have hτu : fieldSp n K τ u = s⁻¹ := MulEquiv.apply_symm_apply _ _
  set last : Fin n := ⟨n - 1, by omega⟩ with hlastdef
  have hlast : last.val + 1 = n := by
    rw [hlastdef]
    simp only
    omega
  set T := leviTorusSp K ({last} : Finset (Fin n)) with hT
  have hX : ∀ y ∈ T, ψ (u * y * u⁻¹) =
      π (Subgroup.inclusion hLG (e.symm (fieldSp n K τ y))) := by
    intro y hy
    have h1 : e (φ (u * y * u⁻¹)) = fieldSp n K τ y := by
      have h2 := hsτ (u * y * u⁻¹)
      rw [MulEquiv.trans_apply] at h2
      rw [h2, map_mul, map_mul, map_inv, hτu]
      group
    rw [← hφψ, ← h1, MulEquiv.symm_apply_apply]
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one hK4
  set M := pieceCore e ({last} : Finset (Fin n)) with hMdef
  have hMG : M ≤ spGlobal e := le_iSup (fun j : Fin n => pieceCore e ({j} : Finset (Fin n))) last
  set M₀ : Subgroup (spGlobal e) := M.subgroupOf (spGlobal e) with hM₀
  have hM₀perf : ⁅M₀, M₀⁆ = M₀ :=
    commutator_subgroupOf_eq hMG (F4Pilot.commutator_centralizerPerfectCore _)
  have hMbperf : ⁅M₀.map π, M₀.map π⁆ = M₀.map π := by
    rw [← Subgroup.map_commutator, hM₀perf]
  have hMbc : M₀.map π ≤ centralizer
      (((T.map (MulAut.conj u).toMonoidHom).map ψ : Subgroup _) : Set _) := by
    rintro _ ⟨m, hm, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hmM : ((m : spGlobal e) : G) ∈ M := hm
    have hc : ((m : spGlobal e) : G) * ((e.symm (fieldSp n K τ y) : L) : G) =
        ((e.symm (fieldSp n K τ y) : L) : G) * ((m : spGlobal e) : G) :=
      (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ hmM) _
        ((mem_modelToG e).2 ⟨_, fieldSp_mem_leviTorusSp τ hy, rfl⟩)).symm
    have hc' : m * Subgroup.inclusion hLG (e.symm (fieldSp n K τ y)) =
        Subgroup.inclusion hLG (e.symm (fieldSp n K τ y)) * m := Subtype.ext hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hX y hy, ← map_mul, ← map_mul, hc']
  have hMbL : M₀.map π ≤ L₀.map π := by
    have h1 := CFSG.Quasithin.le_perfectCore_of_perfect hMbc hMbperf
    have hY : (T.map (MulAut.conj u).toMonoidHom).map ψ =
        ((T.map (MulAut.conj u).toMonoidHom).map
          ((spModelPSL n F).comp (statedSpMap (σ : K →+* F) n))).map Φ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rw [hY, centralizer_map_mulEquiv_toMonoidHom Φ, ← map_perfectCore] at h1
    have h2 := perfectCore_centralizer_conj_torus_le hF4 (by omega) hlast σ hκ₀ u
    have h3 := Subgroup.map_mono (f := Φ.toMonoidHom) h2
    rw [← hfix, ← hLbfix] at h3
    exact h1.trans h3
  have hM₀LZ : M₀ ≤ L₀ ⊔ center (spGlobal e) := by
    have h1 := Subgroup.map_le_iff_le_comap.1 hMbL
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hM₀L : M₀ ≤ L₀ := by
    rw [← hM₀perf]
    exact (Subgroup.commutator_mono hM₀LZ hM₀LZ).trans (commutator_sup_center_le L₀)
  intro x hx
  have hxL : x ∈ L := hM₀L (show (⟨x, hMG hx⟩ : spGlobal e) ∈ M₀ from hx)
  exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hxL)

theorem spLinearEvenSecondClassQuotInput_holds : SpLinearEvenSecondClassQuotInput :=
  spLinearEvenSecondClassQuot_of_partner spLinearSecondClassShapeQuotInput_holds
    spGraphCosetInnQuotInput_linearEven
    (spGraphCosetCardQuotInput_linearEven_of_shape spLinearSecondClassShapeQuotInput_holds)
    spLongPieceQuotInput_linearEven

section Rows

theorem false_of_spLinearEvenRow_of_kindCover (hc : SpKindCoverInput .linearEven) :
    SpLinearEvenRowInput :=
  false_of_spLinearEvenRow_of_cover hc spLinearEvenSecondClassQuotInput_holds

end Rows

end CFSG.SeitzReduction.SymplecticPilot
