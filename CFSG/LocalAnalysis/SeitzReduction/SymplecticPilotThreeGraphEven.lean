module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotLinearEven

public section

namespace CFSG.SeitzReduction.SymplecticPilot

section Linear

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

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_coords_linearEven_quot_of_three_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
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

theorem exists_graph_coords_of_equiv_quot_of_three_le (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤
    n)
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

theorem cosetInnConjInput_linearEven_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    CosetInnConjInput (centerQuotAction (spGlobal e) ⟨t, htN⟩) := by
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, hfixC⟩ :=
    exists_coords_linearEven_quot_of_three_le hset hn hKc hf e ht hKt hglob htN
  have hmod := cosetInnConjInput_blockSwapJ (by omega) hF (by omega) rfl hJ hfixC
  apply cosetInnConjInput_of_congr ε
  rw [he, ← LinearPilot.mulAut_congr_eq_mul]
  exact cosetInnConjInput_congr _ hmod

theorem spPartnerShapeOn_linearEven_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven)
    (htN : t ∈ normalizer (spGlobal e : Set G))
    (α : MulAut (spGlobal e ⧸ center (spGlobal e))) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f)
    (ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F)
    (H : GL (Fin (2 * n)) F)
    (he : MulAut.congr ε α = LinearFlag.conjAut (2 * n) F H * LinearFlag.dualAut (2 * n) F *
      (LinearFlag.conjAut (2 * n) F H)⁻¹) :
    SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) α := by
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨H₁, hH₁⟩ := exists_graph_coords_of_equiv_quot_of_three_le hset hn hKc hf e ht hKt hglob
      htN hF ε
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

theorem spCosetCardOn_linearEven_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    SpCosetCardOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) := by
  intro y hy2
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, hfixC⟩ :=
    exists_coords_linearEven_quot_of_three_le hset hn hKc hf e ht hKt hglob htN
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
      spPartnerShapeOn_linearEven_of_three_le hset hn hKc hf e ht hKt hglob htN _ hF ε H'
        (hyA.trans hconj)
    exact ⟨p, hcard.le⟩
  · left
    obtain rfl : n = r' := by omega
    have hCC' : C' = C := Units.ext (hC'J.trans hJ.symm)
    subst hCC'
    refine exists_mulAut_mul_eq_of_congr ε
      (γ := conjAut (2 * n) F H' * (conjAut (2 * n) F H)⁻¹) ?_
    rw [hyA, hconj, he]
    group

theorem pieceCore_last_le_centralizer_linearEven (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven) :
    pieceCore e ({⟨n - 1, by omega⟩} : Finset (Fin n)) ≤ centralizer ({t} : Set G) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨F, _, _, _, ε, H, C, hF, hJ, he, -⟩ :=
    exists_coords_linearEven_quot_of_three_le hset hn hKc hf e ht hKt hglob htN
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

end Linear

section Unitary

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Quasithin (perfectCore map_perfectCore)
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem exists_unitary_coords_quot_of_three_le {n f : ℕ} (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t :
    G}
    (ht : orderOf t = 2) (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (C₀ : GL (Fin (2 * n)) K')
      (hC₀ : IsPrimeFormGram C₀) (_ : ¬(2 * n = 3 ∧ 2 ^ f = 2))
      (ε : spGlobal e ⧸ center (spGlobal e) ≃*
        primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')),
      (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n ∧
      MulAut.congr ε (centerQuotAction (spGlobal e) ⟨t, htN⟩) =
        primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h) := by
  have hS : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * n) 2 f := hglob.1.2.2
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  obtain ⟨K', _, h, C₀, hC₀, -, hq, φ, ε, hcase, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU' hS (centerQuotAction_mul_self ht htN) hout hfix
  have hφ' : φ = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hφ, UnitaryPilot.barRingEquiv_apply]
  rcases hcase with ⟨hodd, -⟩ | ⟨r, hr, hJ⟩
  · exact absurd (even_two_mul n) (Nat.not_even_iff_odd.2 hodd)
  · obtain rfl : r = n := by omega
    exact ⟨K', inferInstance, h, C₀, hC₀, hq, ε, hJ, hε.trans (by rw [hφ'])⟩

omit [Finite G] [Finite K] [CharP K 2] in
theorem cosetInnConjInput_unitaryEven_of_three_le {n f : ℕ} (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    CosetInnConjInput (centerQuotAction (spGlobal e) ⟨t, htN⟩) := by
  obtain ⟨K', _, h, C₀, hC₀, hq, ε, -, hε⟩ := exists_unitary_coords_quot_of_three_le hn e ht hglob
      htN
  apply cosetInnConjInput_of_congr ε
  rw [hε]
  exact cosetInnConjInput_fieldBar h C₀ hC₀ (by omega) hq

omit [Finite G] [CharP K 2] in
theorem spCosetCardOn_unitaryEven_of_three_le {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven)
    (htN : t ∈ normalizer (spGlobal e : Set G)) :
    SpCosetCardOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) := by
  intro y hy2
  obtain ⟨K', _, h, C₀, hC₀, hq, ε, hJ₀, hε⟩ := exists_unitary_coords_quot_of_three_le hn e ht
      hglob htN
  have : CharP K' 2 := h.charP
  have : Finite K' := h.finite
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  set fb := primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h) with hfb
  set α := MulAut.congr ε (MulAut.conj y * θt) with hαdef
  have hα : α = MulAut.conj (ε y) * fb := by
    rw [hαdef, map_mul, congr_conj_eq_conj_apply, hε]
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hy2, map_one]
  have hm : 3 ≤ 2 * n := by omega
  have hα1 : α ≠ 1 := by
    intro h1
    apply (hglob.2 htN).1
    have h2 : MulAut.conj y * θt = 1 :=
      (MulAut.congr ε).injective (by rw [← hαdef, h1, map_one])
    refine ⟨y⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hαo : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ε y)
  have hαψ : α = primeFormPsi h hC₀ ⟨⟨s, s.2.1⟩, UnitaryPilot.barRingEquiv h⟩ := by
    rw [hα, primeFormPsi_apply, primeFormConjHom_eq_conj, ← hs]
  have hfac : ∀ x, primeFormFieldFactor h hC₀ hm hq α x = h.bar x := by
    intro x
    rw [hαψ, primeFormFieldFactor_psi]
    rfl
  obtain ⟨-, -, C₁, hC₁, hcase₁, -, -, -, -, ⟨θ', -, hθ'α⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC₀ hm hq α hαo hfac
  have hφ : primeFormFieldFactor h hC₀ hm hq α = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hfac, UnitaryPilot.barRingEquiv_apply]
  have hαθ : α = MulAut.congr θ' (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hθ'α x, hφ]
    rfl
  rcases hcase₁ with h1 | ⟨r, hr, hJ⟩
  · right
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [← LinearPilot.card_fixedSubgroup_congr ε, ← hαdef, hαθ,
      LinearPilot.card_fixedSubgroup_congr]
    have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
    have := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
    obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h hm hq hC₁
      (Or.inl h1) _ (fun x => UnitaryPilot.barRingEquiv_apply h x)
    obtain rfl : Cl = 1 := by
      apply Units.ext
      apply Matrix.map_injective h.fixedField.subtype_injective
      change (Cl : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField).map h.fixedField.subtype =
        ((1 : GL (Fin (2 * n)) h.fixedField) : Matrix (Fin (2 * n)) (Fin (2 * n))
          h.fixedField).map h.fixedField.subtype
      rw [hCl, h1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Nat.card_congr Φ.toEquiv, card_matrixIsometryGroup_one_eq (F := h.fixedField)
      (by omega) h.card_fixedField (by omega) ⟨0, by omega⟩]
    have : Fintype K := Fintype.ofFinite K
    have : Fintype h.fixedField := Fintype.ofFinite h.fixedField
    set σ : K ≃+* h.fixedField := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h.card_fixedField])
      with hσ
    rw [← map_statedSpMap_centralizer_siegDiag σ,
      Subgroup.card_map_of_injective (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ n)]
  · left
    obtain rfl : r = n := by omega
    obtain rfl : C₁ = C₀ := Units.ext (hJ.trans hJ₀.symm)
    refine exists_mulAut_mul_eq_of_congr ε (γ := θ') ?_
    rw [hε, ← hαdef, hαθ, LinearPilot.mulAut_congr_eq_mul, hfb]
    group

omit [Finite G] in
theorem spPartnerShapeOn_unitaryEven_of_three_le {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven)
    (htN : t ∈ normalizer (spGlobal e : Set G))
    (α : MulAut (spGlobal e ⧸ center (spGlobal e))) {K'' : Type} [Field K'']
    (h'' : UnitaryFieldData 2 f K'')
    (ψ : spGlobal e ⧸ center (spGlobal e) ≃* primeFormP h'' ((1 : GL (Fin (2 * n)) K'') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K''))
    (θ : MulAut (primeFormP h'' ((1 : GL (Fin (2 * n)) K'') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K'')))
    (he : MulAut.congr ψ α =
      θ * primeFormFieldHom h'' isPrimeFormGram_one (UnitaryPilot.barRingEquiv h'') * θ⁻¹) :
    SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩) α := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨K', _, h, C₀, hC, hq, ε, hJ₀, hε⟩ := exists_unitary_coords_quot_of_three_le hn e ht hglob
      htN
  have : CharP K' 2 := h.charP
  have : Finite K' := h.finite
  have : CharP h.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  have : Finite h.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have : CharP K'' 2 := h''.charP
  have : Finite K'' := h''.finite
  have : CharP h''.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h''
  have : Finite h''.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h''
  have hm : 3 ≤ 2 * (m + 1) := by omega
  have hq'' : ¬(2 * (m + 1) = 3 ∧ 2 ^ f = 2) := by omega
  have hC1 : IsPrimeFormGram (1 : GL (Fin (2 * (m + 1))) K'') := isPrimeFormGram_one
  set fI := primeFormFieldHom h'' hC1 (UnitaryPilot.barRingEquiv h'') with hfI
  set fJ := primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) with hfJ
  have hαout : α ∉ (MulAut.conj : spGlobal e ⧸ center (spGlobal e) →* MulAut _).range := by
    rintro ⟨y, rfl⟩
    rw [congr_conj_eq_conj_apply] at he
    have h1 : fI = MulAut.conj (θ⁻¹ (ψ y)) := by
      calc fI = θ⁻¹ * (θ * fI * θ⁻¹) * θ := by group
        _ = θ⁻¹ * MulAut.conj (ψ y) * θ := by rw [← he]
        _ = MulAut.conj (θ⁻¹ (ψ y)) := by
            ext x
            simp [MulAut.conj_apply]
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (θ⁻¹ (ψ y))
    have h3 := primeFormFieldFactor_apply h'' hC1 hm hq'' 1 (UnitaryPilot.barRingEquiv h'')
    rw [map_one, one_mul, ← hfI, h1, ← hs, ← primeFormConjHom_eq_conj] at h3
    have h4 := primeFormFieldFactor_apply h'' hC1 hm hq'' ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one] at h4
    exact barRingEquiv_ne_one (h := h'') (h3.symm.trans h4)
  have hα2 : α * α = 1 := by
    apply (MulAut.congr ψ).injective
    rw [map_mul, he, map_one]
    calc θ * fI * θ⁻¹ * (θ * fI * θ⁻¹) = θ * (fI * fI) * θ⁻¹ := by group
      _ = 1 := by rw [hfI, fieldBar_mul_self, mul_one, mul_inv_cancel]
  set β := MulAut.congr ε α with hβdef
  have hβ2 : β * β = 1 := by rw [hβdef, ← map_mul, hα2, map_one]
  have hβout : β ∉ (MulAut.conj : primeFormP h (C₀ : Matrix (Fin (2 * (m + 1)))
      (Fin (2 * (m + 1))) K') →* MulAut _).range := by
    rintro ⟨y, hy⟩
    apply hαout
    refine ⟨ε.symm y, ?_⟩
    rw [← congr_conj_eq_conj_apply, hy, hβdef, mulAut_congr_symm_congr_apply]
  have hβ1 : β ≠ 1 := fun h1 => hβout ⟨1, by rw [map_one, h1]⟩
  have hβo : orderOf β = 2 := orderOf_eq_prime (by rw [sq]; exact hβ2) hβ1
  obtain ⟨hcases, hinn, -, -⟩ := even_unitary_involution_matrix_lifts h hC hm hq β hβo
  have hfacβ : ∀ x, primeFormFieldFactor h hC hm hq β x = h.bar x := by
    refine hcases.resolve_left fun hid => ?_
    obtain ⟨s, -, -, hs⟩ := hinn hid
    exact hβout ⟨_, ((primeFormConjHom_eq_conj h _ s).symm.trans hs.symm)⟩
  obtain ⟨-, -, C₁, hC₁, hcase₁, -, -, -, -, ⟨θ₁, -, hθ₁β⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hm hq β hβo hfacβ
  have hφ : primeFormFieldFactor h hC hm hq β = UnitaryPilot.barRingEquiv h :=
    RingEquiv.ext fun x => by rw [hfacβ, UnitaryPilot.barRingEquiv_apply]
  have hβθ : β = MulAut.congr θ₁ (primeFormFieldHom h hC₁ (UnitaryPilot.barRingEquiv h)) := by
    refine MulEquiv.ext fun x => ?_
    rw [hθ₁β x, hφ]
    rfl
  have : Fintype K := Fintype.ofFinite K
  have : Fintype h.fixedField := Fintype.ofFinite h.fixedField
  have : Fintype h''.fixedField := Fintype.ofFinite h''.fixedField
  set σ : K ≃+* h.fixedField := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h.card_fixedField]) with hσ
  set σ'' : K ≃+* h''.fixedField := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h''.card_fixedField])
    with hσ''
  have hp0 : 0 < m + 1 := by omega
  have hcardα : Nat.card (fixedSubgroup α) =
      Nat.card (centralizer ({siegDiag K ⟨0, hp0⟩ 1} : Set (StatedSp (m + 1) K))) := by
    rw [← LinearPilot.card_fixedSubgroup_congr ψ, he, ← LinearPilot.mulAut_congr_eq_mul,
      LinearPilot.card_fixedSubgroup_congr]
    obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h'' hm hq'' hC1
      (Or.inl (by rw [Units.val_one])) _ (fun x => UnitaryPilot.barRingEquiv_apply h'' x)
    obtain rfl : Cl = 1 := by
      apply Units.ext
      apply Matrix.map_injective h''.fixedField.subtype_injective
      change (Cl : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) h''.fixedField).map
          h''.fixedField.subtype =
        ((1 : GL (Fin (2 * (m + 1))) h''.fixedField) : Matrix (Fin (2 * (m + 1)))
          (Fin (2 * (m + 1))) h''.fixedField).map h''.fixedField.subtype
      rw [hCl, Units.val_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Nat.card_congr Φ.toEquiv, card_matrixIsometryGroup_one_eq (F := h''.fixedField)
      (by omega) h''.card_fixedField (by omega) ⟨0, hp0⟩,
      ← map_statedSpMap_centralizer_siegDiag σ'',
      Subgroup.card_map_of_injective (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1))]
  rcases hcase₁ with h1 | ⟨r, hr, hJ⟩
  swap
  · exfalso
    have hrn : m + 1 = r := by omega
    subst hrn
    obtain rfl : C₁ = C₀ := Units.ext (hJ.trans hJ₀.symm)
    have h2 : Nat.card (fixedSubgroup α) = Nat.card (StatedSp (m + 1) K) := by
      rw [← LinearPilot.card_fixedSubgroup_congr ε, ← hβdef, hβθ,
        LinearPilot.card_fixedSubgroup_congr, ← range_uModelP (by omega) hq hC₁ hJ₀,
        ← Nat.card_congr (MonoidHom.ofInjective (uModelP_injective (by omega) hJ₀)).toEquiv,
        card_statedSp_eq_of_ringEquiv σ]
    have h3 := card_centralizer_siegDiag_lt (K := K) (⟨0, hp0⟩ : Fin (m + 1))
    omega
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 1), p = ⟨0, hp0⟩ := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂, θ', h2, hθ'⟩ :=
    exists_iType_conj_uModel_siegDiag (h := h) (by omega) hq hC hJ₀ p
  obtain rfl : C₂ = C₁ := Units.ext (h2.trans h1.symm)
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : MulAut (primeFormP h (C₀ : Matrix (Fin (2 * (m + 1)))
      (Fin (2 * (m + 1))) K')), Γ = θ'.symm.trans θ₁ := ⟨_, rfl⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : primeFormP h (C₀ : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) K') ≃*
      spGlobal e ⧸ center (spGlobal e), Ξ = Γ.trans ε.symm := ⟨_, rfl⟩
  obtain ⟨Zp, hZp⟩ : ∃ Zp, Zp = uModelP h hJ₀ (siegDiag h.fixedField p 1) := ⟨_, rfl⟩
  have hβΓ : β = MulAut.congr Γ (MulAut.conj Zp * fJ) := by
    rw [hβθ, hZp, hfJ, hθ', hΓ, mulAut_congr_trans_apply, mulAut_congr_symm_congr_apply]
  have hαΞ : α = MulAut.congr Ξ (MulAut.conj Zp * fJ) := by
    rw [hΞ, mulAut_congr_trans_apply, ← hβΓ, hβdef, mulAut_congr_symm_congr_apply]
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : StatedSp (m + 1) K →* spGlobal e ⧸ center (spGlobal e), ψ₀ =
    Ξ.toMonoidHom.comp ((uModelP h hJ₀).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* h.fixedField) (m + 1))) := ⟨_, rfl⟩
  have hψ₀inj : Function.Injective ψ₀ := by
    rw [hψ₀]
    exact Ξ.injective.comp ((uModelP_injective (by omega) hJ₀).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1)))
  have hψ₀z : ψ₀ (siegDiag K p 1) = Ξ Zp := by
    rw [hψ₀, hZp]
    change Ξ (uModelP h hJ₀ (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* h.fixedField)
      (m + 1) (siegDiag K p 1))) = _
    rw [statedSpMap_siegDiag]
  obtain ⟨η, hη⟩ : ∃ η : MulAut (spGlobal e ⧸ center (spGlobal e)), η = MulAut.congr Ξ fJ :=
    ⟨_, rfl⟩
  refine spPartnerShapeOn_of_embedding hK4 (by omega : 1 ≤ m) (η := η) ψ₀ hψ₀inj p ?_ ?_ ?_ ?_
  · rw [hψ₀z, hαΞ, map_mul, congr_conj_eq_conj_apply, hη]
  · rw [hψ₀z, hη]
    change Ξ (fJ (Ξ.symm (Ξ Zp))) = Ξ Zp
    rw [MulEquiv.symm_apply_apply, hfJ, hZp, fieldBar_uModelP hC hJ₀]
  · refine exists_mulAut_mul_eq_of_congr ε (γ := Γ) ?_
    rw [hε, hη, hΞ, mulAut_congr_trans_apply, mulAut_congr_congr_symm_apply,
      LinearPilot.mulAut_congr_eq_mul]
    group
  · rw [hαΞ, LinearPilot.fixedSubgroup_congr_eq_map, hZp, hfJ,
      fixedSubgroup_conj_uModel_siegDiag_mul_fieldBar (by omega) hC hJ₀ p, hψ₀,
      ← Subgroup.map_map, ← Subgroup.map_map, map_statedSpMap_centralizer_siegDiag σ p]

theorem pieceCore_last_le_centralizer_unitaryEven {n f : ℕ} (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven) :
    pieceCore e ({⟨n - 1, by omega⟩} : Finset (Fin n)) ≤ centralizer ({t} : Set G) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨K', _, h, C₀, hC, hq, ε, hJ₀, hε⟩ := exists_unitary_coords_quot_of_three_le hn e ht hglob
      htN
  have : CharP h.fixedField 2 := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  have : Finite h.fixedField := UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have : Finite K' := h.finite
  have : Finite (primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) := by infer_instance
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  have hLG : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  set π : spGlobal e →* spGlobal e ⧸ center (spGlobal e) :=
    QuotientGroup.mk' (center (spGlobal e)) with hπ
  set L₀ : Subgroup (spGlobal e) := L.subgroupOf (spGlobal e) with hL₀
  have : Fintype K := Fintype.ofFinite K
  have : Fintype h.fixedField := Fintype.ofFinite h.fixedField
  set σ : K ≃+* h.fixedField := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKc, h.card_fixedField]) with hσ
  set Φ : primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') ≃*
    spGlobal e ⧸ center (spGlobal e) := ε.symm with hΦ
  have hfix : fixedSubgroup θt = (uModelP h hJ₀).range.map Φ.toMonoidHom := by
    have h1 : MulAut.congr ε θt =
        1 * primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) * 1⁻¹ := by
      rw [hε]
      group
    rw [fixedSubgroup_eq_map_of_congr ε h1, range_uModelP (by omega) hq hC hJ₀]
    congr 1
    exact Subgroup.map_id _
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
      ← Nat.card_congr (MonoidHom.ofInjective (uModelP_injective (by omega) hJ₀)).toEquiv]
  set ψ : StatedSp n K →* spGlobal e ⧸ center (spGlobal e) :=
    Φ.toMonoidHom.comp ((uModelP h hJ₀).comp (statedSpMap (σ : K →+* h.fixedField) n)) with hψ
  have hψinj : Function.Injective ψ :=
    Φ.injective.comp ((uModelP_injective (by omega) hJ₀).comp (statedSpMap_injective _ n))
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
          ((uModelP h hJ₀).comp (statedSpMap (σ : K →+* h.fixedField) n))).map
            Φ.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rw [hY, centralizer_map_mulEquiv_toMonoidHom Φ, ← map_perfectCore] at h1
    have h2 := perfectCore_centralizer_conj_torus_le_unitary (by omega) hq hlast hC hJ₀ σ hκ₀ u
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

end Unitary

section Partner

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem not_spPartnerShapeQuot_of_three_le {κ : Sp2mKind} (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f κ) (htN : t ∈ normalizer (spGlobal e : Set G))
    (hInn' : CosetInnConjInput (centerQuotAction (spGlobal e) ⟨t, htN⟩))
    (hCard' : SpCosetCardOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩))
    (hTor' : pieceCore e ({⟨n - 1, by omega⟩} : Finset (Fin n)) ≤ centralizer ({t} : Set G))
    (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ¬ SpPartnerShapeOn n K (centerQuotAction (spGlobal e) ⟨t, htN⟩)
      (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) := by
  intro hsh
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  have : Group.IsPerfect (spGlobal e) := hglob.1.1.1
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have htZ : t ∉ centralizer (spGlobal e : Set G) := by
    intro htZ
    apply (hglob.2 htN).1
    refine ⟨1, ?_⟩
    rw [map_one]
    exact (EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer (MulEquiv.refl _) htN htZ).symm
  have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hlast : (⟨m + 3 - 1, by omega⟩ : Fin (m + 3)) = Fin.last (m + 2) :=
    Fin.ext (by simp)
  rw [hlast] at hTor'
  exact false_of_spPartnerShapeQuot hset hKc hf e ht hKt hLS hZ htN hodd
    (fun h hh γ hγ => mem_normalizer_of_conj_centerQuotAction hset (by omega) hKc hf e ht hKt
      hglob.1.1.1 hZ htN hh γ hγ) hInn' hCard' hTor' hg hsh

end Partner

section Classes

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem ne_dualAut_of_conj_linearEven_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f)
    (ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F)
    (H : GL (Fin (2 * n)) F) :
    MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) ≠
      LinearFlag.conjAut (2 * n) F H * LinearFlag.dualAut (2 * n) F *
        (LinearFlag.conjAut (2 * n) F H)⁻¹ := by
  intro he
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  exact not_spPartnerShapeQuot_of_three_le hset hn hKc hf e ht hKt hglob htN
    (cosetInnConjInput_linearEven_of_three_le hset hn hKc hf e ht hKt hglob htN)
    (spCosetCardOn_linearEven_of_three_le hset hn hKc hf e ht hKt hglob htN)
    (pieceCore_last_le_centralizer_linearEven hset hn hKc hf e ht hKt hglob) g hg
    (spPartnerShapeOn_linearEven_of_three_le hset hn hKc hf e ht hKt hglob htN _ hF ε H he)

theorem ne_fieldBar_of_conj_unitaryEven_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K')
    (ψ : spGlobal e ⧸ center (spGlobal e) ≃* primeFormP h ((1 : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
    (θ : MulAut (primeFormP h ((1 : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K'))) :
    MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) ≠
      θ * primeFormFieldHom h isPrimeFormGram_one (UnitaryPilot.barRingEquiv h) * θ⁻¹ := by
  intro he
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  exact not_spPartnerShapeQuot_of_three_le hset hn hKc hf e ht hKt hglob htN
    (cosetInnConjInput_unitaryEven_of_three_le hn e ht hglob htN)
    (spCosetCardOn_unitaryEven_of_three_le hn hKc hf e ht hglob htN)
    (pieceCore_last_le_centralizer_unitaryEven hn hKc hf e ht hKt hglob) g hg
    (spPartnerShapeOn_unitaryEven_of_three_le hn hKc hf e ht hglob htN _ h ψ θ he)

theorem exists_conj_centerQuotAction_linearEven (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven) (htN : t ∈ normalizer (spGlobal e : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ∃ γ : MulAut (spGlobal e ⧸ center (spGlobal e)),
      γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
        centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * n) 2 f := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSL (2 * n) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * n) F).symm with hεdef
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
      ∃ H C : GL (Fin (2 * n)) F,
        (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = blockSwapJ (2 * n) n ∧
        MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) =
          LinearFlag.conjAut (2 * n) F H *
            (LinearFlag.conjAut (2 * n) F C * LinearFlag.dualAut (2 * n) F) *
              (LinearFlag.conjAut (2 * n) F H)⁻¹ := by
    intro g hg
    have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    have hαw : MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
    have hdw : Nat.card (fixedSubgroup (MulAut.congr ε
        (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩))) ∣
          2 * (Nat.card (StatedSp n K) * f) := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) hw2 hg).trans
        (card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg)
    obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
      (by omega) hF hKc (Or.inl rfl) hαw hdw
    rcases hc with h1 | ⟨-, hJ⟩
    · exfalso
      have hC1 : C = 1 := Units.ext h1
      rw [hC1, map_one, one_mul] at he
      exact ne_dualAut_of_conj_linearEven_of_three_le hset hn hKc hf e ht hKt hglob g hg hF ε H he
    · exact ⟨H, C, hJ, he⟩
  obtain ⟨hg1, he1⟩ := centerQuotAction_one_conj htN
  obtain ⟨H₁, C₁, hJ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨H₂, C₂, hJ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ε
    (γ := LinearFlag.conjAut (2 * n) F H₂ * (LinearFlag.conjAut (2 * n) F H₁)⁻¹) ?_
  rw [h₁, h₂]
  group

theorem exists_conj_centerQuotAction_unitaryEven (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven) (htN : t ∈ normalizer (spGlobal e : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ∃ γ : MulAut (spGlobal e ⧸ center (spGlobal e)),
      γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
        centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * n) 2 f := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSU (2 * n) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have hq : ¬(2 * n = 3 ∧ 2 ^ f = 2) := by omega
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K'), orderOf y = 2 →
      f * n ^ 2 + 1 + f.factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))))).factorization 2 := by
    intro y hy
    set φ := OutcomeLocal.primeFormOneEquiv h (2 * n)
    have h1 := unitaryEvenInnerTwoPart_holds f K' h n (by omega) (φ y) (by rw [MulEquiv.orderOf_eq,
        hy])
    rw [card_centralizer_map_mulEquiv] at h1
    have h3 : f * (n ^ 2 + 2) = f * n ^ 2 + 2 * f := by ring
    omega
  have hy0 := exists_orderOf_eq_two_of_mulEquiv_quot (by omega) hKc hf e ht hKt hZ ψ
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
      ∃ (C₀ : GL (Fin (2 * n)) K') (hC₀ : IsPrimeFormGram C₀),
        (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n ∧
        ∃ θ : primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') ≃*
            primeFormP h ((1 : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K'),
          MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) =
            MulAut.congr θ (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h)) := by
    intro g hg
    have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    have hαw : MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
    have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ
        (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩)))).factorization 2 ≤
          f * n ^ 2 + 1 + f.factorization 2 := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
        (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
    obtain ⟨C₀, hC₀, hc, θ, he⟩ :=
      exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
    rcases hc with h1 | ⟨r, hr, hJ⟩
    · exfalso
      have hC1 : C₀ = 1 := Units.ext h1
      subst hC1
      refine ne_fieldBar_of_conj_unitaryEven_of_three_le hset hn hKc hf e ht hKt hglob g hg h ψ θ ?_
      rw [he, LinearPilot.mulAut_congr_eq_mul]
    · obtain rfl : r = n := by omega
      exact ⟨C₀, hC₀, hJ, θ, he⟩
  obtain ⟨hg1, he1⟩ := centerQuotAction_one_conj htN
  obtain ⟨C₁, hC₁, hJ₁, θ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨C₂, hC₂, hJ₂, θ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ψ (γ := θ₁.symm.trans θ₂) ?_
  rw [h₁, h₂]
  exact symm_trans_mul_congr θ₁ θ₂ _

theorem mem_normalizer_of_conj_linearEven (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearEven) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    g ∈ normalizer (spGlobal e : Set G) := by
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  obtain ⟨γ, hγ⟩ := exists_conj_centerQuotAction_linearEven hset hn hKc hf e ht hKt hglob htN hg
  exact mem_normalizer_of_conj_centerQuotAction hset hn hKc hf e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

theorem mem_normalizer_of_conj_unitaryEven (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryEven) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    g ∈ normalizer (spGlobal e : Set G) := by
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  obtain ⟨γ, hγ⟩ := exists_conj_centerQuotAction_unitaryEven hset hn hKc hf e ht hKt hglob htN hg
  exact mem_normalizer_of_conj_centerQuotAction hset hn hKc hf e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

end Classes

section Rows


open Subgroup CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_coverType_linearEven (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : SpGlobalCoverType e f .linearEven) : False := by
  have hglob := spOmegaRowGlobalQuot_of_coverType hset hn hKc hf e ht hKt (Or.inl rfl) hcov
  exact false_of_spLinearRow_of_globalQuot hset e ht hKt (Or.inl rfl) hglob
    (mem_normalizer_of_conj_linearEven hset hn hKc hf e ht hKt hglob)

theorem false_of_coverType_unitaryEven (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : SpGlobalCoverType e f .unitaryEven) : False := by
  have hglob := spOmegaRowGlobalQuot_of_coverType hset hn hKc hf e ht hKt (Or.inr (Or.inl rfl))
    hcov
  exact false_of_spUnitaryRow_of_globalQuot hset hKc hf e ht hKt (Or.inl rfl) hglob
    (mem_normalizer_of_conj_unitaryEven hset hn hKc hf e ht hKt hglob)

end Rows

end CFSG.SeitzReduction.SymplecticPilot


