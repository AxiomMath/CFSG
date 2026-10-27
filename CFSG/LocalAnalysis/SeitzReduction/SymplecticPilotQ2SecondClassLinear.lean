module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SecondClassPartner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open LinearFlag CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

section CharTwo

theorem not_isCharacteristicP_two_of_isSimpleGroup {X : Type*} [Group X] [IsSimpleGroup X]
    {y : X} (hy : orderOf y = 3) : ¬ IsCharacteristicP 2 X := by
  intro h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := pCore 2 X) with hb | ht
  · have hy1 : y ∈ pCore 2 X := by
      apply h
      rw [hb]
      rw [mem_centralizer_iff]
      intro z hz
      rw [SetLike.mem_coe, mem_bot] at hz
      rw [hz, one_mul, mul_one]
    rw [hb, mem_bot] at hy1
    rw [hy1, orderOf_one] at hy
    omega
  · have hyc : y ∈ pCore 2 X := ht ▸ mem_top y
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 pCore_isPGroup) ⟨y, hyc⟩
    rw [Subgroup.orderOf_mk, hy] at hk
    rcases k with _ | _ | k
    · simp at hk
    · simp at hk
    · have : 4 ≤ 2 ^ (k + 2) := by
        rw [pow_add]
        have := Nat.one_le_two_pow (n := k)
        omega
      omega

theorem not_isCharacteristicP_fixedSubgroup_blockSwapJ_two {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n) {C : GL (Fin (2 * n)) F}
    (hC : (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = UnitaryHigher.blockSwapJ (2 * n) n) :
    ¬ IsCharacteristicP 2 (fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F)) := by
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  have hrange := range_spModelPSL (n := n) le_rfl hF' (by omega) hC
  set E : StatedSp n F ≃* fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F) :=
    (MonoidHom.ofInjective (spModelPSL_injective (n := n) (F := F) (by omega))).trans
      (MulEquiv.subgroupCongr hrange) with hE
  have : IsSimpleGroup (StatedSp n F) := isSimpleGroup_statedSp_two hF hn
  have : IsSimpleGroup (fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F)) :=
    E.symm.isSimpleGroup_congr.2 this
  have hy : orderOf (E (nsElt (K := F) (⟨0, by omega⟩ : Fin n))) = 3 := by
    rw [MulEquiv.orderOf_eq, orderOf_nsElt]
  exact not_isCharacteristicP_two_of_isSimpleGroup hy

end CharTwo

section Coords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_graph_coords_of_equiv_ns (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (ε : nsGlobal e ≃* projectiveSL (2 * (m + 1)) F) :
    ∃ H₁ : GL (Fin (2 * (m + 1))) F,
      MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
        conjAut (2 * (m + 1)) F H₁ * (conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) *
          dualAut (2 * (m + 1)) F) * (conjAut (2 * (m + 1)) F H₁)⁻¹ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  set θt := (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθt
  have hθθ : MulAut.congr ε θt * MulAut.congr ε θt = 1 := by
    rw [← map_mul, hθt, normalizerMonoidHom_mul_self htt htN, map_one]
  have hdvd : Nat.card (fixedSubgroup (MulAut.congr ε θt)) ∣
      2 * (Nat.card (StatedSp (m + 1) K) * 1) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact card_fixedSubgroup_dvd_of_mem hset (by omega) hKc e ht hKt htN
  obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    le_rfl hF' hKc (Or.inl rfl) hθθ hdvd
  have hfixt : LieModel (fixedSubgroup θt) .PSp (m + 1) 2 1 := (hglob.2 htN).2
  have hfix' : LieModel (fixedSubgroup (MulAut.congr ε θt)) .PSp (m + 1) 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θt) hfixt
  rw [he, ← LinearPilot.mulAut_congr_eq_mul] at hfix'
  have hfixC : LieModel (fixedSubgroup (conjAut (2 * (m + 1)) F C * dualAut (2 * (m + 1)) F))
      .PSp (m + 1) 2 1 :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv (conjAut _ F H) _).symm
      hfix'
  rcases hc with h1 | ⟨-, hJ⟩
  · exact absurd hfixC (not_lieModel_PSp_fixedSubgroup_dualAut_one le_rfl hF' (by omega)
      (even_two_mul _) h1)
  · obtain rfl : C = spBlockSwapGL (m + 1) F := Units.ext (hJ.trans coe_spBlockSwapGL.symm)
    exact ⟨H, he⟩

theorem exists_coords_nsLinearEven (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (ε : nsGlobal e ≃* projectiveSL (2 * (m + 1)) F) (H : GL (Fin (2 * (m + 1))) F),
      Nat.card F = 2 ∧
      MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
        conjAut (2 * (m + 1)) F H * (conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) *
          dualAut (2 * (m + 1)) F) * (conjAut (2 * (m + 1)) F H)⁻¹ := by
  have hty' : LieModel (nsGlobal e) .PSL (2 * (m + 1)) 2 1 := hglob.1
  have hadm : StatedLieAdmissible .PSL (2 * (m + 1)) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  set ε : nsGlobal e ≃* projectiveSL (2 * (m + 1)) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * (m + 1)) F).symm with hεdef
  obtain ⟨H, he⟩ := exists_graph_coords_of_equiv_ns hset hK hm e ht hKt hglob htN hF2 ε
  exact ⟨F, inferInstance, inferInstance, inferInstance, ε, H, hF2, he⟩

end Coords

section Shape

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsPartnerShape_of_iType (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    {α : MulAut (nsGlobal e)} {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (ε : nsGlobal e ≃* projectiveSL (2 * (m + 1)) F) (H : GL (Fin (2 * (m + 1))) F)
    (he : MulAut.congr ε α = conjAut (2 * (m + 1)) F H * dualAut (2 * (m + 1)) F *
      (conjAut (2 * (m + 1)) F H)⁻¹) :
    NsPartnerShape e ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) α := by
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  obtain ⟨H₁, hH₁⟩ := exists_graph_coords_of_equiv_ns hset hK hm e ht hKt hglob htN hF ε
  set p : Fin (m + 1) := 0 with hp
  set zP := spModelPSL (m + 1) F (siegDiag F p 1) with hzP
  set β := conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) * dualAut (2 * (m + 1)) F with hβ
  obtain ⟨H', hconj, -⟩ := exists_normalForm_conj_siegDiag le_rfl hF' (by omega) p
  have : Fintype K := Fintype.ofFinite K
  have : Fintype F := Fintype.ofFinite F
  set σ : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF]) with hσ
  set Φ : projectiveSL (2 * (m + 1)) F ≃* nsGlobal e :=
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
        (conjAut (2 * (m + 1)) F H' * dualAut (2 * (m + 1)) F *
          (conjAut (2 * (m + 1)) F H')⁻¹) *
          (conjAut (2 * (m + 1)) F H' * (conjAut (2 * (m + 1)) F H)⁻¹) =
        MulAut.congr ε α := by
      rw [he]
      group
    rw [h1, mulAut_congr_symm_congr_apply]
  set ρ : StatedSp (m + 1) K →* nsGlobal e :=
    Φ.toMonoidHom.comp ((spModelPSL (m + 1) F).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* F) (m + 1))) with hρ
  have hρinj : Function.Injective ρ :=
    Φ.injective.comp ((spModelPSL_injective (by omega)).comp
      (CFSG.SeitzReduction.F4Pilot.statedSpMap_injective _ (m + 1)))
  have hρz : ρ (siegDiag K p 1) = Φ zP := by
    simp only [hρ, MonoidHom.coe_comp, Function.comp_apply, statedSpMap_siegDiag]
    rfl
  set η : MulAut (nsGlobal e) := MulAut.congr Φ β with hη
  refine ⟨ρ, η, p, hρinj, ?_, ?_, ?_, ?_⟩
  · rw [hρz, hαΦ, map_mul, congr_conj_eq_conj_apply]
  · intro y
    change Φ (β (Φ.symm (Φ (spModelPSL (m + 1) F
      (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* F) (m + 1) y))))) =
        Φ (spModelPSL (m + 1) F (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* F) (m + 1) y))
    rw [MulEquiv.symm_apply_apply, hβ, conjAut_dualAut_spModelPSL (by omega) coe_spBlockSwapGL]
  · refine exists_mulAut_mul_eq_of_congr ε
      (γ := conjAut (2 * (m + 1)) F H * (conjAut (2 * (m + 1)) F H')⁻¹ *
        (conjAut (2 * (m + 1)) F H₁)⁻¹) ?_
    rw [hH₁, hη, hΦcongr, mulAut_congr_congr_symm_apply]
    group
  · rw [hαΦ, LinearPilot.fixedSubgroup_congr_eq_map,
      fixedSubgroup_conj_siegDiag_mul_graph le_rfl hF' (by omega) p, hρ,
      ← Subgroup.map_map, ← Subgroup.map_map, map_statedSpMap_centralizer_siegDiag σ p]

end Shape

section Coset

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem lieModel_fixedSubgroup_blockSwapJ_of_coords {m : ℕ} (e : L ≃* StatedSp (m + 1) K)
    {t : G} (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    {F : Type} [Field F] [CharP F 2] (ε : nsGlobal e ≃* projectiveSL (2 * (m + 1)) F)
    {H₁ : GL (Fin (2 * (m + 1))) F}
    (he : MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) =
      conjAut (2 * (m + 1)) F H₁ * (conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) *
        dualAut (2 * (m + 1)) F) * (conjAut (2 * (m + 1)) F H₁)⁻¹) :
    LieModel (fixedSubgroup (conjAut (2 * (m + 1)) F (spBlockSwapGL (m + 1) F) *
      dualAut (2 * (m + 1)) F)) .PSp (m + 1) 2 1 := by
  have hfixt := (hglob.2 htN).2
  have hfix' := LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε _) hfixt
  rw [he, ← LinearPilot.mulAut_congr_eq_mul] at hfix'
  exact LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv (conjAut _ F H₁) _).symm
    hfix'

theorem cosetInnConjInput_nsLinearEven (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    CosetInnConjInput ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) := by
  obtain ⟨F, _, _, _, ε, H, hF, he⟩ := exists_coords_nsLinearEven hset hK hm e ht hKt hglob htN
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  have hmod := cosetInnConjInput_blockSwapJ le_rfl hF' (by omega : 3 ≤ 2 * (m + 1)) rfl
    coe_spBlockSwapGL
    (lieModel_fixedSubgroup_blockSwapJ_of_coords e hglob htN ε he)
  apply cosetInnConjInput_of_congr ε
  rw [he, ← LinearPilot.mulAut_congr_eq_mul]
  exact cosetInnConjInput_congr _ hmod

theorem nsCosetCardInput_nsLinearEven (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G)) :
    NsCosetCardInput e ((nsGlobal e).normalizerMonoidHom ⟨t, htN⟩) := by
  intro y hy2
  obtain ⟨F, _, _, _, ε, H, hF, he⟩ := exists_coords_nsLinearEven hset hK hm e ht hKt hglob htN
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  set θt := (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθt
  set C := spBlockSwapGL (m + 1) F with hCdef
  obtain ⟨g, hg⟩ := proj_surjective (2 * (m + 1)) F (ε y)
  set A : GL (Fin (2 * (m + 1))) F := SpecialLinearGroup.toGL g * H * C *
    GeneralLinearGroup.inverseTranspose H⁻¹ with hA
  have hδ : conjAut (2 * (m + 1)) F (GeneralLinearGroup.inverseTranspose H⁻¹) *
      dualAut (2 * (m + 1)) F = dualAut (2 * (m + 1)) F * (conjAut (2 * (m + 1)) F H)⁻¹ := by
    rw [← dualAut_mul_conjAut, map_inv]
  have hyA : MulAut.congr ε (MulAut.conj y * θt) =
      conjAut (2 * (m + 1)) F A * dualAut (2 * (m + 1)) F := by
    calc MulAut.congr ε (MulAut.conj y * θt) =
        conjAut (2 * (m + 1)) F (SpecialLinearGroup.toGL g) * (conjAut (2 * (m + 1)) F H *
          (conjAut (2 * (m + 1)) F C * dualAut (2 * (m + 1)) F) *
            (conjAut (2 * (m + 1)) F H)⁻¹) := by
          rw [map_mul, congr_conj_eq_conj_apply, he, ← hg, ← conjAut_toGL]
      _ = conjAut (2 * (m + 1)) F (SpecialLinearGroup.toGL g) * conjAut (2 * (m + 1)) F H *
          conjAut (2 * (m + 1)) F C *
            (dualAut (2 * (m + 1)) F * (conjAut (2 * (m + 1)) F H)⁻¹) := by group
      _ = conjAut (2 * (m + 1)) F (SpecialLinearGroup.toGL g) * conjAut (2 * (m + 1)) F H *
          conjAut (2 * (m + 1)) F C *
            (conjAut (2 * (m + 1)) F (GeneralLinearGroup.inverseTranspose H⁻¹) *
              dualAut (2 * (m + 1)) F) := by rw [hδ]
      _ = conjAut (2 * (m + 1)) F A * dualAut (2 * (m + 1)) F := by
          rw [hA, map_mul, map_mul, map_mul]
          group
  have hA2 : (conjAut (2 * (m + 1)) F A * dualAut (2 * (m + 1)) F) ^ 2 = 1 := by
    rw [sq, ← hyA, ← map_mul, hy2, map_one]
  obtain ⟨-, ⟨H', C', -, hconj, hC'⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms le_rfl hF' (by omega) A hA2
  rcases hC' with ⟨hC'1, -⟩ | ⟨r', hr', hC'J, -⟩
  · right
    have hC1 : C' = 1 := Units.ext hC'1
    rw [hC1, map_one, one_mul] at hconj
    obtain ⟨ρ, η, p, hρ, -, -, -, hfix⟩ :=
      nsPartnerShape_of_iType hset hK hm e ht hKt hglob htN hF ε H' (hyA.trans hconj)
    exact ⟨p, by rw [hfix, Subgroup.card_map_of_injective hρ]⟩
  · left
    obtain rfl : r' = m + 1 := by omega
    have hCC' : C' = C := Units.ext (hC'J.trans coe_spBlockSwapGL.symm)
    subst hCC'
    refine exists_mulAut_mul_eq_of_congr ε
      (γ := conjAut (2 * (m + 1)) F H' * (conjAut (2 * (m + 1)) F H)⁻¹) ?_
    rw [hyA, hconj, he]
    group

theorem spTwoLinearEvenSecondClassInput_holds : SpTwoLinearEvenSecondClassInput := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt _ hglob g hg hchar
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨F, _, _, _, ε, H, hF, he⟩ :=
    exists_coords_nsLinearEven hset hK (by omega) e ht hKt hglob htN
  have hF' : Nat.card F = 2 ^ 1 := by rw [hF, pow_one]
  set θw := (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθw
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
    have hsh := nsPartnerShape_of_iType hset hK (by omega) e ht hKt hglob htN hF ε H₂ he₂
    have hLS : L ≤ nsGlobal e := le_nsGlobal hK (by omega) e
    have htZ : t ∉ centralizer (nsGlobal e : Set G) := by
      intro htZ
      apply ((hglob.2 htN).1)
      refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
      rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
    have hodd := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLS ht htN htZ
    exact false_of_nsPartnerShape hset hK (by omega) e ht hKt htN hodd
      (cosetInnConjInput_nsLinearEven hset hK (by omega) e ht hKt hglob htN)
      (nsCosetCardInput_nsLinearEven hset hK (by omega) e ht hKt hglob htN) hg hsh
  ·
    rw [← LinearPilot.mulAut_congr_eq_mul] at he₂
    have Φ := (fixedSubgroupCongrEquiv ε θw).trans ((MulEquiv.subgroupCongr
      (congrArg fixedSubgroup he₂)).trans (fixedSubgroupCongrEquiv (conjAut _ F H₂) _).symm)
    exact not_isCharacteristicP_fixedSubgroup_blockSwapJ_two hF (by omega) hJ₂
      (isCharacteristicP_of_mulEquiv Φ hchar)

end Coset

end CFSG.SeitzReduction.SymplecticPilot
