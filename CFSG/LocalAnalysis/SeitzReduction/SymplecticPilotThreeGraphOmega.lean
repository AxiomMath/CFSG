module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowMinusOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

section PlusRecognition

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (B12 B23 blockSL)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL leviEmbedSL_injective)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {m : ℕ}

theorem sp2mKindType_omegaPlus_of_pieces_of_one_le [Finite G] {f : ℕ} (hm : 1 ≤ m)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K)
    (h : SpOmegaPlusPieces e) : Sp2mKindType (spGlobal e) (m + 2) f .omegaPlus := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨hshort, A, B, hAB, hfork, hfar, ⟨θA, hθA, hA12, hA23⟩, ⟨θB, hθB, hB12, hB23⟩⟩ := h
  set U := omegaPlusNode e A B with hUdef
  have hG₀ := spGlobal_eq_iSup_omegaPlusNode hK4 e hshort hfork
  have hAle : A ≤ pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) :=
    hfork ▸ le_sup_left
  have hBle : B ≤ pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) :=
    hfork ▸ le_sup_right
  have hfin : ∀ a b : Fin (m + 2), a.val = b.val →
      modelToG e (simpleRootSL2 K a) = modelToG e (simpleRootSL2 K b) := fun a b hab => by
    rw [Fin.ext hab]
  have hfar' : ∀ i j : Fin (m + 3), i.val + 1 ≤ m → m + 1 ≤ j.val →
      U i ≤ centralizer (U j : Set G) := by
    intro i j hi hj
    rw [hUdef, omegaPlusNode_of_le e A B (by omega)]
    refine (hfar ⟨i.val, by omega⟩ (by simp only; omega)).trans (centralizer_le ?_)
    by_cases hj' : j.val = m + 1
    · rw [omegaPlusNode_of_eq_succ e A B hj']
      exact hAle
    · rw [omegaPlusNode_of_eq_add_two e A B (by have := j.isLt; omega)]
      exact hBle
  have hcomm : ∀ i j : Fin (m + 3), i ≠ j → ¬ edgeD (m + 3) i j → ¬ edgeD (m + 3) j i →
      U i ≤ centralizer (U j : Set G) := by
    intro i j hij h1 h2
    unfold edgeD at h1 h2
    have hiv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have hi := i.isLt
    have hj := j.isLt
    by_cases hi' : i.val ≤ m
    · by_cases hj' : j.val ≤ m
      · rw [hUdef, omegaPlusNode_of_le e A B hi', omegaPlusNode_of_le e A B hj']
        refine UnitaryPilot.modelToG_le_centralizer e ?_
        rcases lt_or_gt_of_ne hiv with hlt | hgt
        · exact kOmega_simpleRootSL2_le_centralizer (by simp only; omega)
        · exact le_centralizer_iff.1 (kOmega_simpleRootSL2_le_centralizer
            (by simp only; omega))
      · exact hfar' i j (by omega) (by omega)
    · by_cases hj' : j.val ≤ m
      · exact le_centralizer_iff.1 (hfar' j i (by omega) (by omega))
      · by_cases hiA : i.val = m + 1
        · rw [hUdef, omegaPlusNode_of_eq_succ e A B hiA, omegaPlusNode_of_eq_add_two e A B
            (by omega)]
          exact hAB
        · rw [hUdef, omegaPlusNode_of_eq_add_two e A B (by omega), omegaPlusNode_of_eq_succ e A B
            (by omega)]
          exact le_centralizer_iff.1 hAB
  have hpair : ∀ i j : Fin (m + 3), edgeD (m + 3) i j → ∃ θ : SL(3, K) →* G,
      θ.ker ≤ center SL(3, K) ∧ (B12 K).map θ = U i ∧ (B23 K).map θ = U j := by
    intro i j hij
    unfold edgeD at hij
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hj' : j.val ≤ m
      · obtain ⟨θ, hθ, h12, h23⟩ := kOmega_exists_theta_simpleRootSL2 (K := K) (n := m + 2)
          (i := i.val) (by omega)
        have hinj : Function.Injective (L.subtype.comp (e.symm.toMonoidHom.comp θ)) :=
          L.subtype_injective.comp (e.symm.injective.comp hθ)
        refine ⟨L.subtype.comp (e.symm.toMonoidHom.comp θ), ?_, ?_, ?_⟩
        · rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
          exact bot_le
        · rw [hUdef, omegaPlusNode_of_le e A B (by omega), UnitaryPilot.modelToG, ← h12,
            Subgroup.map_map, Subgroup.map_map]
          rfl
        · rw [hUdef, omegaPlusNode_of_le e A B hj',
            hfin _ ⟨i.val + 1, by omega⟩ (by simp only; omega),
            UnitaryPilot.modelToG, ← h23, Subgroup.map_map, Subgroup.map_map]
          rfl
      · refine ⟨θA, hθA, ?_, ?_⟩
        · rw [hA12, hUdef, omegaPlusNode_of_le e A B (by omega)]
          exact hfin _ _ (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
        · rw [hA23, hUdef, omegaPlusNode_of_eq_succ e A B (by omega)]
    · refine ⟨θB, hθB, ?_, ?_⟩
      · rw [hB12, hUdef, omegaPlusNode_of_le e A B (by omega)]
        exact hfin _ _ (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
      · rw [hB23, hUdef, omegaPlusNode_of_eq_add_two e A B (by omega)]
  obtain ⟨Ψ, -, hcen, hmodel⟩ := OmegaPilot.exists_weakCT_spinPlus_of_pieces_two_pow
    (n := m + 3) (by omega) (by omega : 1 ≤ f) hKc hK4 U hG₀ hcomm hpair
  have hZ : center (spGlobal e) = ⊥ := by
    rw [hcen, OmegaPilot.center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel

theorem sp2mKindType_omegaPlus_three_of_pieces [Finite G] {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf :
    2 ≤ f)
    (e : L ≃* StatedSp 3 K) (h : SpOmegaPlusPieces (m := 1) e) :
    Sp2mKindType (spGlobal e) 3 f .omegaPlus :=
  sp2mKindType_omegaPlus_of_pieces_of_one_le (m := 1) le_rfl hKc hf e h

end PlusRecognition

section MinusRecognition

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (B12 B23 LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair spinMinusModel)
open CFSG.LieType.Universal.Spin.Twisted (fact_shortField)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {m : ℕ}

theorem sp2mKindType_omegaMinus_of_pieces_of_one_le [CharP K 2] {f : ℕ} (hm : 1 ≤ m)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K)
    (h : SpOmegaMinusPieces e) : Sp2mKindType (spGlobal e) (m + 2) f .omegaMinus := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨hshort, hfar, b, c, hirr, W, hW⟩ := h
  set G₀ := spGlobal e with hG₀def
  set P : Fin (m + 2) → Subgroup G := fun j => pieceCore e ({j} : Finset (Fin (m + 2)))
    with hPdef
  have hPle : ∀ j, P j ≤ G₀ := fun j => le_iSup P j
  have hPmap : ∀ j, ((P j).subgroupOf G₀).map G₀.subtype = P j := fun j => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hPle j)]
  set U : Fin (m + 3 - 1) → Subgroup G₀ := fun k => (P k).subgroupOf G₀ with hUdef
  have hgen : ⨆ k, U k = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUdef, hPmap]
    rfl
  have hcommG : ∀ i j : Fin (m + 2), i.val + 1 < j.val → P i ≤ centralizer (P j : Set G) := by
    intro i j hij
    have hi : i.val + 1 < m + 2 := by have := j.isLt; omega
    rw [hPdef]
    simp only
    rw [hshort i hi]
    by_cases hj : j.val + 1 < m + 2
    · rw [hshort j hj]
      exact UnitaryPilot.modelToG_le_centralizer e
        (kOmega_simpleRootSL2_le_centralizer (by omega))
    · have hjl : j = Fin.last (m + 1) := Fin.ext (by rw [Fin.val_last]; omega)
      rw [hjl]
      exact hfar i (by omega)
  have hcomm : ∀ i j : Fin (m + 3 - 1), i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j,
      u * v = v * u := by
    intro i j hij u hu v hv
    have h1 := mem_centralizer_iff.1 (hcommG i j hij (mem_subgroupOf.1 hu)) (v : G)
      (mem_subgroupOf.1 hv)
    exact Subtype.ext h1.symm
  have hpair : ∀ i j : Fin (m + 3 - 1), i.val + 1 = j.val → j.val + 2 < m + 3 →
      ∃ W, LinearBlockStandardPair K W (U i) (U j) := by
    intro i j hij hj
    obtain ⟨θ, hθ, h12, h23⟩ := kOmega_exists_theta_simpleRootSL2 (K := K) (n := m + 2)
      (i := i.val) (by omega)
    set θG : SL(3, K) →* G := L.subtype.comp (e.symm.toMonoidHom.comp θ) with hθG
    have hinj : Function.Injective θG := L.subtype_injective.comp (e.symm.injective.comp hθ)
    have hθker : θG.ker ≤ center SL(3, K) := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
      exact bot_le
    have hi12 : (B12 K).map θG = P i := by
      rw [hPdef]
      simp only
      rw [hshort i (by omega), UnitaryPilot.modelToG, hθG, ← Subgroup.map_map, ← Subgroup.map_map,
        h12]
      rfl
    have hj23 : (B23 K).map θG = P j := by
      rw [hPdef]
      simp only
      rw [hshort j (by omega), UnitaryPilot.modelToG, hθG, ← Subgroup.map_map, ← Subgroup.map_map,
        h23]
      congr 3
      exact Fin.ext (by simp only; omega)
    have hpairG := kOmega_linearBlockStandardPair_of_theta θG hθker
    rw [hi12, hj23] at hpairG
    have hWle : θG.range ≤ G₀ := by
      rw [kOmega_range_theta_eq_sup, hi12, hj23]
      exact sup_le (hPle i) (hPle j)
    exact ⟨_, CFSG.ClassicalInvolution.Models.SymplecticPairs.linearBlockStandardPair_subgroupOf
      hWle hpairG⟩
  have htw : ∀ i j : Fin (m + 3 - 1), i.val + 3 = m + 3 → j.val + 2 = m + 3 →
      ∃ W, TwistedB2BlockStandardPair hirr W (U i) (U j) := by
    intro i j hi hj
    have hiP : P i = modelToG e (simpleRootSL2 K (Fin.last m).castSucc) := by
      rw [hPdef]
      simp only
      rw [hshort i (by omega)]
      congr 2
      exact Fin.ext (by simp only [Fin.val_castSucc, Fin.val_last]; omega)
    have hjP : P j = pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) := by
      rw [hPdef]
      simp only
      congr 2
      exact Fin.ext (by rw [Fin.val_last]; omega)
    rw [← hiP, ← hjP] at hW
    have hWle : W ≤ G₀ :=
      (kOmega_twistedB2BlockStandardPair_le_sup hW).trans (sup_le (hPle i) (hPle j))
    exact ⟨_, kOmega_twistedB2BlockStandardPair_subgroupOf hWle hW⟩
  have hadm : StatedLieAdmissible .POmegaMinus (m + 3) 2 f := ⟨Nat.prime_two, by omega, by omega⟩
  obtain ⟨Ψ, -, -, -, hcen, hmodel, -⟩ := CFSG.RankThree.PartOne.CTP.weakCT_spinMinus_even
    hadm hKc hK4 hirr U hgen hcomm hpair htw
  have hZ : center G₀ = ⊥ := by
    rw [hcen, CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (by omega) hirr,
      Subgroup.map_bot]
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel

theorem sp2mKindType_omegaMinus_three_of_pieces [CharP K 2] {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf
    : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) (h : SpOmegaMinusPieces (m := 1) e) :
    Sp2mKindType (spGlobal e) 3 f .omegaMinus :=
  sp2mKindType_omegaMinus_of_pieces_of_one_le (m := 1) le_rfl hKc hf e h

end MinusRecognition

section Sign

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def OmegaPlusSignInput (N : ℕ) : Prop :=
  ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2],
    ∃ v : Fin (2 * N) → K', coordinateQuadPlus N K' v = 1 ∧
      ∃ χ : MulAut (matrixProjectiveDerived (coordinateQuadPlus N K')) →* Multiplicative (ZMod 2),
        (∀ x, χ (MulAut.conj x) = 1) ∧ χ (symmetryAut (coordinateQuadPlus N K') v) ≠ 1

end Sign

section Endgame

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem false_of_spOmegaPlusRow_of_global_of_sign (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hD : OmegaPlusSignInput (n + 1)) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t
        = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobal e t f .omegaPlus)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hty' : LieModel (spGlobal e) .POmegaPlus (n + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (spGlobal e)
    .POmegaPlus (Or.inl rfl) (n + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ n + 1 := hn4'
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := (hI K' hK' eE).1
  have hreg := regular_coordinateQuadPlus (K := K') (n := n + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K') (n := n + 1) (by omega)
  obtain ⟨v, hv, χ, hχInn, hχv⟩ := hD K'
  set ε := coordinatePlusWitnessEquiv K' eE with hεdef
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉ inner (matrixProjectiveDerived (coordinateQuadPlus (n + 1) K')) :=
      by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_mulAut_hom ε htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  have h1 : χ (MulAut.congr ε θ) = χ (symmetryAut (coordinateQuadPlus (n + 1) K') v) := by
    rw [hΨ, map_mul, map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  change χ (MulAut.congr ε θ) ≠ 1
  rw [h1]
  exact hχv

omit [Finite K] [CharP K 2] in
theorem false_of_spOmegaMinusRow_of_global_of_three_le (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 3 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobal e t f .omegaMinus)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hty' : LieModel (spGlobal e) .POmegaMinus (n + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (spGlobal e)
    .POmegaMinus (Or.inr rfl) (n + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', b, c, hirr, ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ n + 1 := hn4'
  have h1n : 1 ≤ n + 1 := by omega
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := hI h1n K' hK' b c hirr eE
  have hreg := regular_coordinateQuadMinus (n + 1) K' b c hn4 hirr
  have hE := commutator_coordinateQuadMinus (n + 1) K' b c hn4 hirr
  obtain ⟨v, hv, C, hCcyc, hCInn, hNF, hvC⟩ := omegaMinusOutInput_holds K' (n + 1) hn4 b c hirr
  set ε := coordinateMinusWitnessEquiv K' h1n b c eE with hεdef
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉
      inner (matrixProjectiveDerived (coordinateQuadMinus (n + 1) K' h1n b c)) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have htZ : t ∉ centralizer (spGlobal e : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt (le_spGlobal hK4 (by omega) e) ht
    htN htZ
  have hker : Odd (Nat.card (normalizerMulAut ε).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have : IsCyclic C := hCcyc
  have hout' : normalizerMulAut ε ⟨t, htN⟩ ∉
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus (n + 1) K' h1n b c) →*
        MulAut _).range := hαo
  have hidx := EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut ε)
    hker hCInn hNF (EPilot.exists_normalizerMulAut_eq_conj ε) htN ht hout' huniq ⟨Ψ⁻¹, by
      change Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ ∈ C
      have h1 : Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ =
          symmetryAut (coordinateQuadMinus (n + 1) K' h1n b c) v := by
        rw [hΨ]
        group
      rw [h1]
      exact hvC⟩
  have : IsSimpleGroup G := hset.1
  have htG : t ∉ spGlobal e := EPilot.not_mem_of_normalizerMulAut_not_mem_range ε htN hout'
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG) hidx

end Endgame

section Rows

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem false_of_sp2mKindType_omegaPlus_three (hD : OmegaPlusSignInput 4)
    (hset : SeitzSetting G L) {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hty : Sp2mKindType (spGlobal e) 3 f .omegaPlus)
    (huniq : SpOmegaRowGlobal e t f .omegaPlus → ∀ g : G,
      g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) → g ∈ normalizer (spGlobal e : Set G)) :
    False := by
  have hglob := spOmegaRowGlobal_of_sp2mKindType hset le_rfl hKc hf e ht hKt (Or.inl rfl) hty
  exact false_of_spOmegaPlusRow_of_global_of_sign hset le_rfl hD e ht hKt hglob (huniq hglob)

theorem false_of_sp2mKindType_omegaMinus_three (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hty : Sp2mKindType (spGlobal e) 3 f .omegaMinus)
    (huniq : SpOmegaRowGlobal e t f .omegaMinus → ∀ g : G,
      g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) → g ∈ normalizer (spGlobal e : Set G)) :
    False := by
  have hglob := spOmegaRowGlobal_of_sp2mKindType hset le_rfl hKc hf e ht hKt (Or.inr rfl) hty
  exact false_of_spOmegaMinusRow_of_global_of_three_le hset le_rfl hKc hf e ht hKt hglob
    (huniq hglob)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
