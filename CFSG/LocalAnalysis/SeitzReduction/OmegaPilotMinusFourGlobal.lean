module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommFork
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGlobal

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

section Fork

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem center_forkBlock_two (hF : 4 ≤ Nat.card F) (P : Finset (Fin (2 + 1))) :
    center (forkBlock F 2 P) = ⊥ := by
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := F) hF
  have : IsSimpleGroup (forkBlock F 2 P) :=
    (forkBlockEquiv (F := F) 2 (by omega) P).symm.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (forkBlock F 2 P)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : forkBlock F 2 P, x * y = y * x := fun x y =>
      (mem_center_iff.1 (h ▸ Subgroup.mem_top (G := forkBlock F 2 P) y) x)
    have hperf : ⁅(⊤ : Subgroup (forkBlock F 2 P)), (⊤ : Subgroup (forkBlock F 2 P))⁆ =
        (⊤ : Subgroup (forkBlock F 2 P)) := by
      have h1 := commutator_subgroupOf_eq_of_le_perfect (le_refl (forkBlock F 2 P))
        (commutator_forkBlock hF (by omega) P)
      rwa [Subgroup.subgroupOf_self] at h1
    have hbot : ⁅(⊤ : Subgroup (forkBlock F 2 P)), (⊤ : Subgroup (forkBlock F 2 P))⁆ =
        (⊥ : Subgroup (forkBlock F 2 P)) := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x _ y _
      rw [commutatorElement_def, hcomm x y, mul_inv_cancel_right, mul_inv_cancel,
        Subgroup.mem_bot]
    have htriv : (⊤ : Subgroup (forkBlock F 2 P)) = ⊥ := hperf.symm.trans hbot
    have : Nontrivial (forkBlock F 2 P) := IsSimpleGroup.toNontrivial
    exact (bot_ne_top (α := Subgroup (forkBlock F 2 P))) htriv.symm

theorem card_forkBlock_sup (hF : 4 ≤ Nat.card F) :
    Nat.card (forkBlock F 2 ∅ ⊔ forkBlock F 2 {Fin.last 2} :
        Subgroup (GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F)) = Nat.card (SL(2, F) × SL(2, F)) := by
  set A := forkBlock F 2 (∅ : Finset (Fin (2 + 1))) with hA
  set B := forkBlock F 2 ({Fin.last 2} : Finset (Fin (2 + 1))) with hB
  have hPB : consecutiveBlock (2 + 1) (2 - 1) 2 ∩ {Fin.last 2} = {Fin.last 2} := by decide
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y := by
    intro x hx y hy
    rw [hA, forkBlock, map_conj_flipGL_empty] at hx
    rw [hB, forkBlock] at hy
    exact commute_siegelBlockGL_flip hF (card_consecutiveBlock_two (by omega)) hPB hx hy
  have hdisj : Disjoint A B := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.1⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y y.2 x hx.2).eq
    rw [center_forkBlock_two hF ∅, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hcomm' : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm' with hφ
  have hinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective _ _ _).2 ⟨A.subtype_injective, B.subtype_injective,
      by rw [range_subtype, range_subtype]; exact hdisj⟩
  have hrange : φ.range = A ⊔ B := by
    rw [hφ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (((forkBlockEquiv (F := F) 2 (by omega) ∅).prodCongr
    (forkBlockEquiv (F := F) 2 (by omega) {Fin.last 2})).symm.toEquiv)

end Fork

section Nodes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {hn : 1 ≤ 2 + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn b c)} {ι : K →+* F}

theorem minusPieceCore_le_sup_minusNode_four [CharP F 2] (C₀ : MinusFieldCover e ι 0)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) :
    minusPieceCore e {Fin.last 2} ≤ minusNode C₀ 2 ⊔ minusNode C₀ 3 := by
  set E := minusNeighbourCore e (0 : Fin (2 + 1)) with hE
  set M := minusPieceCore e {Fin.last 2} with hM
  have h0 : (0 : Fin (2 + 1)) ∉ ({Fin.last 2} : Finset (Fin (2 + 1))) := by decide
  have hME : M ≤ E := minusPieceCore_le_minusNeighbourCore e h0
  have hU2 : minusNode C₀ 2 = C₀.lift (forkBlock F 2 ∅) := minusNode_of_eq C₀ (j := 2) rfl
  have hU3 : minusNode C₀ 3 = C₀.lift (forkBlock F 2 {Fin.last 2}) :=
    minusNode_of_eq_succ C₀ (j := 3) rfl
  have hU2E : minusNode C₀ 2 ≤ E := hU2 ▸ C₀.lift_le _
  have hU3E : minusNode C₀ 3 ≤ E := hU3 ▸ C₀.lift_le _
  set π' := (StatedOmega (StatedQuadPlus (2 + 1) F)).subtype.comp C₀.π with hπ'
  have hker : π'.ker ≤ center E := C₀.ker_comp_subtype_le
  have hmap : ∀ A : Subgroup G, (A.subgroupOf E).map π' =
      ((A.subgroupOf E).map C₀.π).map (StatedOmega (StatedQuadPlus (2 + 1) F)).subtype :=
    fun A => by rw [hπ', ← Subgroup.map_map]
  have hA : ((minusNode C₀ 2).subgroupOf E).map π' = forkBlock F 2 ∅ := by
    rw [hmap, hU2]
    exact C₀.map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
      (commutator_forkBlock hF (by omega) ∅)
  have hB : ((minusNode C₀ 3).subgroupOf E).map π' = forkBlock F 2 {Fin.last 2} := by
    rw [hmap, hU3]
    exact C₀.map_lift (forkBlock_le_statedOmega hF (by omega) _)
      (commutator_forkBlock hF (by omega) _)
  have hMimg := C₀.map_pieceCore hK hF h0 (Finset.singleton_nonempty _)
  rw [insert_castSuccPlanes_preimagePlanes_zero_last (r := 2) (by omega)] at hMimg
  have hcardM : Nat.card ((M.subgroupOf E).map π') = Nat.card (SL(2, F) × SL(2, F)) := by
    rw [hmap, hMimg]
    obtain ⟨φ⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card F hF
    have hc : (consecutiveBlock (2 + 1) (2 - 1) 2).card = 2 := card_consecutiveBlock_two (by omega)
    rw [Nat.card_congr ((StatedOmega (StatedQuadPlus
      (consecutiveBlock (2 + 1) (2 - 1) 2).card F)).equivMapOfInjective _
        (spEmbedGL_injective (SymplecticPilot.planeEnum_injective _))).symm.toEquiv]
    have e2 : StatedOmega (StatedQuadPlus (consecutiveBlock (2 + 1) (2 - 1) 2).card F) ≃*
        StatedOmega (StatedQuadPlus 2 F) := by rw [hc]
    exact Nat.card_congr (e2.trans φ).toEquiv
  have hAM : forkBlock F 2 ∅ ⊔ forkBlock F 2 {Fin.last 2} ≤ (M.subgroupOf E).map π' := by
    rw [← hA, ← hB]
    refine sup_le (Subgroup.map_mono fun x hx => ?_) (Subgroup.map_mono fun x hx => ?_)
    · rw [mem_subgroupOf] at hx ⊢
      exact (hU2 ▸ lift_forkBlock_le_minusPieceCore C₀ hF (by omega) (Finset.empty_subset _)) hx
    · rw [mem_subgroupOf] at hx ⊢
      exact (hU3 ▸ lift_forkBlock_le_minusPieceCore C₀ hF (by omega) le_rfl) hx
  have heq : forkBlock F 2 ∅ ⊔ forkBlock F 2 {Fin.last 2} = (M.subgroupOf E).map π' :=
    Subgroup.eq_of_le_of_card_ge hAM (by rw [hcardM, card_forkBlock_sup hF])
  have hMp : ⁅M.subgroupOf E, M.subgroupOf E⁆ = M.subgroupOf E :=
    commutator_subgroupOf_eq_of_le_perfect hME (commutator_centralizerPerfectCore _)
  have hUp : ⁅minusNode C₀ 2 ⊔ minusNode C₀ 3, minusNode C₀ 2 ⊔ minusNode C₀ 3⁆ =
      minusNode C₀ 2 ⊔ minusNode C₀ 3 := by
    have h := commutator_iSup_of_perfect (A := fun i : Bool =>
      cond i (minusNode C₀ 2) (minusNode C₀ 3)) (fun i => by
        cases i
        · exact commutator_minusNode C₀ 3
        · exact commutator_minusNode C₀ 2)
    rwa [iSup_bool_eq] at h
  have hUp' := commutator_subgroupOf_eq_of_le_perfect (sup_le hU2E hU3E) hUp
  have hle := le_of_map_le_of_perfect hker hMp hUp' (by
    rw [Subgroup.subgroupOf_sup hU2E hU3E, Subgroup.map_sup, hA, hB, heq])
  intro x hx
  exact hle (show (⟨x, hME hx⟩ : E) ∈ M.subgroupOf E from hx)

theorem minusNode_le_minusPieceCore_of_le_four (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F)
    {j : Fin (2 + 2)} (hj : 2 ≤ j.val) : minusNode C₀ j ≤ minusPieceCore e {Fin.last 2} := by
  rcases (show j.val = 2 ∨ j.val = 3 by omega) with h | h
  · rw [minusNode_of_eq _ h]
    exact lift_forkBlock_le_minusPieceCore C₀ hF (by omega) (Finset.empty_subset _)
  · rw [minusNode_of_eq_succ _ h]
    exact lift_forkBlock_le_minusPieceCore C₀ hF (by omega) le_rfl

theorem exists_theta_minusNode_fork_four (C₀ : MinusFieldCover e ι 0) (hK : 4 ≤ Nat.card K)
    (hF : 5 ≤ Nat.card F) {j : Fin (2 + 2)} (hj : j = 2 ∨ j = 3) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ 1 ∧
      (B23 F).map θ = minusNode C₀ j := by
  have hF4 : 4 ≤ Nat.card F := by omega
  have h0 : (0 : Fin (2 + 1)) ∉ consecutiveBlock (2 + 1) 1 2 := by decide
  rw [minusNode_of_le C₀ (j := 1) (by simp)]
  have hU := C₀.map_levelCore hK hF4 h0 (card_consecutiveBlock_two (by omega)).ge
  rw [castSuccPlanes_preimagePlanes_zero (r := 2) (j := 1) le_rfl (by omega)] at hU
  rw [show (consecutiveBlock (2 + 1) ((1 : Fin (2 + 2)).val) 2) = consecutiveBlock (2 + 1) 1 2
    from rfl]
  rcases hj with rfl | rfl
  · rw [minusNode_of_eq C₀ (j := 2) rfl]
    have hV := C₀.map_lift (forkBlock_le_statedOmega hF4 (by omega) ∅)
      (commutator_forkBlock hF4 (by omega) ∅)
    refine C₀.exists_theta_of_images hF (minusLevelCore_le_minusNeighbourCore e h0)
      (C₀.lift_le _) (commutator_centralizerPerfectCore _) (C₀.commutator_lift _)
      (a := 0) (by omega) ∅ ?_ ?_
    · rw [hU, map_conj_flipGL_empty]
    · rw [hV, forkBlock]
  · rw [minusNode_of_eq_succ C₀ (j := 3) rfl]
    have hV := C₀.map_lift (forkBlock_le_statedOmega hF4 (by omega) {Fin.last 2})
      (commutator_forkBlock hF4 (by omega) {Fin.last 2})
    have hdisj : Disjoint (consecutiveBlock (2 + 1) 0 2) {Fin.last 2} := by decide
    refine C₀.exists_theta_of_images hF (minusLevelCore_le_minusNeighbourCore e h0)
      (C₀.lift_le _) (commutator_centralizerPerfectCore _) (C₀.commutator_lift _)
      (a := 0) (by omega) {Fin.last 2} ?_ ?_
    · rw [hU, map_flipGL_siegelBlockGL_of_disjoint hdisj]
    · rw [hV, forkBlock]

end Nodes

section Global

open CFSG.LieType CFSG.LieType.Universal
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (minusIndexEquiv
  regular_coordinateQuadMinus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {hn : 1 ≤ 2 + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn b c)} {ι : K →+* F}

omit [CharP F 2] in
theorem exists_theta_minusNode_four (C₀ : MinusFieldCover e ι 0) (hK : 4 ≤ Nat.card K)
    (hF : 5 ≤ Nat.card F)
    (h01 : ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ 0 ∧
      (B23 F).map θ = minusNode C₀ 1) {i j : Fin (2 + 2)} (hij : edgeD (2 + 2) i j) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ i ∧
      (B23 F).map θ = minusNode C₀ j := by
  have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ (j = 2 ∨ j = 3)) := by
    revert hij
    fin_cases i <;> fin_cases j <;> decide
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, hj⟩
  · exact h01
  · exact exists_theta_minusNode_fork_four C₀ hK hF hj

theorem exists_weakCT_minus_four {f : ℕ} (hKf : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hF : Nat.card F = 2 ^ (2 * f)) (C₀ : MinusFieldCover e ι 0) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ j, minusNode C₀ j)
    (hcomm : ∀ i j : Fin (2 + 2), i ≠ j → ¬ edgeD (2 + 2) i j → ¬ edgeD (2 + 2) j i →
      minusNode C₀ i ≤ centralizer (minusNode C₀ j : Set G))
    (h01 : ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = minusNode C₀ 0 ∧
      (B23 F).map θ = minusNode C₀ 1) {t : G} (htC : t ∈ centralizer (L : Set G)) :
    (∃ Ψ : spinGroup (Spin.quadPlus (2 + 2) F) →* G₀, Function.Surjective Ψ ∧
        Ψ.ker ≤ center (spinGroup (Spin.quadPlus (2 + 2) F))) ∧
      CFSG.IsQuasisimple G₀ ∧ center G₀ = ⊥ ∧ LieModel G₀ .POmegaPlus (2 + 2) 2 (2 * f) ∧
      minusPieceCore e {Fin.last 2} ≤ G₀ ∧ t ∈ normalizer (G₀ : Set G) := by
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF4 : 4 ≤ Nat.card F := by omega
  have hpair := fun (i j : Fin (2 + 2)) (hij : edgeD (2 + 2) i j) =>
    exists_theta_minusNode_four C₀ hq (by omega) h01 hij
  obtain ⟨Ψ, hΨs, hΨk, hG₀q, -, -⟩ := exists_weakCT_spinPlus_of_pieces (n := 2 + 2) (by omega)
    (by omega) (by omega : 1 ≤ f) hF (minusNode C₀) hG₀ hcomm hpair
  obtain ⟨Ψ', -, hcen, hmodel⟩ := exists_weakCT_spinPlus_of_pieces_two_pow (n := 2 + 2)
    (by omega) (by omega : 1 ≤ 2 * f) hF hF4 (minusNode C₀) hG₀ hcomm hpair
  have hZ : center G₀ = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  have hG₀L : LieModel G₀ .POmegaPlus (2 + 2) 2 (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  have hD : minusPieceCore e {Fin.last 2} ≤ G₀ := by
    refine (minusPieceCore_le_sup_minusNode_four C₀ hq hF4).trans ?_
    rw [hG₀]
    exact sup_le (le_iSup (minusNode C₀) 2) (le_iSup (minusNode C₀) 3)
  have hconj : ∀ x ∈ centralizer (L : Set G), ∀ g ∈ G₀, x * g * x⁻¹ ∈ G₀ := by
    intro x hx g hg
    rw [hG₀] at hg
    refine Subgroup.iSup_induction (minusNode C₀) (C := fun g => x * g * x⁻¹ ∈ G₀) hg ?_ ?_ ?_
    · intro j y hy
      by_cases hj : j.val + 1 ≤ 2
      · rw [minusNode_of_le _ hj] at hy
        have h1 := (mem_normalizer_iff.1
          (UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e hx
            (minusLevelTorus hn b c (consecutiveBlock (2 + 1) j.val 2))) y).1 hy
        rw [hG₀]
        exact le_iSup (minusNode C₀) j (by rw [minusNode_of_le _ hj]; exact h1)
      · have hyD := minusNode_le_minusPieceCore_of_le_four C₀ hF4 (by omega) hy
        exact hD ((mem_normalizer_iff.1 (mem_normalizer_minusPieceCore e hx _) y).1 hyD)
    · simp only [mul_one, mul_inv_cancel]
      exact one_mem _
    · intro y z hy hz
      have h1 : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
      rw [h1]
      exact mul_mem hy hz
  have htN : t ∈ normalizer (G₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj t htC g hg, fun hg => ?_⟩
    have h1 := hconj t⁻¹ (inv_mem htC) _ hg
    have h2 : t⁻¹ * (t * g * t⁻¹) * t⁻¹⁻¹ = g := by group
    rwa [h2] at h1
  exact ⟨⟨Ψ, hΨs, hΨk⟩, hG₀q, hZ, hG₀L, hD, htN⟩

theorem le_iSup_minusNode_four (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (C₀ : MinusFieldCover e ι 0) (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) :
    L ≤ ⨆ j, minusNode C₀ j := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus (2 + 2) K b c (by omega) hirr
  have h := isHypFrame_minus K hn b c
  set Y₀₁ := frameLeviProj (coordinateQuadMinus (2 + 2) K hn b c) (minusFrameLeft hn)
    (minusFrameRight hn) 0 1 with hY₀₁
  set Y₁₂ := frameLeviProj (coordinateQuadMinus (2 + 2) K hn b c) (minusFrameLeft hn)
    (minusFrameRight hn) 1 2 with hY₁₂
  set R := stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
    (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
    (minusIndexEquiv (2 + 2) hn (.inl 1)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 1))) with hR
  have htop : Y₀₁ ⊔ Y₁₂ ⊔ R = ⊤ :=
    eq_top_of_frameLeviProj_le_four hirr (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_left) le_sup_right
  have hnode : ∀ j : Fin (2 + 2), j.val + 1 ≤ 2 →
      minusLevelCore e (consecutiveBlock (2 + 1) j.val 2) ≤ ⨆ j, minusNode C₀ j := fun j hj => by
    rw [← minusNode_of_le C₀ hj]
    exact le_iSup (minusNode C₀) j
  have h0 : (0 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) 0 2 := by decide
  have h1 : (1 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) 0 2 := by decide
  have h1' : (1 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) 1 2 := by decide
  have h2' : (2 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) 1 2 := by decide
  have hU₀ : modelToG e Y₀₁ ≤ ⨆ j, minusNode C₀ j :=
    (UnitaryPilot.modelToG_le_centralizerPerfectCore e (h.frameLeviProj_le_centralizer h0 h1)
      (h.commutator_frameLeviProj (by decide) hK hQ hT)).trans (hnode 0 (by simp))
  have hU₁ : modelToG e Y₁₂ ≤ ⨆ j, minusNode C₀ j :=
    (UnitaryPilot.modelToG_le_centralizerPerfectCore e (h.frameLeviProj_le_centralizer h1' h2')
      (h.commutator_frameLeviProj (by decide) hK hQ hT)).trans (hnode 1 (by simp))
  have hRq := (isQuasisimple_minusStabPairsBar_of_four_le (n := 2 + 2) le_rfl hirr
    (i := 0) (j := 1) (by decide)).1
  have hRM : modelToG e R ≤ minusPieceCore e {Fin.last 2} := by
    have h01c : (({0, 1} : Finset (Fin (2 + 2 - 1)))ᶜ) = {Fin.last 2} := by decide
    have hc := modelToG_stabPairsBar_le_minusPieceCore hn e (i := 0) (j := 1) (by decide)
      (Subgroup.isPerfect_iff.mp hRq.1)
    rwa [h01c] at hc
  have hU₂₃ : modelToG e R ≤ ⨆ j, minusNode C₀ j :=
    (hRM.trans (minusPieceCore_le_sup_minusNode_four C₀ hK hF)).trans
      (sup_le (le_iSup (minusNode C₀) 2) (le_iSup (minusNode C₀) 3))
  have hL : modelToG e Y₀₁ ⊔ modelToG e Y₁₂ ⊔ modelToG e R = L := by
    rw [← UnitaryPilot.modelToG_sup, ← UnitaryPilot.modelToG_sup, htop, UnitaryPilot.modelToG_top]
  calc L = modelToG e Y₀₁ ⊔ modelToG e Y₁₂ ⊔ modelToG e R := hL.symm
    _ ≤ ⨆ j, minusNode C₀ j := sup_le (sup_le hU₀ hU₁) hU₂₃

end Global

end CFSG.SeitzReduction.OmegaPilot
