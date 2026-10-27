module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmegaMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogStandard

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Block

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isQuasisimple_blockSpecialLinear_of_card_two {n : ℕ} {I : Finset (Fin n)}
    (hI : I.card = 2) (hF : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple (blockSpecialLinear (K := F) I) := by
  have hs := LinearPilot.isSimpleGroup_blockSpecialLinear_of_card_two hI hF
  have hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear (K := F) I :=
    LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hI.ge hF
  have htop : commutator (blockSpecialLinear (K := F) I) = ⊤ :=
    (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  refine ⟨htop, ?_⟩
  have := hs
  have hc : center (blockSpecialLinear (K := F) I) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (blockSpecialLinear (K := F) I)) with
      h | h
    · exact h
    · exfalso
      have hab : commutator (blockSpecialLinear (K := F) I) = ⊥ := by
        rw [commutator_def, commutator_eq_bot_iff_le_centralizer, ← h]
        exact center_le_centralizer _
      have hnt : Nontrivial (blockSpecialLinear (K := F) I) := hs.toNontrivial
      exact bot_ne_top (htop.symm.trans hab).symm
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

end Block

section Ident

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def neighbourBlock (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k)
    (I : Finset (Fin (2 * 2))) : Subgroup G :=
  (blockSpecialLinear (K := F) I).map ((neighbourCore e k).subtype.comp Φ.toMonoidHom)

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem neighbourBlock_le_centralizer (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k)
    {I I' : Finset (Fin (2 * 2))} (h : Disjoint I I') :
    neighbourBlock e Φ I' ≤ centralizer (neighbourBlock e Φ I : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (LinearPilot.commute_blockSpecialLinear_of_disjoint h hy hx).eq

omit [Finite G] [Finite K] [CharP K 2] [Finite F] [CharP F 2] in
theorem neighbourBlock_sup_eq (e : L ≃* StatedSp 3 K) {k : Fin 3}
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k)
    (I I' : Finset (Fin (2 * 2))) :
    neighbourBlock e Φ I ⊔ neighbourBlock e Φ I' =
      ((blockSpecialLinear (K := F) I ⊔ blockSpecialLinear (K := F) I').map Φ.toMonoidHom).map
        (neighbourCore e k).subtype := by
  rw [neighbourBlock, neighbourBlock, ← Subgroup.map_sup, Subgroup.map_map]

theorem fstS_sndS_eq_blocks (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (σ : K ≃+* F) (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G))
    (S : SiegelSwapParam e t) :
    (S.fstS (simpleRootSL2 K 1) = neighbourBlock e Φ (twBlockSL 0) ∧
        S.sndS (simpleRootSL2 K 1) = neighbourBlock e Φ (twBlockSL 0)ᶜ) ∨
      (S.fstS (simpleRootSL2 K 1) = neighbourBlock e Φ (twBlockSL 0)ᶜ ∧
        S.sndS (simpleRootSL2 K 1) = neighbourBlock e Φ (twBlockSL 0)) := by
  have hF : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  set A := neighbourBlock e Φ (twBlockSL 0) with hA
  set B := neighbourBlock e Φ (twBlockSL 0)ᶜ with hB
  have hM1 : pieceCore e ({1} : Finset (Fin 3)) = A ⊔ B := by
    rw [hA, hB, neighbourBlock_sup_eq, pieceCore_one_eq_of_standard hK e σ Φ hN1]
  have hM2 := S.pieceCore_eq_fstS_sup_sndS hK (j := 1) (by decide)
  have hnA := UnitaryPilot.dichotomy_map_of_isQuasisimple
    (isQuasisimple_blockSpecialLinear_of_card_two (card_twBlockSL 0) hF)
    ((neighbourCore e 0).subtype.comp Φ.toMonoidHom)
  have hnB := UnitaryPilot.dichotomy_map_of_isQuasisimple
    (isQuasisimple_blockSpecialLinear_of_card_two (card_compl_twBlockSL 0) hF)
    ((neighbourCore e 0).subtype.comp Φ.toMonoidHom)
  have hBA : B ≤ centralizer (A : Set G) := neighbourBlock_le_centralizer e Φ disjoint_compl_right
  have hqS := isQuasisimple_simpleRootSL2_subgroupOf hK
    (simpleRootSL2_le_siegelLevi (F := K) (j := (1 : Fin 3)) (by decide))
  obtain ⟨hperf₁, hbot₁, hnN₁⟩ := S.fstS_props hqS
  obtain ⟨hperf₂, hbot₂, hnN₂⟩ := S.flip.fstS_props hqS
  rw [S.flip_fstS] at hperf₂ hbot₂ hnN₂
  have hc₁₂ := S.sndS_le_centralizer_fstS (simpleRootSL2 K 1) (simpleRootSL2 K 1)
  have hc₂₁ : S.fstS (simpleRootSL2 K 1) ≤ centralizer (S.sndS (simpleRootSL2 K 1) : Set G) :=
    le_centralizer_iff.1 hc₁₂
  have h1 := F4Pilot.eq_or_eq_of_perfect_of_le_sup hBA hnA hnB hperf₁ hbot₁ hnN₁
    (by rw [← hM1, hM2]; exact le_sup_left)
    (by rw [← hM1, hM2]
        exact sup_le le_normalizer (hc₁₂.trans (centralizer_le_normalizer _)))
  have h2 := F4Pilot.eq_or_eq_of_perfect_of_le_sup hBA hnA hnB hperf₂ hbot₂ hnN₂
    (by rw [← hM1, hM2]; exact le_sup_right)
    (by rw [← hM1, hM2]
        exact sup_le (hc₂₁.trans (centralizer_le_normalizer _)) le_normalizer)
  have hne : S.fstS (simpleRootSL2 K 1) ≠ S.sndS (simpleRootSL2 K 1) := by
    intro h
    have hab : S.fstS (simpleRootSL2 K 1) ≤ centralizer (S.fstS (simpleRootSL2 K 1) : Set G) := by
      calc S.fstS (simpleRootSL2 K 1) = S.sndS (simpleRootSL2 K 1) := h
        _ ≤ centralizer (S.fstS (simpleRootSL2 K 1) : Set G) := hc₁₂
    exact hbot₁ (by rw [← hperf₁, commutator_eq_bot_iff_le_centralizer.2 hab])
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Ident

section Pairs

theorem linearBlockStandardPair_range_of_map {X : Type} [Group X] {F : Type} [Field F]
    {θ : SL(3, F) →* X} (hker : θ.ker ≤ center SL(3, F)) {U V : Subgroup X}
    (hU : (B12 F).map θ = U) (hV : (B23 F).map θ = V) :
    LinearBlockStandardPair F θ.range U V := by
  have h1 : ∀ H : Subgroup SL(3, F), H.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = H :=
    fun H => by ext x; simp
  exact ⟨θ, 1, rfl, hker, Or.inl ⟨by rw [h1, hU], by rw [h1, hV]⟩⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite K] [CharP K 2] in
theorem pieceCore_two_eq_neighbourBlock (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) = neighbourBlock e Φ (offPlaneSL 0) := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  rw [neighbourBlock, ← Subgroup.map_map]
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ (MonoidHom.id _) Φ hN1
    (rootTorusSp K 0) leviTorusSp_two_le_sup map_rootTorusSp_zero_le_leviTorusSp_two
    (by rw [map_std_rootTorusSp_zero_eq]; exact perfectCore_centralizer_stdTorusSL hF4 0)

omit [CharP K 2] in
theorem exists_pair_offPlane_twBlock (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0) :
    ∃ W, LinearBlockStandardPair K W (neighbourBlock e Φ (offPlaneSL 0))
      (neighbourBlock e Φ (twBlockSL 0)) := by
  obtain ⟨θ, hker, h1, h2⟩ := exists_theta_of_reindex σ
    ((neighbourCore e 0).subtype.comp Φ.toMonoidHom)
    ((neighbourCore e 0).subtype_injective.comp Φ.injective) epsA epsA_block_zero epsA_block_one
  exact ⟨θ.range, linearBlockStandardPair_range_of_map hker h1 h2⟩

omit [CharP K 2] in
theorem exists_pair_offPlane_twBlock_compl (e : L ≃* StatedSp 3 K) (σ : K ≃+* F)
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0) :
    ∃ W, LinearBlockStandardPair K W (neighbourBlock e Φ (offPlaneSL 0))
      (neighbourBlock e Φ (twBlockSL 0)ᶜ) := by
  obtain ⟨θ, hker, h1, h2⟩ := exists_theta_of_reindex σ
    ((neighbourCore e 0).subtype.comp Φ.toMonoidHom)
    ((neighbourCore e 0).subtype_injective.comp Φ.injective) epsB epsB_block_zero epsB_block_one
  exact ⟨θ.range, linearBlockStandardPair_range_of_map hker h1 h2⟩

end Pairs

section SiegelPairs

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  {e : L ≃* StatedSp 3 K} {t : G}

theorem map_range_blockSL_siegelLeviEquiv {j : Fin 3} (h : j.val + 1 < 3) {i : ℕ}
    (hi : i + 2 ≤ 3) (hI : LinearPilot.consecutiveBlock 3 i 2 = {j, ⟨j.val + 1, h⟩}) :
    ((CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 i hi).range).map
        (siegelLeviEquiv (K := K) (n := 3)).toMonoidHom =
      (simpleRootSL2 K j).subgroupOf (siegelLevi K 3) := by
  rw [LinearPilot.range_blockSL_eq hi, hI, ← siegelBlock_pair_eq_simpleRootSL2' h]
  ext x
  rw [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, (coe_siegelLeviEquiv_apply A).symm⟩
  · rintro ⟨A, hA, hAx⟩
    exact ⟨A, hA, Subtype.ext ((coe_siegelLeviEquiv_apply A).trans hAx)⟩

theorem SiegelSwapParam.exists_pair_fstS (S : SiegelSwapParam e t) :
    ∃ W, LinearBlockStandardPair K W (S.fstS (simpleRootSL2 K 0))
      (S.fstS (simpleRootSL2 K 1)) := by
  set θ : SL(3, K) →* G := (S.Ψ.comp (MonoidHom.inl _ _)).comp
    (siegelLeviEquiv (K := K) (n := 3)).toMonoidHom with hθ
  have hker : θ.ker ≤ center SL(3, K) := by
    intro x hx
    have hz := S.ker_comp_inl_le_center
      (show siegelLeviEquiv x ∈ (S.Ψ.comp (MonoidHom.inl _ _)).ker from hx)
    refine mem_center_iff.2 fun g => (siegelLeviEquiv (K := K) (n := 3)).injective ?_
    rw [map_mul, map_mul]
    exact mem_center_iff.1 hz (siegelLeviEquiv g)
  have hB : ∀ (H : Subgroup SL(3, K)) (J : Subgroup (StatedSp 3 K)),
      H.map (siegelLeviEquiv (K := K) (n := 3)).toMonoidHom = J.subgroupOf (siegelLevi K 3) →
        H.map θ = S.fstS J := by
    intro H J hHJ
    rw [SiegelSwapParam.fstS, ← hHJ, Subgroup.map_map]
  exact ⟨θ.range, linearBlockStandardPair_range_of_map hker
    (hB _ _ (map_range_blockSL_siegelLeviEquiv (j := 0) (by decide) (by omega) (by decide)))
    (hB _ _ (map_range_blockSL_siegelLeviEquiv (j := 1) (by decide) (by omega) (by decide)))⟩

theorem SiegelSwapParam.exists_pair_sndS (S : SiegelSwapParam e t) :
    ∃ W, LinearBlockStandardPair K W (S.sndS (simpleRootSL2 K 0))
      (S.sndS (simpleRootSL2 K 1)) := by
  have h := S.flip.exists_pair_fstS
  rwa [S.flip_fstS, S.flip_fstS] at h

end SiegelPairs

end CFSG.SeitzReduction.SymplecticPilot
