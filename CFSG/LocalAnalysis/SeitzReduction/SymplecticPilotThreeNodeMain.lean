module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNodePairs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNodeSiegel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG OddCentralSplit)
open scoped MatrixGroups

section Orth

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {e : L ≃* StatedSp 3 K}
  {t : G}

variable (K) in
@[expose] noncomputable def siegelRootHomZero : SL(2, K) →* siegelLevi K 3 :=
  (simpleRootHom K (0 : Fin 3)).codRestrict (siegelLevi K 3)
    (simpleRootHom_mem_siegelLevi (j := (0 : Fin 3)) (by decide))

@[expose] noncomputable def SiegelSwapParam.rootSwapHom (S : SiegelSwapParam e t) :
    SL(2, K) × SL(2, K) →* G :=
  S.Ψ.comp (MonoidHom.prodMap (siegelRootHomZero K) (siegelRootHomZero K))

theorem SiegelSwapParam.rootSwapHom_apply (S : SiegelSwapParam e t) (p : SL(2, K) × SL(2, K)) :
    S.rootSwapHom p = S.Ψ (siegelRootHomZero K p.1, siegelRootHomZero K p.2) :=
  rfl

theorem SiegelSwapParam.rootSwapHom_diag (S : SiegelSwapParam e t) (A : SL(2, K)) :
    S.rootSwapHom (A, A) = ((e.symm (simpleRootHom K (0 : Fin 3) A) : L) : G) :=
  S.diag _

theorem SiegelSwapParam.conj_rootSwapHom (S : SiegelSwapParam e t) (p : SL(2, K) × SL(2, K)) :
    t * S.rootSwapHom p * t⁻¹ = S.rootSwapHom p.swap :=
  S.swap _ _

theorem SiegelSwapParam.fstS_zero_le_range_rootSwapHom (S : SiegelSwapParam e t) :
    S.fstS (simpleRootSL2 K (0 : Fin 3)) ≤ S.rootSwapHom.range := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx
  refine ⟨(A, 1), ?_⟩
  rw [S.rootSwapHom_apply, map_one]
  exact congrArg S.Ψ (Prod.ext (Subtype.ext hA) rfl)

theorem SiegelSwapParam.sndS_zero_le_range_rootSwapHom (S : SiegelSwapParam e t) :
    S.sndS (simpleRootSL2 K (0 : Fin 3)) ≤ S.rootSwapHom.range := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx
  refine ⟨(1, A), ?_⟩
  rw [S.rootSwapHom_apply, map_one]
  exact congrArg S.Ψ (Prod.ext rfl (Subtype.ext hA))

theorem SiegelSwapParam.range_rootSwapHom [Finite G] [Finite K] (S : SiegelSwapParam e t)
    (hK : 4 ≤ Nat.card K) : S.rootSwapHom.range = pieceCore e ({0} : Finset (Fin 3)) := by
  rw [S.pieceCore_eq_fstS_sup_sndS hK (j := 0) (by decide)]
  refine le_antisymm ?_ (sup_le S.fstS_zero_le_range_rootSwapHom
    S.sndS_zero_le_range_rootSwapHom)
  rintro _ ⟨⟨A, B⟩, rfl⟩
  have h : S.rootSwapHom (A, B) =
      S.Ψ (siegelRootHomZero K A, 1) * S.Ψ (1, siegelRootHomZero K B) := by
    rw [S.rootSwapHom_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [h]
  exact mul_mem (mem_sup_left ⟨siegelRootHomZero K A, mem_subgroupOf.2 ⟨A, rfl⟩, rfl⟩)
    (mem_sup_right ⟨siegelRootHomZero K B, mem_subgroupOf.2 ⟨B, rfl⟩, rfl⟩)

theorem SiegelSwapParam.pieceCore_zero_le_centralizer_longRootSp2_two [Finite G] [Finite K]
    [CharP K 2] (hset : SeitzSetting G L) (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (S : SiegelSwapParam e t) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (modelToG e (longRootSp2 K 3 (2 : Fin 3)) : Set G) := by
  rw [← S.range_rootSwapHom hK]
  exact range_le_centralizer_longRootSp2_two_of_swap hset hK e htC ht
    (S.range_rootSwapHom hK).le S.rootSwapHom_diag S.conj_rootSwapHom

end Orth

section Nodes

theorem nodeFive_lt_cases : ∀ i j : Fin 5, (i : ℕ) + 1 < j →
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨
      (i = 2 ∧ j = 4) := by
  decide

theorem nodeFive_succ_cases : ∀ i j : Fin 5, (j : ℕ) = i + 1 →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 4) := by
  decide

theorem nodeFive_fold_cases : ∀ (j : Fin 3) (i i' : Fin 5), (i : ℕ) = j → (i' : ℕ) + j + 1 = 5 →
    (j = 0 ∧ i = 0 ∧ i' = 4) ∨ (j = 1 ∧ i = 1 ∧ i' = 3) ∨ (j = 2 ∧ i = 2 ∧ i' = 2) := by
  decide

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spLinearNodeSystem_of_siegelSwapParam (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [Finite F]
    [CharP F 2] (σ : K ≃+* F)
    (Φ : Matrix.SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G))
    (S : SiegelSwapParam e t) : SpLinearNodeSystem e f 5 := by
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hM0 := S.pieceCore_eq_fstS_sup_sndS hK (j := 0) (by decide)
  have hM1 := S.pieceCore_eq_fstS_sup_sndS hK (j := 1) (by decide)
  have hU2 : pieceCore e ({2} : Finset (Fin 3)) = modelToG e (longRootSp2 K 3 (2 : Fin 3)) := by
    rw [pieceCore_two_eq_of_standard hK e σ Φ hN1, simpleRootSL2_of_not_lt (by decide)]
  have hO := S.pieceCore_zero_le_centralizer_longRootSp2_two hset hK e htC ht
  rw [← hU2] at hO
  have hc : ∀ B B' : Subgroup (StatedSp 3 K), ∀ x ∈ S.fstS B, ∀ y ∈ S.sndS B', x * y = y * x :=
    fun B B' x hx y hy => mem_centralizer_iff.1 (S.sndS_le_centralizer_fstS B B' hy) x hx
  have h02 : ∀ x ∈ S.fstS (simpleRootSL2 K 0), ∀ y ∈ pieceCore e ({2} : Finset (Fin 3)),
      x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (hO (hM0.ge (mem_sup_left hx))) y hy).symm
  have h24 : ∀ x ∈ pieceCore e ({2} : Finset (Fin 3)), ∀ y ∈ S.sndS (simpleRootSL2 K 0),
      x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (hO (hM0.ge (mem_sup_right hy))) x hx
  have hsymm : ∀ {W U V : Subgroup G}, LinearBlockStandardPair K W U V →
      LinearBlockStandardPair K W V U := by
    rintro W U V ⟨θ, c, h1, h2, h3⟩
    exact ⟨θ, c, h1, h2, h3.symm⟩
  have hA := pieceCore_two_eq_neighbourBlock hK e σ Φ hN1
  obtain ⟨WA, hWA⟩ := exists_pair_offPlane_twBlock e σ Φ
  obtain ⟨WB, hWB⟩ := exists_pair_offPlane_twBlock_compl e σ Φ
  rw [← hA] at hWA hWB
  have hp : (∃ W, LinearBlockStandardPair K W (S.fstS (simpleRootSL2 K 1))
        (pieceCore e ({2} : Finset (Fin 3)))) ∧
      (∃ W, LinearBlockStandardPair K W (pieceCore e ({2} : Finset (Fin 3)))
        (S.sndS (simpleRootSL2 K 1))) := by
    rcases fstS_sndS_eq_blocks hK e σ Φ hN1 S with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · rw [h1, h3]
      exact ⟨⟨WA, hsymm hWA⟩, ⟨WB, hWB⟩⟩
    · rw [h1, h3]
      exact ⟨⟨WB, hsymm hWB⟩, ⟨WA, hWA⟩⟩
  obtain ⟨W₃₄, h₃₄⟩ := S.exists_pair_sndS
  refine ⟨K, inferInstance, inferInstance, ![S.fstS (simpleRootSL2 K 0),
    S.fstS (simpleRootSL2 K 1), pieceCore e ({2} : Finset (Fin 3)), S.sndS (simpleRootSL2 K 1),
    S.sndS (simpleRootSL2 K 0)], hKc, ?_, ?_, ?_⟩
  · intro j i i' hi hi'
    rcases nodeFive_fold_cases j i i' hi hi' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
    · exact hM0
    · exact hM1
    · exact (sup_idem _).symm
  · intro i j hij
    rcases nodeFive_lt_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h02
    · exact hc _ _
    · exact hc _ _
    · exact hc _ _
    · exact hc _ _
    · exact h24
  · intro i j hij
    rcases nodeFive_succ_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.exists_pair_fstS
    · exact hp.1
    · exact hp.2
    · exact ⟨W₃₄, hsymm h₃₄⟩

end Nodes

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spLinearNodeSystem_of_standard
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hsplit : OddCentralSplit (siegelLevi K 3)) (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .linearEven) (hstd : SpThreeStandard e) :
    SpLinearNodeSystem e f 5 := by
  obtain ⟨S⟩ := nonempty_siegelSwapParam_of_standard hcat hdet hsplit hset hKc hf e htC ht
    (hroot 2) hstd
  obtain ⟨F, _, _, _, σ, Φ, -, hN1, -⟩ := exists_mulEquiv_of_spThreeLinearNormalized hKc hf
    (spThreeLinearNormalized_of_standard hset hKc hf e htC ht 0 (hroot 0) hstd)
  exact spLinearNodeSystem_of_siegelSwapParam hset hKc hf e htC ht σ Φ hN1 S

end Standard

theorem spThreeLinearEvenStandardInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3) :
    SpThreeLinearEvenStandardInput := by
  refine spThreeLinearEvenStandardInput_of_nodes ?_
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  exact spLinearNodeSystem_of_standard hcat hdet (oddCentralSplit_siegelLevi (by norm_num)) hset
    hKc hf e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht hroot hstd

theorem spThreeLinearEvenRecognitionInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3) :
    SpThreeLinearEvenRecognitionInput :=
  spThreeLinearEvenRecognitionInput_of_standardInput
    (spThreeLinearEvenStandardInput_of_clauses hcat hdet)

section TypeDet

theorem spThreeLinearEvenRecognitionInput_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) : SpThreeLinearEvenRecognitionInput :=
  spThreeLinearEvenRecognitionInput_of_clauses hcat (LinearPilot.slmEvenTypeDetAt le_rfl)

end TypeDet

end CFSG.SeitzReduction.SymplecticPilot
