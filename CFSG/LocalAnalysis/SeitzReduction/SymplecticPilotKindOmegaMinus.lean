module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaPlus
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.RankThree.PartOne.CTP.SU4EvenGen
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCPairs

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (B12 B23 LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair spinMinusModel)
open CFSG.LieType.Universal.Spin.Twisted (fact_shortField)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Pairs

variable {X : Type} [Group X]

theorem kOmega_linearBlockStandardPair_of_theta {K : Type} [Field K] (θ : SL(3, K) →* X)
    (hθ : θ.ker ≤ center SL(3, K)) :
    LinearBlockStandardPair K θ.range ((B12 K).map θ) ((B23 K).map θ) :=
  ⟨θ, 1, rfl, hθ, Or.inl ⟨by rw [OmegaPilot.map_conj_one_inv_eq'],
    by rw [OmegaPilot.map_conj_one_inv_eq']⟩⟩

theorem kOmega_range_theta_eq_sup {K : Type} [Field K] (θ : SL(3, K) →* X) :
    θ.range = (B12 K).map θ ⊔ (B23 K).map θ := by
  rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, Subgroup.map_sup]

variable
  {F : Type} [Field F] [Finite F] {b c : F} {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0}

theorem kOmega_twistedB2BlockStandardPair_subgroupOf {W U V J : Subgroup X} (hW : W ≤ J)
    (h : TwistedB2BlockStandardPair hirr W U V) :
    TwistedB2BlockStandardPair hirr (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  have := fact_shortField hirr
  obtain ⟨θ, hrange, hker, hinjL, hinjS, hU, hV⟩ := h
  have hJ : ∀ g, θ g ∈ J := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  have himg : ∀ (S : Subgroup _) (Y : Subgroup X), S.map θ = Y →
      S.map (θ.codRestrict J hJ) = Y.subgroupOf J := by
    intro S Y hSY
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hSY ▸ ⟨g, hg, rfl⟩)
    · intro hx
      obtain ⟨g, hg, hgx⟩ := hSY ▸ (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨g, hg, Subtype.ext hgx⟩
  refine ⟨θ.codRestrict J hJ, ?_, ?_, ?_, ?_, himg _ _ hU, himg _ _ hV⟩
  · rw [MonoidHom.range_eq_map, himg ⊤ W (by rw [← MonoidHom.range_eq_map, hrange])]
  · rw [MonoidHom.ker_codRestrict]
    exact hker
  · exact fun x y hxy => hinjL (congrArg Subtype.val hxy)
  · exact fun x y hxy => hinjS (congrArg Subtype.val hxy)

theorem kOmega_twistedB2BlockStandardPair_le_sup [CharP F 2] {W U V : Subgroup X}
    (h : TwistedB2BlockStandardPair hirr W U V) : W ≤ U ⊔ V := by
  have := fact_shortField hirr
  obtain ⟨θ, hrange, -, -, -, hU, hV⟩ := h
  rw [← hrange, MonoidHom.range_eq_map,
    ← CFSG.RankThree.PartOne.CTP.SU4Even.spinMinusModel_blocks_sup_eq_top_even hirr,
    Subgroup.map_sup, hU, hV]

end Pairs

section Minus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {m : ℕ}

@[expose] def SpOmegaMinusPieces (e : L ≃* StatedSp (m + 2) K) : Prop :=
  (∀ j : Fin (m + 2), j.val + 1 < m + 2 →
      pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j)) ∧
  (∀ i : Fin (m + 2), i.val + 3 ≤ m + 2 → modelToG e (simpleRootSL2 K i) ≤
      centralizer (pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) : Set G)) ∧
  ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
    TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K (Fin.last m).castSucc))
      (pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))))

theorem sp2mKindType_omegaMinus_of_pieces [CharP K 2] {f : ℕ} (hm : 2 ≤ m)
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

end Minus

@[expose] def SpOmegaMinusPieceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 2) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 2), RootKindSp e t f k .omegaMinus) → SpOmegaMinusPieces e

theorem spOmegaKindInput_omegaMinus_of_pieceInput (h : SpOmegaMinusPieceInput) :
    SpOmegaKindInput .omegaMinus := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact sp2mKindType_omegaMinus_of_pieces (by omega) hKc hf e
    (h G L hset m f K (by omega) hKc hf e t ht hKt hroot)

end CFSG.SeitzReduction.SymplecticPilot
