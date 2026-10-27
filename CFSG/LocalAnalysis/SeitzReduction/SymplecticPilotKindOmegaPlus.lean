module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCTRoot
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (B12 B23 blockSL)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL leviEmbedSL_injective)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open scoped MatrixGroups

section Chain

variable {K : Type} [Field K] {n : ℕ}

theorem kOmega_simpleRootSL2_le_centralizer {i j : Fin n} (hij : i.val + 2 ≤ j.val) :
    simpleRootSL2 K i ≤ centralizer (simpleRootSL2 K j : Set (StatedSp n K)) := by
  classical
  set I : Finset (Fin n) := Finset.univ.filter fun x => x.val ≤ i.val + 1 with hIdef
  set J : Finset (Fin n) := Finset.univ.filter fun x => j.val ≤ x.val with hJdef
  have hI : simpleRootSL2 K i ≤ spBlock K I :=
    simpleRootSL2_le_spBlock (by simp [hIdef]) (fun _ => by simp [hIdef])
  have hJ : simpleRootSL2 K j ≤ spBlock K J :=
    simpleRootSL2_le_spBlock (by simp [hJdef]) (fun _ => by
      simp only [hJdef, Finset.mem_filter, Finset.mem_univ, true_and]
      omega)
  have hdisj : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [hIdef, hJdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    omega
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (commute_of_mem_spBlock_of_disjoint hdisj (hI hx) (hJ hy)).eq.symm

theorem kOmega_consecutiveBlock_two {i : ℕ} (hi : i + 1 < n) :
    consecutiveBlock n i 2 = {(⟨i, by omega⟩ : Fin n), ⟨i + 1, hi⟩} := by
  ext x
  rw [LinearPilot.mem_consecutiveBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
    Fin.ext_iff]
  simp only
  omega

theorem kOmega_map_leviEmbedSL_blockSL_two [Finite K] {i : ℕ} (hi : i + 1 < n) :
    (⊤ : Subgroup SL(2, K)).map ((leviEmbedSL K n).comp (blockSL K n 2 i (by omega))) =
      simpleRootSL2 K ⟨i, by omega⟩ := by
  rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, LinearPilot.range_blockSL_eq,
    ← siegelBlock_pair_eq_simpleRootSL2' (j := ⟨i, by omega⟩) hi, kOmega_consecutiveBlock_two hi]
  rfl

theorem kOmega_exists_theta_simpleRootSL2 [Finite K] {i : ℕ} (hi : i + 2 < n) :
    ∃ θ : SL(3, K) →* StatedSp n K, Function.Injective θ ∧
      (B12 K).map θ = simpleRootSL2 K ⟨i, by omega⟩ ∧
      (B23 K).map θ = simpleRootSL2 K ⟨i + 1, by omega⟩ := by
  refine ⟨(leviEmbedSL K n).comp (blockSL K n 3 i (by omega)),
    leviEmbedSL_injective.comp (CFSG.ClassicalInvolution.WeakCT.blockSL_injective _), ?_, ?_⟩
  · have h : (B12 K).map ((leviEmbedSL K n).comp (blockSL K n 3 i (by omega))) =
        (⊤ : Subgroup SL(2, K)).map ((leviEmbedSL K n).comp (blockSL K n 2 i (by omega))) := by
      rw [CFSG.ClassicalInvolution.WeakCT.B12, MonoidHom.range_eq_map, Subgroup.map_map,
        MonoidHom.comp_assoc, CFSG.ClassicalInvolution.WeakCT.blockSL_comp]
      rfl
    rw [h, kOmega_map_leviEmbedSL_blockSL_two (by omega)]
  · have h : (B23 K).map ((leviEmbedSL K n).comp (blockSL K n 3 i (by omega))) =
        (⊤ : Subgroup SL(2, K)).map
          ((leviEmbedSL K n).comp (blockSL K n 2 (i + 1) (by omega))) := by
      rw [CFSG.ClassicalInvolution.WeakCT.B23, MonoidHom.range_eq_map, Subgroup.map_map,
        MonoidHom.comp_assoc, CFSG.ClassicalInvolution.WeakCT.blockSL_comp]
    rw [h, kOmega_map_leviEmbedSL_blockSL_two (by omega)]

end Chain

section Nodes

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {m : ℕ}

@[expose] def SpOmegaPlusPieces (e : L ≃* StatedSp (m + 2) K) : Prop :=
  (∀ j : Fin (m + 2), j.val + 1 < m + 2 →
      pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j)) ∧
  ∃ A B : Subgroup G, A ≤ centralizer (B : Set G) ∧
    A ⊔ B = pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) ∧
    (∀ i : Fin (m + 2), i.val + 3 ≤ m + 2 → modelToG e (simpleRootSL2 K i) ≤
      centralizer (pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) : Set G)) ∧
    (∃ θ : SL(3, K) →* G, θ.ker ≤ center SL(3, K) ∧
      (B12 K).map θ = modelToG e (simpleRootSL2 K (Fin.last m).castSucc) ∧ (B23 K).map θ = A) ∧
    (∃ θ : SL(3, K) →* G, θ.ker ≤ center SL(3, K) ∧
      (B12 K).map θ = modelToG e (simpleRootSL2 K (Fin.last m).castSucc) ∧ (B23 K).map θ = B)

@[expose] noncomputable def omegaPlusNode (e : L ≃* StatedSp (m + 2) K) (A B : Subgroup G)
    (i : Fin (m + 3)) : Subgroup G :=
  if h : i.val ≤ m then modelToG e (simpleRootSL2 K ⟨i.val, by omega⟩)
  else if i.val = m + 1 then A else B

variable (e : L ≃* StatedSp (m + 2) K) (A B : Subgroup G)

theorem omegaPlusNode_of_le {i : Fin (m + 3)} (h : i.val ≤ m) :
    omegaPlusNode e A B i = modelToG e (simpleRootSL2 K ⟨i.val, by omega⟩) :=
  dite_eq_left h

theorem omegaPlusNode_of_eq_succ {i : Fin (m + 3)} (h : i.val = m + 1) :
    omegaPlusNode e A B i = A := by
  rw [omegaPlusNode, dite_eq_right (by omega), ite_eq_left h]

theorem omegaPlusNode_of_eq_add_two {i : Fin (m + 3)} (h : i.val = m + 2) :
    omegaPlusNode e A B i = B := by
  rw [omegaPlusNode, dite_eq_right (by omega), ite_eq_right (by omega)]

end Nodes

section Recognition

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {m : ℕ}

omit [Finite K] [CharP K 2] in
theorem spGlobal_eq_iSup_omegaPlusNode (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp (m + 2) K)
    {A B : Subgroup G}
    (hshort : ∀ j : Fin (m + 2), j.val + 1 < m + 2 →
      pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j))
    (hAB : A ⊔ B = pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2)))) :
    spGlobal e = ⨆ i, omegaPlusNode e A B i := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hj : j.val + 1 < m + 2
    · rw [hshort j hj]
      have h1 := le_iSup (omegaPlusNode e A B) ⟨j.val, by omega⟩
      rw [omegaPlusNode_of_le e A B (i := ⟨j.val, by omega⟩) (by simp only; omega)] at h1
      exact h1
    · have hjl : j = Fin.last (m + 1) := Fin.ext (by rw [Fin.val_last]; omega)
      rw [hjl, ← hAB]
      refine sup_le ?_ ?_
      · have h1 := le_iSup (omegaPlusNode e A B) ⟨m + 1, by omega⟩
        rwa [omegaPlusNode_of_eq_succ e A B rfl] at h1
      · have h1 := le_iSup (omegaPlusNode e A B) ⟨m + 2, by omega⟩
        rwa [omegaPlusNode_of_eq_add_two e A B rfl] at h1
  · refine iSup_le fun i => ?_
    have hlast : pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) ≤ spGlobal e :=
      le_iSup (fun j : Fin (m + 2) => pieceCore e ({j} : Finset (Fin (m + 2)))) (Fin.last (m + 1))
    by_cases hi : i.val ≤ m
    · rw [omegaPlusNode_of_le e A B hi]
      exact (modelToG_simpleRootSL2_le_pieceCore e hK (Finset.mem_singleton_self _)).trans
        (le_iSup (fun j : Fin (m + 2) => pieceCore e ({j} : Finset (Fin (m + 2)))) _)
    · by_cases hi' : i.val = m + 1
      · rw [omegaPlusNode_of_eq_succ e A B hi', ← hAB] at *
        exact le_sup_left.trans hlast
      · rw [omegaPlusNode_of_eq_add_two e A B (by have := i.isLt; omega), ← hAB] at *
        exact le_sup_right.trans hlast

theorem sp2mKindType_omegaPlus_of_pieces [Finite G] {f : ℕ} (hm : 2 ≤ m)
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

end Recognition

@[expose] def SpOmegaPlusPieceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 2 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 2) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 2), RootKindSp e t f k .omegaPlus) → SpOmegaPlusPieces e

theorem spOmegaKindInput_omegaPlus_of_pieceInput (h : SpOmegaPlusPieceInput) :
    SpOmegaKindInput .omegaPlus := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact sp2mKindType_omegaPlus_of_pieces (by omega) hKc hf e
    (h G L hset m f K (by omega) hKc hf e t ht hKt hroot)

end CFSG.SeitzReduction.SymplecticPilot
