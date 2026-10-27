module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataChart
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGlobal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.SeitzReduction.SymplecticPilot (planeCoords planeEnum planeEnum_injective liftParam
  planeTorusParam suppGL)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

section NodeDef

variable {G : Type} [Group G] {F : Type} [Field F] {r : ℕ} {τ : (Fin (r + 1) → Fˣ) →* G}

@[expose] noncomputable def q2Node (C₀ : Q2FrameChart τ 0) (j : Fin (r + 2)) : Subgroup G :=
  if j.val + 1 ≤ r then q2LevelCore τ (consecutiveBlock (r + 1) j.val 2)
  else if j.val = r then C₀.lift (forkBlock F r ∅)
  else C₀.lift (forkBlock F r {Fin.last r})

theorem q2Node_of_le (C₀ : Q2FrameChart τ 0) {j : Fin (r + 2)} (hj : j.val + 1 ≤ r) :
    q2Node C₀ j = q2LevelCore τ (consecutiveBlock (r + 1) j.val 2) := by
  simp [q2Node, hj]

theorem q2Node_of_eq (C₀ : Q2FrameChart τ 0) {j : Fin (r + 2)} (hj : j.val = r) :
    q2Node C₀ j = C₀.lift (forkBlock F r ∅) := by
  simp [q2Node, hj]

theorem q2Node_of_eq_succ (C₀ : Q2FrameChart τ 0) {j : Fin (r + 2)} (hj : j.val = r + 1) :
    q2Node C₀ j = C₀.lift (forkBlock F r {Fin.last r}) := by
  simp [q2Node, hj]

end NodeDef

section Nodes

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem commutator_q2Node (C₀ : Q2FrameChart τ 0) (j : Fin (r + 2)) :
    ⁅q2Node C₀ j, q2Node C₀ j⁆ = q2Node C₀ j := by
  unfold q2Node
  split_ifs
  · exact commutator_centralizerPerfectCore _
  · exact C₀.commutator_lift _
  · exact C₀.commutator_lift _

theorem Q2FrameChart.lift_forkBlock_le_q2PieceCore (C₀ : Q2FrameChart τ 0)
    (hF : 4 ≤ Nat.card F) (hr : 1 ≤ r) {P : Finset (Fin (r + 1))} (hP : P ⊆ {Fin.last r}) :
    C₀.lift (forkBlock F r P) ≤ q2PieceCore τ {Fin.last r} := by
  have h0 : (0 : Fin (r + 1)) ∉ ({Fin.last r} : Finset (Fin (r + 1))) := by
    rw [Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, Fin.val_last]
    omega
  have hME := q2PieceCore_le_q2NbrCore τ h0
  have h := C₀.map_frameCore (P := planeTorusParam F {Fin.last r})
    (rootParam_le_planeTorusParam h0)
  rw [image_minusNeighbourDiag] at h
  have hblock : forkBlock F r P ≤ ((((q2PieceCore τ {Fin.last r}).subgroupOf
      (q2NbrCore τ (0 : Fin (r + 1)))).map C₀.π.toMonoidHom).map
        (StatedOmega (StatedQuadPlus (r + 1) F)).subtype) := by
    rw [q2PieceCore, h]
    refine le_perfectCore_of_perfect (le_inf (forkBlock_le_statedOmega hF hr P) ?_)
      (commutator_forkBlock hF hr P)
    refine flip_siegelBlockGL_le_centralizer ?_
    rintro _ ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩ i hi
    have hlast : ∀ x : Fin (r + 1), x = Fin.last r ∨ x.val = r - 1 →
        snocOneParam F r (liftParam (RingHom.id F) (restrictParam 0 t)) x = 1 := by
      rintro x (rfl | hx)
      · exact snocOneParam_last _
      · have hx' : x = (⟨r - 1, by omega⟩ : Fin r).castSucc := Fin.ext (by simp [hx])
        rw [hx', snocOneParam_castSucc]
        have htl : t (Fin.last r) = 1 := ht _ (Finset.mem_singleton_self _)
        have hsa : (0 : Fin (r + 1)).succAbove ⟨r - 1, by omega⟩ = Fin.last r :=
          Fin.ext (by simp; omega)
        simp only [liftParam, restrictParam_apply, hsa, htl, map_one]
    apply hlast
    rcases hi with hi | hi
    · rw [mem_consecutiveBlock] at hi
      by_cases h' : i.val = r
      · exact Or.inl (Fin.ext (by simp [h']))
      · exact Or.inr (by omega)
    · exact Or.inl (Finset.mem_singleton.1 (hP hi))
  have hA : ⁅(C₀.lift (forkBlock F r P)).subgroupOf (q2NbrCore τ (0 : Fin (r + 1))),
      (C₀.lift (forkBlock F r P)).subgroupOf (q2NbrCore τ (0 : Fin (r + 1)))⁆ =
      (C₀.lift (forkBlock F r P)).subgroupOf (q2NbrCore τ (0 : Fin (r + 1))) :=
    commutator_subgroupOf_eq_of_le_perfect (C₀.lift_le _) (C₀.commutator_lift _)
  have hB : ⁅(q2PieceCore τ {Fin.last r}).subgroupOf (q2NbrCore τ (0 : Fin (r + 1))),
      (q2PieceCore τ {Fin.last r}).subgroupOf (q2NbrCore τ (0 : Fin (r + 1)))⁆ =
      (q2PieceCore τ {Fin.last r}).subgroupOf (q2NbrCore τ (0 : Fin (r + 1))) :=
    commutator_subgroupOf_eq_of_le_perfect hME (commutator_centralizerPerfectCore _)
  have hAB := le_of_map_le_of_perfect C₀.ker_toGL_le hA hB (by
    rw [C₀.map_toGL, C₀.map_toGL, C₀.map_lift (forkBlock_le_statedOmega hF hr P)
      (commutator_forkBlock hF hr P)]
    exact hblock)
  intro x hx
  exact hAB (show (⟨x, C₀.lift_le _ hx⟩ : q2NbrCore τ (0 : Fin (r + 1))) ∈ _ from hx)

end Nodes

section Pairs

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem exists_theta_q2Node (hr : 3 ≤ r) (hC : ∀ k, Q2FrameChart τ k) (hF : 4 ≤ Nat.card F)
    {i j : Fin (r + 2)} (hij : edgeD (r + 2) i j) :
    ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = q2Node (hC 0) i ∧
      (B23 F).map θ = q2Node (hC 0) j := by
  have hcb : ∀ a, a + 2 ≤ r + 1 → 2 ≤ (consecutiveBlock (r + 1) a 2).card := fun a ha =>
    (card_consecutiveBlock_two ha).ge
  unfold edgeD at hij
  rcases hij with ⟨hij, hjn⟩ | ⟨hi, hj⟩
  · by_cases hjr : j.val + 1 ≤ r
    ·
      have hir : i.val + 1 ≤ r := by omega
      rw [q2Node_of_le _ hir, q2Node_of_le _ hjr]
      by_cases hi0 : i.val = 0
      · have hki : Fin.last r ∉ consecutiveBlock (r + 1) i.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_last]
          omega
        have hkj : Fin.last r ∉ consecutiveBlock (r + 1) j.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_last]
          omega
        have hU := (hC (Fin.last r)).map_levelCore hF hki (hcb _ (by omega))
        have hV := (hC (Fin.last r)).map_levelCore hF hkj (hcb _ (by omega))
        rw [castSuccPlanes_preimagePlanes_last (by omega)] at hU hV
        refine (hC (Fin.last r)).exists_theta_of_images hF
          (q2LevelCore_le_q2NbrCore τ hki) (q2LevelCore_le_q2NbrCore τ hkj)
          (a := i.val) (by omega) ∅ ?_ ?_
        · rw [hU, map_conj_flipGL_empty]
        · rw [hV, map_conj_flipGL_empty, ← hij]
      · have h0i : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_zero]
          omega
        have h0j : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) j.val 2 := by
          rw [mem_consecutiveBlock, Fin.val_zero]
          omega
        have hU := (hC 0).map_levelCore hF h0i (hcb _ (by omega))
        have hV := (hC 0).map_levelCore hF h0j (hcb _ (by omega))
        rw [castSuccPlanes_preimagePlanes_zero (by omega) hir] at hU
        rw [castSuccPlanes_preimagePlanes_zero (by omega) hjr] at hV
        refine (hC 0).exists_theta_of_images hF
          (q2LevelCore_le_q2NbrCore τ h0i) (q2LevelCore_le_q2NbrCore τ h0j)
          (a := i.val - 1) (by omega) ∅ ?_ ?_
        · rw [hU, map_conj_flipGL_empty]
        · rw [hV, map_conj_flipGL_empty, show j.val - 1 = i.val - 1 + 1 by omega]
    ·
      have hjr' : j.val = r := by omega
      have hir : i.val + 1 ≤ r := by omega
      rw [q2Node_of_le _ hir, q2Node_of_eq _ hjr']
      have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
        rw [mem_consecutiveBlock, Fin.val_zero]
        omega
      have hU := (hC 0).map_levelCore hF h0 (hcb _ (by omega))
      rw [castSuccPlanes_preimagePlanes_zero (by omega) hir, show i.val - 1 = r - 2 by omega] at hU
      have hV := (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
        (commutator_forkBlock hF (by omega) ∅)
      refine (hC 0).exists_theta_of_images hF (q2LevelCore_le_q2NbrCore τ h0)
        ((hC 0).lift_le _) (a := r - 2) (by omega) ∅ ?_ ?_
      · rw [hU, map_conj_flipGL_empty]
      · rw [hV, forkBlock, show r - 2 + 1 = r - 1 by omega]
  ·
    have hir : i.val + 1 ≤ r := by omega
    have hj' : j.val = r + 1 := by omega
    rw [q2Node_of_le _ hir, q2Node_of_eq_succ _ hj']
    have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) i.val 2 := by
      rw [mem_consecutiveBlock, Fin.val_zero]
      omega
    have hU := (hC 0).map_levelCore hF h0 (hcb _ (by omega))
    rw [castSuccPlanes_preimagePlanes_zero (by omega) hir, show i.val - 1 = r - 2 by omega] at hU
    have hV := (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) {Fin.last r})
      (commutator_forkBlock hF (by omega) {Fin.last r})
    have hdisj : Disjoint (consecutiveBlock (r + 1) (r - 2) 2) {Fin.last r} := by
      rw [Finset.disjoint_singleton_right, mem_consecutiveBlock, Fin.val_last]
      omega
    refine (hC 0).exists_theta_of_images hF (q2LevelCore_le_q2NbrCore τ h0)
      ((hC 0).lift_le _) (a := r - 2) (by omega) {Fin.last r} ?_ ?_
    · rw [hU, map_flipGL_siegelBlockGL_of_disjoint hdisj]
    · rw [hV, forkBlock, show r - 2 + 1 = r - 1 by omega]

end Pairs

section Commute

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem q2LevelCore_le_centralizer_q2PieceCore (hr : 3 ≤ r) [CharP F 2]
    (hC : ∀ k, Q2FrameChart τ k) (hF : 4 ≤ Nat.card F) {j : ℕ} (hj : j + 2 ≤ r) :
    q2LevelCore τ (consecutiveBlock (r + 1) j 2) ≤
      centralizer (q2PieceCore τ {Fin.last r} : Set G) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := consecutiveBlock (r + 1) j 2 ∪ {Fin.last r}) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 := Finset.card_union_le (consecutiveBlock (r + 1) j 2) {Fin.last r}
      rw [card_consecutiveBlock_two (by omega), Finset.card_singleton] at h1
      omega)
  have hkJ : k ∉ consecutiveBlock (r + 1) j 2 := fun h => hk (Finset.mem_union_left _ h)
  have hkI : k ∉ ({Fin.last r} : Finset (Fin (r + 1))) := fun h => hk (Finset.mem_union_right _ h)
  have hU := (hC k).map_levelCore hF hkJ (card_consecutiveBlock_two (by omega)).ge
  have hV := (hC k).map_pieceCore hF hkI (Finset.singleton_nonempty _)
  have hdisj : Disjoint (castSuccPlanes (preimagePlanes k (consecutiveBlock (r + 1) j 2)))
      (insert (Fin.last r) (castSuccPlanes (preimagePlanes k {Fin.last r}))) := by
    rw [Finset.disjoint_insert_right]
    refine ⟨last_notMem_castSuccPlanes _, disjoint_castSuccPlanes_preimagePlanes ?_⟩
    rw [Finset.disjoint_singleton_right, mem_consecutiveBlock, Fin.val_last]
    omega
  refine (hC k).le_centralizer (q2LevelCore_le_q2NbrCore τ hkJ)
    (q2PieceCore_le_q2NbrCore τ hkI) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_suppGL_of_disjoint (disjoint_planeCoords hdisj)
    (siegelBlockGL_le_suppGL _ hx) (map_statedOmega_spEmbedGL_le_suppGL _ hy)

theorem q2LevelCore_le_centralizer_q2LevelCore (hr : 4 ≤ r)
    (hC : ∀ k, Q2FrameChart τ k) (hF : 4 ≤ Nat.card F) {i j : ℕ}
    (hi : i + 2 ≤ r + 1) (hj : j + 2 ≤ r + 1)
    (hd : Disjoint (consecutiveBlock (r + 1) i 2) (consecutiveBlock (r + 1) j 2)) :
    q2LevelCore τ (consecutiveBlock (r + 1) i 2) ≤
      centralizer (q2LevelCore τ (consecutiveBlock (r + 1) j 2) : Set G) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := consecutiveBlock (r + 1) i 2 ∪ consecutiveBlock (r + 1) j 2) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 := Finset.card_union_le (consecutiveBlock (r + 1) i 2)
        (consecutiveBlock (r + 1) j 2)
      rw [card_consecutiveBlock_two hi, card_consecutiveBlock_two hj] at h1
      omega)
  have hki : k ∉ consecutiveBlock (r + 1) i 2 := fun h => hk (Finset.mem_union_left _ h)
  have hkj : k ∉ consecutiveBlock (r + 1) j 2 := fun h => hk (Finset.mem_union_right _ h)
  have hU := (hC k).map_levelCore hF hki (card_consecutiveBlock_two hi).ge
  have hV := (hC k).map_levelCore hF hkj (card_consecutiveBlock_two hj).ge
  refine (hC k).le_centralizer (q2LevelCore_le_q2NbrCore τ hki)
    (q2LevelCore_le_q2NbrCore τ hkj) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_suppGL_of_disjoint
    (disjoint_planeCoords (disjoint_castSuccPlanes_preimagePlanes hd))
    (siegelBlockGL_le_suppGL _ hx) (siegelBlockGL_le_suppGL _ hy)

theorem Q2FrameChart.lift_forkBlock_le_centralizer (C₀ : Q2FrameChart τ 0) (hr : 2 ≤ r)
    (hF : 4 ≤ Nat.card F) :
    C₀.lift (forkBlock F r ∅) ≤ centralizer (C₀.lift (forkBlock F r {Fin.last r}) : Set G) := by
  have hU := C₀.map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
    (commutator_forkBlock hF (by omega) ∅)
  have hV := C₀.map_lift (forkBlock_le_statedOmega hF (by omega) {Fin.last r})
    (commutator_forkBlock hF (by omega) {Fin.last r})
  have hPB : consecutiveBlock (r + 1) (r - 1) 2 ∩ {Fin.last r} = {Fin.last r} := by
    rw [Finset.inter_singleton_of_mem]
    rw [mem_consecutiveBlock, Fin.val_last]
    omega
  refine C₀.le_centralizer (C₀.lift_le _) (C₀.lift_le _) ?_
  intro x hx y hy
  rw [hU, forkBlock, map_conj_flipGL_empty] at hx
  rw [hV, forkBlock] at hy
  exact commute_siegelBlockGL_flip hF (card_consecutiveBlock_two (by omega)) hPB hx hy

theorem q2Node_le_centralizer [CharP F 2] (hr : 4 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    (hF : 4 ≤ Nat.card F) {i j : Fin (r + 2)} (hij : i ≠ j)
    (h1 : ¬ edgeD (r + 2) i j) (h2 : ¬ edgeD (r + 2) j i) :
    q2Node (hC 0) i ≤ centralizer (q2Node (hC 0) j : Set G) := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  unfold edgeD at h1 h2
  have hfork : ∀ x : Fin (r + 2), r ≤ x.val →
      q2Node (hC 0) x ≤ q2PieceCore τ {Fin.last r} := by
    intro x hx
    rcases (show x.val = r ∨ x.val = r + 1 by omega) with h | h
    · rw [q2Node_of_eq _ h]
      exact (hC 0).lift_forkBlock_le_q2PieceCore hF (by omega) (Finset.empty_subset _)
    · rw [q2Node_of_eq_succ _ h]
      exact (hC 0).lift_forkBlock_le_q2PieceCore hF (by omega) le_rfl
  by_cases hi : i.val + 1 ≤ r <;> by_cases hj : j.val + 1 ≤ r
  · rw [q2Node_of_le _ hi, q2Node_of_le _ hj]
    refine q2LevelCore_le_centralizer_q2LevelCore hr hC hF (by omega) (by omega) ?_
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_consecutiveBlock] at hx hx'
    omega
  ·
    rw [q2Node_of_le _ hi]
    exact (q2LevelCore_le_centralizer_q2PieceCore (by omega) hC hF (by omega)).trans
      (Subgroup.centralizer_le (hfork j (by omega)))
  ·
    rw [q2Node_of_le _ hj]
    have h := (q2LevelCore_le_centralizer_q2PieceCore (τ := τ) (by omega) hC hF
      (j := j.val) (by omega)).trans (Subgroup.centralizer_le (hfork i (by omega)))
    exact Subgroup.le_centralizer_iff.1 h
  ·
    rcases (show (i.val = r ∧ j.val = r + 1) ∨ (i.val = r + 1 ∧ j.val = r) by omega) with
      ⟨hi', hj'⟩ | ⟨hi', hj'⟩
    · rw [q2Node_of_eq _ hi', q2Node_of_eq_succ _ hj']
      exact (hC 0).lift_forkBlock_le_centralizer (by omega) hF
    · rw [q2Node_of_eq_succ _ hi', q2Node_of_eq _ hj']
      exact Subgroup.le_centralizer_iff.1 ((hC 0).lift_forkBlock_le_centralizer (by omega) hF)

end Commute

section Global

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem q2Node_succ_le (hC : ∀ k, Q2FrameChart τ k) (j : Fin (r + 1)) :
    q2Node (hC 0) j.succ ≤ q2NbrCore τ (0 : Fin (r + 1)) := by
  rcases (show j.val + 2 ≤ r ∨ r ≤ j.val + 1 by omega) with h | h
  · rw [q2Node_of_le _ (show j.succ.val + 1 ≤ r by rw [Fin.val_succ]; omega)]
    refine q2LevelCore_le_q2NbrCore τ ?_
    rw [mem_consecutiveBlock, Fin.val_zero, Fin.val_succ]
    omega
  · rcases (show j.succ.val = r ∨ j.succ.val = r + 1 by rw [Fin.val_succ]; omega) with h' | h'
    · rw [q2Node_of_eq _ h']
      exact (hC 0).lift_le _
    · rw [q2Node_of_eq_succ _ h']
      exact (hC 0).lift_le _

theorem map_q2Node_succ (hr : 2 ≤ r) (hC : ∀ k, Q2FrameChart τ k) (hF : 4 ≤ Nat.card F)
    (j : Fin (r + 1)) :
    (((q2Node (hC 0) j.succ).subgroupOf (q2NbrCore τ (0 : Fin (r + 1)))).map
        (hC 0).π.toMonoidHom).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelNode F (r + 1) j := by
  rcases (show j.val + 2 ≤ r ∨ j.val + 1 = r ∨ j.val = r by omega) with h | h | h
  · have hj : j.succ.val + 1 ≤ r := by rw [Fin.val_succ]; omega
    have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) j.succ.val 2 := by
      rw [mem_consecutiveBlock, Fin.val_zero, Fin.val_succ]
      omega
    rw [q2Node_of_le _ hj, (hC 0).map_levelCore hF h0
      (card_consecutiveBlock_two (by rw [Fin.val_succ]; omega)).ge,
      castSuccPlanes_preimagePlanes_zero (by rw [Fin.val_succ]; omega) hj, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = ∅ := by
      ext x
      rw [mem_plusNodeFlip]
      simp only [Finset.notMem_empty, iff_false]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (j.succ.val - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock, Fin.val_succ]
      have := x.isLt
      omega
    rw [hflip, flipGL_empty, map_conj_one_eq, hset]
  · have hj : j.succ.val = r := by rw [Fin.val_succ]; omega
    rw [q2Node_of_eq _ hj, (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
      (commutator_forkBlock hF (by omega) ∅), forkBlock, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = ∅ := by
      ext x
      rw [mem_plusNodeFlip]
      simp only [Finset.notMem_empty, iff_false]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (r - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock]
      have := x.isLt
      omega
    rw [hflip, hset]
  · have hj : j.succ.val = r + 1 := by rw [Fin.val_succ]; omega
    rw [q2Node_of_eq_succ _ hj, (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) _)
      (commutator_forkBlock hF (by omega) _), forkBlock, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = {Fin.last r} := by
      ext x
      rw [mem_plusNodeFlip, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (r - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock]
      have := x.isLt
      omega
    rw [hflip, hset]

theorem q2NbrCore_zero_le_iSup [CharP F 2] (hr : 3 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    {f' : ℕ} (hF' : Nat.card F = 2 ^ f') (hF : 4 ≤ Nat.card F) :
    q2NbrCore τ (0 : Fin (r + 1)) ≤ ⨆ j : Fin (r + 1), q2Node (hC 0) j.succ := by
  set E := q2NbrCore τ (0 : Fin (r + 1)) with hE
  set X := ⨆ j : Fin (r + 1), q2Node (hC 0) j.succ with hX
  have hXE : ∀ j : Fin (r + 1), q2Node (hC 0) j.succ ≤ E := q2Node_succ_le hC
  have hXp : ⁅X, X⁆ = X := commutator_iSup_of_perfect fun j => commutator_q2Node _ _
  have himg : (X.subgroupOf E).map (hC 0).toGL = StatedOmega (StatedQuadPlus (r + 1) F) := by
    rw [hX, subgroupOf_iSup_of_le_minus hXE, Subgroup.map_iSup]
    have h1 : ∀ j : Fin (r + 1), ((q2Node (hC 0) j.succ).subgroupOf E).map (hC 0).toGL =
        siegelNode F (r + 1) j := fun j => by
      rw [(hC 0).map_toGL]
      exact map_q2Node_succ (by omega) hC hF j
    simp only [h1]
    exact iSup_siegelNode_eq_statedOmega (by omega) hF' hF
  have hrange : (⊤ : Subgroup E).map (hC 0).toGL = StatedOmega (StatedQuadPlus (r + 1) F) := by
    rw [← MonoidHom.range_eq_map, (hC 0).range_toGL]
  have hA : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = (⊤ : Subgroup E) := by
    have h := commutator_subgroupOf_eq_of_le_perfect (le_refl E)
      (commutator_q2FrameCore τ (rootParam (0 : Fin (r + 1))))
    rwa [Subgroup.subgroupOf_self] at h
  have hB := commutator_subgroupOf_eq_of_le_perfect (iSup_le hXE) hXp
  have hle := le_of_map_le_of_perfect (hC 0).ker_toGL_le hA hB (by rw [hrange, himg])
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : E))

theorem exists_q2Node_le_q2NbrCore (hr : 2 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    (j : Fin (r + 2)) : ∃ k : Fin (r + 1), q2Node (hC 0) j ≤ q2NbrCore τ k := by
  by_cases hj : j.val + 1 ≤ r
  · rw [q2Node_of_le _ hj]
    by_cases hj0 : j.val = 0
    · refine ⟨Fin.last r, q2LevelCore_le_q2NbrCore τ ?_⟩
      rw [mem_consecutiveBlock, Fin.val_last]
      omega
    · refine ⟨0, q2LevelCore_le_q2NbrCore τ ?_⟩
      rw [mem_consecutiveBlock, Fin.val_zero]
      omega
  · refine ⟨0, ?_⟩
    rcases (show j.val = r ∨ j.val = r + 1 by omega) with h | h
    · rw [q2Node_of_eq _ h]
      exact (hC 0).lift_le _
    · rw [q2Node_of_eq_succ _ h]
      exact (hC 0).lift_le _

end Global

end CFSG.SeitzReduction.OmegaPilot
