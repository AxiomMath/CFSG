module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Timmesfeld (edgeD)

section Pieces

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G} {k : Fin (r + 1)}

theorem Q2FrameChart.q2LevelCore_pair_le_sup [CharP F 2] (C : Q2FrameChart τ k)
    (hF : 4 ≤ Nat.card F) {a b' : Fin (r + 1)} (hab : a ≠ b') (hka : k ≠ a) (hkb : k ≠ b') :
    q2LevelCore τ ({a, b'} : Finset (Fin (r + 1))) ≤
      q2PieceCore τ ({a} : Finset (Fin (r + 1))) ⊔ q2PieceCore τ ({b'} : Finset (Fin (r + 1))) := by
  obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (Ne.symm hka)
  obtain ⟨b'', hb''⟩ := Fin.exists_succAbove_eq (Ne.symm hkb)
  have hab' : a' ≠ b'' := fun h => hab (by rw [← ha', ← hb'', h])
  have hkJ : k ∉ ({a, b'} : Finset (Fin (r + 1))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hka, hkb⟩
  have hka' : k ∉ ({a} : Finset (Fin (r + 1))) := by simpa using hka
  have hkb' : k ∉ ({b'} : Finset (Fin (r + 1))) := by simpa using hkb
  have hUE := q2LevelCore_le_q2NbrCore τ hkJ
  have hPaE := q2PieceCore_le_q2NbrCore τ hka'
  have hPbE := q2PieceCore_le_q2NbrCore τ hkb'
  have hU := C.map_levelCore hF hkJ (by rw [Finset.card_pair hab])
  have hPa := C.map_pieceCore hF hka' (Finset.singleton_nonempty _)
  have hPb := C.map_pieceCore hF hkb' (Finset.singleton_nonempty _)
  rw [preimagePlanes_pair ha' hb'', castSuccPlanes_pair] at hU
  rw [preimagePlanes_singleton ha', castSuccPlanes_singleton] at hPa
  rw [preimagePlanes_singleton hb'', castSuccPlanes_singleton] at hPb
  have hne : ∀ x : Fin r, Fin.last r ≠ x.castSucc := fun x h => Fin.castSucc_ne_last x h.symm
  have hcard : ∀ x : Fin r, 2 ≤ (insert (Fin.last r) ({x.castSucc} : Finset (Fin (r + 1)))).card :=
    fun x => by rw [Finset.card_insert_of_notMem (by simpa using hne x), Finset.card_singleton]
  have hmodel : siegelBlockGL F ({a'.castSucc, b''.castSucc} : Finset (Fin (r + 1))) ≤
      (((q2PieceCore τ {a}).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
          (StatedOmega (StatedQuadPlus (r + 1) F)).subtype ⊔
        (((q2PieceCore τ {b'}).subgroupOf (q2NbrCore τ k)).map C.π.toMonoidHom).map
          (StatedOmega (StatedQuadPlus (r + 1) F)).subtype := by
    rw [hPa, hPb]
    refine (siegelBlockGL_pair_le_sup (fun h => hab' (Fin.castSucc_injective _ h))
      (fun h => hne a' h.symm) (fun h => hne b'' h.symm)).trans (sup_le_sup ?_ ?_)
    · exact siegelBlockGL_le_map_statedOmega hF (hcard a')
    · exact siegelBlockGL_le_map_statedOmega hF (hcard b'')
  have hA := commutator_subgroupOf_eq_of_le_perfect hUE (commutator_q2FrameCore τ _)
  have hB := commutator_subgroupOf_eq_of_le_perfect (sup_le hPaE hPbE)
    (commutator_sup_of_perfect (commutator_q2FrameCore τ _) (commutator_q2FrameCore τ _))
  have hle := le_of_map_le_of_perfect C.ker_toGL_le hA hB (by
    rw [C.map_toGL, C.map_toGL, Subgroup.subgroupOf_sup hPaE hPbE, Subgroup.map_sup,
      Subgroup.map_sup, hU]
    exact hmodel)
  intro x hx
  exact hle (show (⟨x, hUE hx⟩ : q2NbrCore τ k) ∈
    (q2LevelCore τ ({a, b'} : Finset (Fin (r + 1)))).subgroupOf (q2NbrCore τ k) from hx)

theorem Q2FrameChart.q2LevelCore_le_centralizer_q2PieceCore_of_notMem [CharP F 2]
    (C : Q2FrameChart τ k) (hF : 4 ≤ Nat.card F) {J : Finset (Fin (r + 1))} (hJ : 2 ≤ J.card)
    {p : Fin (r + 1)} (hkJ : k ∉ J) (hkp : k ≠ p) (hpJ : p ∉ J) :
    q2LevelCore τ J ≤ centralizer (q2PieceCore τ ({p} : Finset (Fin (r + 1))) : Set G) := by
  have hkI : k ∉ ({p} : Finset (Fin (r + 1))) := by simpa using hkp
  have hU := C.map_levelCore hF hkJ hJ
  have hV := C.map_pieceCore hF hkI (Finset.singleton_nonempty _)
  have hdisj : Disjoint (castSuccPlanes (preimagePlanes k J))
      (insert (Fin.last r) (castSuccPlanes (preimagePlanes k {p}))) := by
    rw [Finset.disjoint_insert_right]
    refine ⟨last_notMem_castSuccPlanes _, disjoint_castSuccPlanes_preimagePlanes ?_⟩
    rwa [Finset.disjoint_singleton_right]
  refine C.le_centralizer (q2LevelCore_le_q2NbrCore τ hkJ) (q2PieceCore_le_q2NbrCore τ hkI) ?_
  intro x hx y hy
  rw [hU] at hx
  rw [hV] at hy
  exact commute_of_mem_suppGL_of_disjoint (disjoint_planeCoords hdisj)
    (siegelBlockGL_le_suppGL _ hx) (map_statedOmega_spEmbedGL_le_suppGL _ hy)

end Pieces

section Commute

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {r : ℕ}
  {τ : (Fin (r + 1) → Fˣ) →* G}

theorem q2LevelCore_le_centralizer_q2LevelCore_of_three_le [CharP F 2] (hr : 3 ≤ r)
    (hC : ∀ k, Q2FrameChart τ k) (hF : 4 ≤ Nat.card F) {i j : ℕ} (hi : i + 2 ≤ r + 1)
    (hj : j + 2 ≤ r + 1)
    (hd : Disjoint (consecutiveBlock (r + 1) i 2) (consecutiveBlock (r + 1) j 2)) :
    q2LevelCore τ (consecutiveBlock (r + 1) i 2) ≤
      centralizer (q2LevelCore τ (consecutiveBlock (r + 1) j 2) : Set G) := by
  set I := consecutiveBlock (r + 1) i 2 with hI
  set a : Fin (r + 1) := ⟨j, by omega⟩ with ha
  set b' : Fin (r + 1) := ⟨j + 1, by omega⟩ with hb
  have hJ : consecutiveBlock (r + 1) j 2 = {a, b'} := consecutiveBlock_two_eq_pair hj
  have hab : a ≠ b' := by simp [a, b', Fin.ext_iff]
  have haI : a ∉ I := fun h => Finset.disjoint_left.1 hd h (by rw [hJ]; simp)
  have hbI : b' ∉ I := fun h => Finset.disjoint_left.1 hd h (by rw [hJ]; simp)
  have hIcard : I.card = 2 := card_consecutiveBlock_two hi
  have hcent : ∀ p : Fin (r + 1), p ∉ I →
      q2LevelCore τ I ≤ centralizer (q2PieceCore τ ({p} : Finset (Fin (r + 1))) : Set G) := by
    intro p hp
    obtain ⟨k, hk⟩ := exists_splitPlane_notMem (S := insert p I)
      (by rw [Finset.card_insert_of_notMem hp, hIcard]; omega)
    rw [Finset.mem_insert, not_or] at hk
    exact (hC k).q2LevelCore_le_centralizer_q2PieceCore_of_notMem hF (by omega) hk.2 hk.1 hp
  obtain ⟨k, hk⟩ := exists_splitPlane_notMem (S := {a, b'}) (by rw [Finset.card_pair hab]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hUJ := (hC k).q2LevelCore_pair_le_sup hF hab hk.1 hk.2
  rw [hJ, Subgroup.le_centralizer_iff]
  exact hUJ.trans (sup_le (Subgroup.le_centralizer_iff.1 (hcent a haI))
    (Subgroup.le_centralizer_iff.1 (hcent b' hbI)))

theorem q2Node_le_centralizer_of_three_le [CharP F 2] (hr : 3 ≤ r) (hC : ∀ k, Q2FrameChart τ k)
    (hF : 4 ≤ Nat.card F) {i j : Fin (r + 2)} (hij : i ≠ j) (h1 : ¬ edgeD (r + 2) i j)
    (h2 : ¬ edgeD (r + 2) j i) :
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
    refine q2LevelCore_le_centralizer_q2LevelCore_of_three_le hr hC hF (by omega) (by omega) ?_
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

section Data

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem anisoCTData_of_q2FrameDataGen_of_three_le {L X : Subgroup G} {r : ℕ} (hr : 3 ≤ r)
    (hF : Nat.card F = 4) (h : Q2FrameDataGen L X r F) : AnisoCTData L X (r + 2) F := by
  obtain ⟨τ, hX, hW, ⟨π, hπ⟩, hL⟩ := h
  subst hX
  choose w hwL hw using hW
  let V₀ : Q2ValuedChart τ 0 :=
    Q2ValuedChart.ofNormalized π (fun t ht => (hπ t ht).1) (fun t ht => (hπ t ht).2)
  let C : ∀ k, Q2FrameChart τ k := fun k => (V₀.conj (hw k)).chart
  have hF4 : 4 ≤ Nat.card F := hF.ge
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hE0 : q2NbrCore τ 0 ≤ ⨆ j, q2Node (C 0) j :=
    (q2NbrCore_zero_le_iSup hr C hF' hF4).trans
      (iSup_le fun j => le_iSup (q2Node (C 0)) j.succ)
  refine ⟨q2Node (C 0), ?_, ?_, ?_, hE0, ?_⟩
  · intro i j hij h1 h2
    exact q2Node_le_centralizer_of_three_le hr C hF4 hij h1 h2
  · intro i j hij
    exact exists_theta_q2Node hr C hF4 hij
  · intro j
    obtain ⟨k, hk⟩ := exists_q2Node_le_q2NbrCore (by omega) C j
    exact hk.trans (q2NbrCore_le_anisoNeighbourJoin (l := ⟨w k, hwL k⟩)
      (map_conj_rootParam_zero (hw k)).symm)
  · exact le_iSup_q2Node_of_le hr C V₀ (V₀.conj (hw (Fin.last r))) hF' hF4 hL

end Data

end CFSG.SeitzReduction.OmegaPilot
