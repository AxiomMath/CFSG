module

public import CFSG.ClassicalInvolution.Q3.TL4VtxMainB
public import CFSG.ClassicalInvolution.Q3.TL4OddFrRoute

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

variable {n : ℕ}

theorem hyp51_triFrame_of_thm5 (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hE4 : E4AutOddFreeR) :
    ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y),
      TightLargeHypR 3 n Y Rd Sd z →
        ∀ (M : Fin 3 → Subgroup Y) (x : Fin 3 → Y) (P : Fin 3 → Subgroup Y),
          TriFrame (CoreAssembly.conjClass (tightCore Rd)) M x P →
            x 2 ∉ Subgroup.closure ({x 0, x 1} : Set Y) →
              Hyp51 (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) := by
  intro Y _ _ Rd Sd z hL M x P hF hx2
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have hΩR := TightLargeHypR.typeRFam hL
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) L, L' = L := fun L hL' =>
    T8.noTwins_of_mem hΩ.conjInvariant (fun J hJ => hJ) (fun K' hK' => by
      rw [hd.twinSet_eq] at hK'
      exact hK') hL'
  have hcomm : ∀ i j : Fin 3, x i * x j = x j * x i := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    · exact Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ (hF.inv i) (hF.nbr i j hij) (hF.inv j)
  have hBe : IsElemAbelian 2 (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) :=
    T8T.isElemAbelian_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2)
  have hB8 : Nat.card ↥(Subgroup.closure ({x 0, x 1, x 2} : Set Y)) = 8 :=
    T8T.natCard_closure_three (hF.sq 0) (hF.sq 1) (hF.sq 2) (hcomm 0 1) (hcomm 0 2) (hcomm 1 2)
      (hF.ne_one 0) (hF.ne_one 1) (hF.x_ne hnt (by decide)) (hF.ne_one 2) hx2
  have hBelow : CIT3Below (Nat.card Y) := by
    rw [hL.card]
    exact hL.below
  have hmem3 : ∀ {w : Y}, w ∈ ({x 0, x 1} : Set Y) →
      w ∈ Subgroup.closure ({x 0, x 1} : Set Y) := fun hw => Subgroup.subset_closure hw
  refine ⟨hBe, hB8, fun c hcB hc1 => ?_⟩
  have hpair : ∀ i j : Fin 3, i ≠ j →
      Subgroup.closure ({x 0, x 1, x 2} : Set Y) = Subgroup.closure ({x i, x j, c} : Set Y) →
      x i ≠ c → x j ≠ c → x i * x j ≠ c →
        Hyp51At (Subgroup.closure ({x 0, x 1, x 2} : Set Y)) c := by
    intro i j hij hgen hic hjc hijc
    have hPc : P j ≤ Subgroup.centralizer ({c} : Set Y) := fun p hp => by
      have hle : Subgroup.closure ({x 0, x 1, x 2} : Set Y) ≤
          Subgroup.centralizer ({p} : Set Y) := by
        rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl) <;>
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (hF.cent j _ hp)).symm
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (hle hcB)).symm
    have hPN : P j ≤ Subgroup.normalizer (M i : Set Y) :=
      (hF.cent j i).trans (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
        (hnt _ (hF.mem i)) (hF.inv i))
    exact hyp51At_of_vtxPair h4 h5 htw hE4 hBelow hL.center hL.card.le hΩR hBe hgen hc1
      (hF.ne_one i) hic (hF.ne_one j) hjc (hF.x_ne hnt hij) hijc
      (xMem_of_triFrame_of_mem hΩ hnt hF hcB i) (xMem_of_triFrame_of_mem hΩ hnt hF hcB j)
      (hF.inv i) (hF.inv j) (hF.syl j) hPc hPN
  by_cases hm0 : c = x 0
  · subst hm0
    refine hpair 1 2 (by decide) ?_ (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    · congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · intro h
      apply hx2
      have e : x 2 = x 1 * x 0 := by
        calc x 2 = x 1 * (x 1 * x 2) := by rw [← mul_assoc, hF.sq 1, one_mul]
          _ = x 1 * x 0 := by rw [h]
      rw [e]
      exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  by_cases hm1 : c = x 1
  · subst hm1
    refine hpair 0 2 (by decide) ?_ (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    · congr 1
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · intro h
      apply hx2
      have e : x 2 = x 0 * x 1 := by
        calc x 2 = x 0 * (x 0 * x 2) := by rw [← mul_assoc, hF.sq 0, one_mul]
          _ = x 0 * x 1 := by rw [h]
      rw [e]
      exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  by_cases hm2 : c = x 2
  · subst hm2
    refine hpair 0 1 (by decide) rfl (hF.x_ne hnt (by decide)) (hF.x_ne hnt (by decide)) ?_
    intro h
    apply hx2
    rw [← h]
    exact Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp))
  have hmem : ∀ i, c ≠ x i := by
    intro i
    fin_cases i
    exacts [hm0, hm1, hm2]
  rcases mem_closure_three_cases (hF.sq 2) (hcomm 0 2) (hcomm 1 2) hcB with hc01 | ⟨e, he, rfl⟩
  · have hc : c = x 0 * x 1 := by
      rcases TypeCSetup.mem_closure_pair (hF.sq 0) (hF.sq 1) (hcomm 0 1) hc01 with
        h | h | h | h
      · exact absurd h hc1
      · exact absurd h (hmem 0)
      · exact absurd h (hmem 1)
      · exact h
    subst hc
    refine hpair 0 2 (by decide) ?_ (fun h => hmem 0 h.symm) (fun h => hmem 2 h.symm) ?_
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact Subgroup.subset_closure (by simp)
        · have h1 : x 0 * (x 0 * x 1) ∈ Subgroup.closure ({x 0, x 2, x 0 * x 1} : Set Y) :=
            Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
          rwa [← mul_assoc, hF.sq 0, one_mul] at h1
        · exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact mem_triFrame_closure 0
        · exact mem_triFrame_closure 2
        · exact Subgroup.mul_mem _ (mem_triFrame_closure 0) (mem_triFrame_closure 1)
    · intro h
      exact hF.x_ne hnt (show (2 : Fin 3) ≠ 1 by decide) (mul_left_cancel h)
  · refine hpair 0 1 (by decide) ?_ (fun h => hmem 0 h.symm) (fun h => hmem 1 h.symm) ?_
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · have heR : e ∈ Subgroup.closure ({x 0, x 1, e * x 2} : Set Y) :=
            Subgroup.closure_mono (by intro w hw; rcases hw with rfl | rfl <;> simp) he
          have h1 : e⁻¹ * (e * x 2) ∈ Subgroup.closure ({x 0, x 1, e * x 2} : Set Y) :=
            Subgroup.mul_mem _ (Subgroup.inv_mem _ heR) (Subgroup.subset_closure (by simp))
          rwa [inv_mul_cancel_left] at h1
      · rw [Subgroup.closure_le]
        rintro w (rfl | rfl | rfl)
        · exact mem_triFrame_closure 0
        · exact mem_triFrame_closure 1
        · refine Subgroup.mul_mem _ ?_ (mem_triFrame_closure 2)
          exact Subgroup.closure_mono (by
            intro w hw
            rcases hw with rfl | rfl <;> simp) he
    · intro h
      apply hx2
      have e2 : x 2 = e⁻¹ * (x 0 * x 1) := by rw [h]; group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ he)
        (Subgroup.mul_mem _ (hmem3 (by simp)) (hmem3 (by simp)))

theorem tightHyp51TriR_three_of_thm5 (h4 : Thm4RBelow 3 n) (h5 : Thm5RBelowF 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetBelow n) (hE4 : E4AutOddFreeR) :
    TightHyp51TriR 3 n :=
  fun Y _ _ Rd Sd z hL M x P hF hx => hyp51_triFrame_of_thm5 h4 h5 htw hE4 Y Rd Sd z hL M x P hF hx

end CFSG.ClassicalInvolution.Q3.TL4
