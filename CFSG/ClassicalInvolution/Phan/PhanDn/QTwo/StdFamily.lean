module

import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamilyRev4
import CFSG.ClassicalInvolution.Phan.PhanDn.PanelStab
import CFSG.LocalAnalysis.StandardType.GGQTwoDModelMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.StandardType.QTwo

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

section General

variable {f : ℕ} (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem qts_stdConj_mem_orthDerived {m : ℕ}
    {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    (hg : g ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :
    (stdConj E m) g ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  have hcoe : ((conjTau (E := E) (m := m) ⟨g, hg⟩ :
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = (stdConj E m) g := by
    rw [coe_conjTau, stdConj, MulAut.conj_apply, stdTau]
  rw [← hcoe]
  exact (conjTau (E := E) (m := m) ⟨g, hg⟩).2

theorem stdFamilyV_ι_mem_orthDerived (m : ℕ) (hm : 3 ≤ m) (k : Fin (m + 1))
    (a : Su K 2 f 2) :
    (stdFamilyV E m hm).ι k a ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) k with ⟨k', rfl⟩ | rfl
  · rw [stdFamilyV_ι, stdIota_castSucc]
    unfold stdChainIota
    exact suEndN_mem_orthDerived E (by omega) (blockEmb2 K 2 f m k' a)
  · rw [stdFamilyV_ι, stdIota_last]
    unfold stdForkIota stdChainIota
    exact qts_stdConj_mem_orthDerived E
      (suEndN_mem_orthDerived E (by omega) (blockEmb2 K 2 f m ⟨m - 1, by omega⟩ a))

theorem stdFamilyV_θ_mem_orthDerived (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1))
    (a : Su K 2 f 3) :
    (stdFamilyV E m hm).θ i j a ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · rw [stdFamilyV_θ, stdTheta_castSucc]
    unfold stdThetaAt
    split_ifs with h
    · unfold stdChainTheta
      exact suEndN_mem_orthDerived E (by omega)
        (blockEmb3 K 2 f m ⟨i.val, by omega⟩ (by show i.val + 1 < m; omega) a)
    · exact Subgroup.one_mem _
  · rw [stdFamilyV_θ, stdTheta_last]
    unfold stdForkTheta stdChainTheta
    exact qts_stdConj_mem_orthDerived E
      (suEndN_mem_orthDerived E (by omega)
        (blockEmb3 K 2 f m ⟨m - 2, by omega⟩ (by show m - 2 + 1 < m; omega) a))

end General

variable (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] noncomputable def qTwoStdIota (m : ℕ) (hm : 3 ≤ m) (k : Fin (m + 1)) :
    Su K 2 1 2 →* ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  ((stdFamilyV E m hm).ι k).codRestrict _ (stdFamilyV_ι_mem_orthDerived E m hm k)

@[expose] noncomputable def qTwoStdTheta₀ (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    Su K 2 1 3 →* ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  ((stdFamilyV E m hm).θ i j).codRestrict _ (stdFamilyV_θ_mem_orthDerived E m hm i j)

@[expose] noncomputable def qTwoStdTheta (m : ℕ) (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    Su K 2 1 3 →* ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
  if i < j then qTwoStdTheta₀ E m hm i j
  else (qTwoStdTheta₀ E m hm j i).comp (revSU3 K 2 1).toMonoidHom

theorem coe_qTwoStdIota (m : ℕ) (hm : 3 ≤ m) (k : Fin (m + 1)) (a : Su K 2 1 2) :
    ((qTwoStdIota E m hm k a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = (stdFamilyV E m hm).ι k a := by
  rfl

theorem coe_qTwoStdTheta_of_lt (m : ℕ) (hm : 3 ≤ m) {i j : Fin (m + 1)} (h : i < j)
    (a : Su K 2 1 3) :
    ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = (stdFamilyV E m hm).θ i j a := by
  rw [qTwoStdTheta, if_pos h]
  rfl

private theorem qts_label_three_symm {m : ℕ} {i j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 :=
  ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j).trans h

theorem qTwoStdTheta_of_gt (m : ℕ) (hm : 3 ≤ m) {i j : Fin (m + 1)} (h : j < i) :
    qTwoStdTheta E m hm i j = (qTwoStdTheta E m hm j i).comp (revSU3 K 2 1).toMonoidHom := by
  rw [qTwoStdTheta, if_neg (not_lt.mpr (le_of_lt h)), qTwoStdTheta, if_pos h]

theorem coe_qTwoStdIota_castSucc (m : ℕ) (hm : 3 ≤ m) (k : Fin m) (a : Su K 2 1 2) :
    ((qTwoStdIota E m hm (Fin.castSucc k) a :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) (blockEmb2 K 2 1 m k a) := by
  rw [coe_qTwoStdIota, stdFamilyV_ι_castSucc]
  rfl

theorem coe_qTwoStdIota_last (m : ℕ) (hm : 3 ≤ m) (a : Su K 2 1 2) :
    ((qTwoStdIota E m hm (Fin.last m) a :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      stdConj E m
        (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb2 K 2 1 m ⟨m - 1, by omega⟩ a)) := by
  rw [coe_qTwoStdIota, stdFamilyV_ι_last]
  rfl

theorem coe_qTwoStdTheta_chain (m : ℕ) (hm : 3 ≤ m) {i : Fin (m + 1)} {j : Fin m}
    (h : i.val + 1 = j.val) (b : Su K 2 1 3) :
    ((qTwoStdTheta E m hm i (Fin.castSucc j) b :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb3 K 2 1 m ⟨i.val, by have := j.2; omega⟩
          (by have := j.2; simp only; omega) b) := by
  have hij : i < Fin.castSucc j := by
    rw [Fin.lt_def]
    simp only [Fin.val_castSucc]
    omega
  rw [coe_qTwoStdTheta_of_lt E m hm hij, stdFamilyV_θ, stdTheta_castSucc]
  unfold stdThetaAt
  rw [dif_pos h]
  rfl

theorem coe_qTwoStdTheta_fork (m : ℕ) (hm : 3 ≤ m) (b : Su K 2 1 3) :
    ((qTwoStdTheta E m hm ⟨m - 2, by omega⟩ (Fin.last m) b :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      stdConj E m
        (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb3 K 2 1 m ⟨m - 2, by omega⟩
            (by simp only; omega) b)) := by
  have hij : (⟨m - 2, by omega⟩ : Fin (m + 1)) < Fin.last m := by
    rw [Fin.lt_def]
    simp only [Fin.val_last]
    omega
  rw [coe_qTwoStdTheta_of_lt E m hm hij, stdFamilyV_θ, stdTheta_last]
  unfold stdForkTheta stdChainTheta
  rfl


private theorem qts_win_mem_orthDerived {m a len : ℕ} (hm : 3 ≤ m)
    (h : a + len ≤ m + 1) (A : Su K 2 1 len) :
    qtwoStdWin (F := F) (K := K) m a len h A ∈
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  unfold qtwoStdWin
  exact suEndN_mem_orthDerived E (by omega) (blockEmb K 2 1 (m + 1) len a h A)

private theorem qts_win_three_congr {m a a' : ℕ} (ha : a = a')
    (h : a + 3 ≤ m + 1) (h' : a' + 3 ≤ m + 1) :
    qtwoStdWin (F := F) (K := K) m a 3 h =
      qtwoStdWin (F := F) (K := K) m a' 3 h' := by
  subst ha
  rfl

private theorem qts_win_range_le_orthDerived {m a len : ℕ} (hm : 3 ≤ m)
    (h : a + len ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a len h).range ≤
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  rintro y ⟨A, rfl⟩
  exact qts_win_mem_orthDerived E hm h A

private theorem qts_stdTheta_eq_win_chain {m a : ℕ} (hm : 3 ≤ m) (ha : a + 2 ≤ m)
    (i j : Fin (m + 1)) (hi : i.val = a) (hj : j.val = a + 1) :
    (stdFamilyV E m hm).θ i j =
      qtwoStdWin (F := F) (K := K) m a 3 (by omega) := by
  obtain ⟨ai, hii⟩ := i
  obtain ⟨aj, hij⟩ := j
  have hia : ai = a := hi
  have hja : aj = a + 1 := hj
  subst ai
  subst aj
  have hjcast : (⟨a + 1, hij⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨a + 1, by omega⟩ : Fin m) := rfl
  rw [stdFamilyV_θ]
  conv_lhs => rw [hjcast]
  rw [stdTheta_castSucc]
  unfold stdThetaAt
  rw [dif_pos (by show a + 1 = a + 1; omega)]
  unfold stdChainTheta qtwoStdWin
  rfl

private theorem qts_stdTheta_eq_fork {m : ℕ} (hm : 3 ≤ m) (i j : Fin (m + 1))
    (hj : j.val = m) :
    (stdFamilyV E m hm).θ i j =
      (stdConj E m).toMonoidHom.comp
        (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)) := by
  obtain ⟨aj, hlt⟩ := j
  have hja : aj = m := hj
  subst aj
  have hjlast : (⟨m, hlt⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [stdFamilyV_θ]
  conv_lhs => rw [hjlast]
  rw [stdTheta_last]
  unfold stdForkTheta stdChainTheta qtwoStdWin
  rfl

private theorem qts_win_comp_blk012 (m a : ℕ) (h4 : a + 4 ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a 4 h4).comp (blk012 K) =
      qtwoStdWin (F := F) (K := K) m a 3 (by omega) := by
  apply MonoidHom.ext
  intro A
  simp only [MonoidHom.comp_apply, qtwoStdWin]
  rw [show blk012 K = blockEmb K 2 1 4 3 0 (by norm_num) from rfl]
  rw [blockEmb_comp_apply]
  rfl

private theorem qts_win_comp_blk123 (m a : ℕ) (h4 : a + 4 ≤ m + 1) :
    (qtwoStdWin (F := F) (K := K) m a 4 h4).comp (blk123 K) =
      qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega) := by
  apply MonoidHom.ext
  intro A
  simp only [MonoidHom.comp_apply, qtwoStdWin]
  rw [show blk123 K = blockEmb K 2 1 4 3 1 (by norm_num) from rfl]
  rw [blockEmb_comp_apply]

private theorem qts_theta_gl_chain {m a : ℕ} (hm : 3 ≤ m) (ha : a + 2 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j) (hi : i.val = a) (hj : j.val = a + 1)
    (A : Su K 2 1 3) :
    ((qTwoStdTheta E m hm i j A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      qtwoStdWin (F := F) (K := K) m a 3 (by omega) A := by
  rw [coe_qTwoStdTheta_of_lt E m hm hij]
  exact DFunLike.congr_fun (qts_stdTheta_eq_win_chain E hm ha i j hi hj) A

private theorem qts_theta_gl_chain_rev {m a : ℕ} (hm : 3 ≤ m) (ha : a + 2 ≤ m)
    {i j : Fin (m + 1)} (hji : j < i) (hi : i.val = a + 1) (hj : j.val = a)
    (A : Su K 2 1 3) :
    ((qTwoStdTheta E m hm i j A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      qtwoStdWin (F := F) (K := K) m a 3 (by omega) (revSU3 K 2 1 A) := by
  rw [qTwoStdTheta_of_gt E m hm hji, MonoidHom.comp_apply,
    coe_qTwoStdTheta_of_lt E m hm hji]
  exact DFunLike.congr_fun (qts_stdTheta_eq_win_chain E hm ha j i hj hi) (revSU3 K 2 1 A)

private theorem qts_theta_gl_fork {m : ℕ} (hm : 3 ≤ m) {j k : Fin (m + 1)} (hjk : j < k)
    (hj : j.val = m - 2) (hk : k.val = m) (A : Su K 2 1 3) :
    ((qTwoStdTheta E m hm j k A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) A) := by
  rw [coe_qTwoStdTheta_of_lt E m hm hjk]
  exact DFunLike.congr_fun (qts_stdTheta_eq_fork E hm j k hk) A

private theorem qts_theta_gl_fork_rev {m : ℕ} (hm : 3 ≤ m) {j k : Fin (m + 1)} (hkj : k < j)
    (hj : j.val = m) (hk : k.val = m - 2) (A : Su K 2 1 3) :
    ((qTwoStdTheta E m hm j k A :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
        (revSU3 K 2 1 A)) := by
  rw [qTwoStdTheta_of_gt E m hm hkj, MonoidHom.comp_apply,
    coe_qTwoStdTheta_of_lt E m hm hkj]
  exact DFunLike.congr_fun (qts_stdTheta_eq_fork E hm k j hj) (revSU3 K 2 1 A)

private theorem qts_forkHom_mem {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 4)
    {θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))}
    (h1 : ∀ h : Su K 2 1 3, θ (blockEmb K 2 1 4 3 1 (by norm_num) h) =
      qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h)
    (h0 : ∀ h : Su K 2 1 3, θ (blockEmb K 2 1 4 3 0 (by norm_num) h) =
      (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
        (revSU3 K 2 1 h))) :
    ∀ x : Su K 2 1 4, θ x ∈
      CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) := by
  have hcomp1 : θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) := by
    apply MonoidHom.ext
    intro h
    exact h1 h
  have hcomp0 : θ.comp (blockEmb K 2 1 4 3 0 (by norm_num)) =
      (stdConj E m).toMonoidHom.comp
        ((qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).comp
          (revSU3 K 2 1).toMonoidHom) := by
    apply MonoidHom.ext
    intro h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact h0 h
  have hcomp0range : (θ.comp (blockEmb K 2 1 4 3 0 (by norm_num))).range =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
        (stdConj E m).toMonoidHom := by
    rw [hcomp0, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (revSU3 K 2 1).surjective, Subgroup.map_top]
  have hrange : θ.range =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range ⊔
        (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
          (stdConj E m).toMonoidHom := by
    rw [MonoidHom.range_eq_map θ, ← blockEmb_three_sup_eq_top hK, Subgroup.map_sup,
      ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 0 (by norm_num)),
      ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 1 (by norm_num)),
      hcomp0range, hcomp1, sup_comm]
  intro x
  have hx : θ x ∈ θ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  rw [hrange] at hx
  refine (sup_le (qts_win_range_le_orthDerived E hm (by omega)) ?_) hx
  rintro y ⟨z, hz, rfl⟩
  exact qts_stdConj_mem_orthDerived E (qts_win_range_le_orthDerived E hm (by omega) hz)

private theorem qts_theta_mem_qtwoStdW {m : ℕ} (hm : 3 ≤ m) {j k : Fin (m + 1)}
    (h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j k = 3) (b : Su K 2 1 3) :
    ((qTwoStdTheta E m hm j k b :
        ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈ qtwoStdW E m hm j k := by
  have hne : j ≠ k := by
    rintro rfl
    rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at h1
    omega
  by_cases hlt : j < k
  · rw [coe_qTwoStdTheta_of_lt E m hm hlt b]
    unfold qtwoStdW
    rw [if_pos h1, if_pos hlt]
    exact ⟨b, rfl⟩
  · have hkj : k < j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    rw [qTwoStdTheta_of_gt E m hm hkj]
    unfold qtwoStdW
    rw [if_pos h1, if_neg (not_lt.mpr (le_of_lt hkj))]
    refine ⟨revSU3 K 2 1 b, ?_⟩
    rw [MonoidHom.comp_apply, coe_qTwoStdTheta_of_lt E m hm hkj]
    rfl

@[expose] noncomputable def qTwoStdFamily (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    QTwoPhanFamily K (CFSG.StandardType.ggCoxeterMatrixD (m + 1))
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) where
  ι := qTwoStdIota E m hm
  θ := qTwoStdTheta E m hm
  left i j hM := by
    have hne : i ≠ j := by
      rintro rfl
      rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at hM
      omega
    rcases lt_or_gt_of_ne hne with hij | hji
    · apply MonoidHom.ext
      intro a
      apply Subtype.ext
      rw [MonoidHom.comp_apply,
        coe_qTwoStdTheta_of_lt E m hm hij (embSUid (unitaryInvolution K 2 1) 2 a),
        coe_qTwoStdIota]
      exact DFunLike.congr_fun ((stdFamilyV E m hm).left i j hij hM) a
    · rw [qTwoStdTheta_of_gt E m hm hji, MonoidHom.comp_assoc, revSU3_comp_embSUid_two K 2 1,
        qTwoStdTheta, if_pos hji]
      apply MonoidHom.ext
      intro a
      apply Subtype.ext
      rw [MonoidHom.comp_apply, coe_qTwoStdIota]
      exact DFunLike.congr_fun ((stdFamilyV E m hm).right j i hji
        (qts_label_three_symm hM)) a
  right i j hM := by
    have hne : i ≠ j := by
      rintro rfl
      rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at hM
      omega
    rcases lt_or_gt_of_ne hne with hij | hji
    · apply MonoidHom.ext
      intro a
      apply Subtype.ext
      rw [MonoidHom.comp_apply,
        coe_qTwoStdTheta_of_lt E m hm hij (embSUid (unitaryInvolution K 2 1) 0 a),
        coe_qTwoStdIota]
      exact DFunLike.congr_fun ((stdFamilyV E m hm).right i j hij hM) a
    · rw [qTwoStdTheta_of_gt E m hm hji, MonoidHom.comp_assoc, revSU3_comp_embSUid_zero K 2 1,
        qTwoStdTheta, if_pos hji]
      apply MonoidHom.ext
      intro a
      apply Subtype.ext
      rw [MonoidHom.comp_apply, coe_qTwoStdIota]
      exact DFunLike.congr_fun ((stdFamilyV E m hm).left j i hji
        (qts_label_three_symm hM)) a
  rev i j hM := by
    have hne : i ≠ j := by
      rintro rfl
      rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl] at hM
      omega
    have hK' : Nat.card K = (2 ^ 1) ^ 2 := by
      rw [hK]
      norm_num
    rcases lt_or_gt_of_ne hne with hij | hji
    · rw [qTwoStdTheta, if_neg (not_lt.mpr (le_of_lt hij)), qTwoStdTheta, if_pos hij]
    · rw [qTwoStdTheta, if_pos hji, qTwoStdTheta, if_neg (not_lt.mpr (le_of_lt hji))]
      apply MonoidHom.ext
      intro a
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [revSU3_revSU3 K 2 1 hK' a]
  comm i j h a b := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, coe_qTwoStdIota] using (stdFamilyV E m hm).comm i j h a b
  a3 i j k h1 h2 h3 := by
    rcases qtwo_A3_cases m i j k h1 h2 h3 with
      ⟨a, ha, ⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩⟩ |
        (⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩) | (⟨hi, hj, hk⟩ | ⟨hi, hj, hk⟩)
    ·
      have hmem : ∀ A : Su K 2 1 4,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) A ∈
            CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        fun A => qts_win_mem_orthDerived E hm (by omega) A
      have h012 : (qtwoStdWin (F := F) (K := K) m a 4 (by omega)).comp (blk012 K) =
          qtwoStdWin (F := F) (K := K) m a 3 (by omega) :=
        qts_win_comp_blk012 m a (by omega)
      have h123 : (qtwoStdWin (F := F) (K := K) m a 4 (by omega)).comp (blk123 K) =
          qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega) :=
        qts_win_comp_blk123 m a (by omega)
      have h012p : ∀ A : Su K 2 1 3,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) (blk012 K A) =
            qtwoStdWin (F := F) (K := K) m a 3 (by omega) A :=
        fun A => DFunLike.congr_fun h012 A
      have h123p : ∀ A : Su K 2 1 3,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) (blk123 K A) =
            qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega) A :=
        fun A => DFunLike.congr_fun h123 A
      refine ⟨(qtwoStdWin (F := F) (K := K) m a 4 (by omega)).codRestrict _ hmem,
        ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [h012p A]
        exact (qts_theta_gl_chain E hm (by omega)
          (by rw [Fin.lt_def]; omega) hi hj A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [h123p A]
        exact (qts_theta_gl_chain E hm (by omega)
          (by rw [Fin.lt_def]; omega) hj hk A).symm
    ·
      have hmem : ∀ A : Su K 2 1 4,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) A ∈
            CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        fun A => qts_win_mem_orthDerived E hm (by omega) A
      have h012 : (qtwoStdWin (F := F) (K := K) m a 4 (by omega)).comp (blk012 K) =
          qtwoStdWin (F := F) (K := K) m a 3 (by omega) :=
        qts_win_comp_blk012 m a (by omega)
      have h123 : (qtwoStdWin (F := F) (K := K) m a 4 (by omega)).comp (blk123 K) =
          qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega) :=
        qts_win_comp_blk123 m a (by omega)
      have h012p : ∀ A : Su K 2 1 3,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) (blk012 K A) =
            qtwoStdWin (F := F) (K := K) m a 3 (by omega) A :=
        fun A => DFunLike.congr_fun h012 A
      have h123p : ∀ A : Su K 2 1 3,
          qtwoStdWin (F := F) (K := K) m a 4 (by omega) (blk123 K A) =
            qtwoStdWin (F := F) (K := K) m (a + 1) 3 (by omega) A :=
        fun A => DFunLike.congr_fun h123 A
      have hrev0 : ∀ A0, (revSU4 K).toMonoidHom (blk012 K A0) = blk123 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk012 K) A0
      have hrev1 : ∀ A0, (revSU4 K).toMonoidHom (blk123 K A0) = blk012 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk123 K) A0
      refine ⟨((qtwoStdWin (F := F) (K := K) m a 4 (by omega)).codRestrict _ hmem).comp
        (revSU4 K).toMonoidHom, ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev0 A, h123p (revSU3 K 2 1 A)]
        exact (qts_theta_gl_chain_rev E hm (by omega)
          (by rw [Fin.lt_def]; omega) hi hj A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev1 A, h012p (revSU3 K 2 1 A)]
        exact (qts_theta_gl_chain_rev E hm (by omega)
          (by rw [Fin.lt_def]; omega) hj hk A).symm
    ·
      have hmem : ∀ A : Su K 2 1 4,
          ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))) A ∈
            CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        fun A => qts_stdConj_mem_orthDerived E
          (qts_win_mem_orthDerived E hm (by omega) A)
      have h012 : ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).comp (blk012 K) =
          qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega) := by
        rw [MonoidHom.comp_assoc, qts_win_comp_blk012 m (m - 3) (by omega)]
        apply MonoidHom.ext
        intro A
        exact qtwoStdConj_win E (a := m - 3) (k := 3) (by omega) A
      have h123 : ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).comp (blk123 K) =
          (stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)) := by
        rw [MonoidHom.comp_assoc, qts_win_comp_blk123 m (m - 3) (by omega)]
        rw [qts_win_three_congr (m := m) (a := (m - 3) + 1) (a' := m - 2)
          (by omega) (by omega) (by omega)]
      have h012p : ∀ A : Su K 2 1 3,
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega)
            (blk012 K A)) =
            qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega) A :=
        fun A => DFunLike.congr_fun h012 A
      have h123p : ∀ A : Su K 2 1 3,
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega)
            (blk123 K A)) =
            (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) A) :=
        fun A => DFunLike.congr_fun h123 A
      have hj' : j.val = (m - 3) + 1 := by omega
      refine ⟨((stdConj E m).toMonoidHom.comp
        (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).codRestrict _ hmem,
        ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [h012p A]
        exact (qts_theta_gl_chain (a := m - 3) E hm (by omega)
          (by rw [Fin.lt_def]; omega) hi hj' A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [h123p A]
        exact (qts_theta_gl_fork E hm (by rw [Fin.lt_def]; omega) hj hk A).symm
    ·
      have hmem : ∀ A : Su K 2 1 4,
          ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))) A ∈
            CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        fun A => qts_stdConj_mem_orthDerived E
          (qts_win_mem_orthDerived E hm (by omega) A)
      have h012 : ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).comp (blk012 K) =
          qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega) := by
        rw [MonoidHom.comp_assoc, qts_win_comp_blk012 m (m - 3) (by omega)]
        apply MonoidHom.ext
        intro A
        exact qtwoStdConj_win E (a := m - 3) (k := 3) (by omega) A
      have h123 : ((stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).comp (blk123 K) =
          (stdConj E m).toMonoidHom.comp
            (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)) := by
        rw [MonoidHom.comp_assoc, qts_win_comp_blk123 m (m - 3) (by omega)]
        rw [qts_win_three_congr (m := m) (a := (m - 3) + 1) (a' := m - 2)
          (by omega) (by omega) (by omega)]
      have h012p : ∀ A : Su K 2 1 3,
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega)
            (blk012 K A)) =
            qtwoStdWin (F := F) (K := K) m (m - 3) 3 (by omega) A :=
        fun A => DFunLike.congr_fun h012 A
      have h123p : ∀ A : Su K 2 1 3,
          (stdConj E m).toMonoidHom (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega)
            (blk123 K A)) =
            (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) A) :=
        fun A => DFunLike.congr_fun h123 A
      have hrev0 : ∀ A0, (revSU4 K).toMonoidHom (blk012 K A0) = blk123 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk012 K) A0
      have hrev1 : ∀ A0, (revSU4 K).toMonoidHom (blk123 K A0) = blk012 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk123 K) A0
      have hj' : j.val = (m - 3) + 1 := by omega
      refine ⟨(((stdConj E m).toMonoidHom.comp
        (qtwoStdWin (F := F) (K := K) m (m - 3) 4 (by omega))).codRestrict _ hmem).comp
        (revSU4 K).toMonoidHom, ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev0 A, h123p (revSU3 K 2 1 A)]
        exact (qts_theta_gl_fork_rev E hm (by rw [Fin.lt_def]; omega) hi hj A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev1 A, h012p (revSU3 K 2 1 A)]
        exact (qts_theta_gl_chain_rev (a := m - 3) E hm (by omega)
          (by rw [Fin.lt_def]; omega) hj' hk A).symm
    ·
      obtain ⟨θ, hθ1, hθ0⟩ := qtwoStd_forkHom_exists E m hm
      have hmem : ∀ x : Su K 2 1 4,
          θ x ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        qts_forkHom_mem E hm hK hθ1 hθ0
      have hK' : Nat.card K = (2 ^ 1) ^ 2 := by
        rw [hK]
        norm_num
      have hrev0 : ∀ A0, (revSU4 K).toMonoidHom (blk012 K A0) = blk123 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk012 K) A0
      have hrev1 : ∀ A0, (revSU4 K).toMonoidHom (blk123 K A0) = blk012 K (revSU3 K 2 1 A0) :=
        fun A0 => DFunLike.congr_fun (revSU4_comp_blk123 K) A0
      have hf1 : ∀ A0, θ (blk123 K A0) =
          qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) A0 := by
        intro A0
        change θ (blockEmb K 2 1 4 3 1 (by norm_num) A0) = _
        exact hθ1 A0
      have hf0 : ∀ A0, θ (blk012 K A0) =
          (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
            (revSU3 K 2 1 A0)) := by
        intro A0
        change θ (blockEmb K 2 1 4 3 0 (by norm_num) A0) = _
        exact hθ0 A0
      have hi' : i.val = (m - 2) + 1 := by omega
      refine ⟨(θ.codRestrict _ hmem).comp (revSU4 K).toMonoidHom, ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev0 A, hf1 (revSU3 K 2 1 A)]
        exact (qts_theta_gl_chain_rev (a := m - 2) E hm (by omega)
          (by rw [Fin.lt_def]; omega) hi' hj A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hrev1 A, hf0 (revSU3 K 2 1 A)]
        rw [revSU3_revSU3 K 2 1 hK' A]
        exact (qts_theta_gl_fork E hm (by rw [Fin.lt_def]; omega) hj hk A).symm
    ·
      obtain ⟨θ, hθ1, hθ0⟩ := qtwoStd_forkHom_exists E m hm
      have hmem : ∀ x : Su K 2 1 4,
          θ x ∈ CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)) :=
        qts_forkHom_mem E hm hK hθ1 hθ0
      have hf1 : ∀ A0, θ (blk123 K A0) =
          qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) A0 := by
        intro A0
        change θ (blockEmb K 2 1 4 3 1 (by norm_num) A0) = _
        exact hθ1 A0
      have hf0 : ∀ A0, θ (blk012 K A0) =
          (stdConj E m) (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)
            (revSU3 K 2 1 A0)) := by
        intro A0
        change θ (blockEmb K 2 1 4 3 0 (by norm_num) A0) = _
        exact hθ0 A0
      have hk' : k.val = (m - 2) + 1 := by omega
      refine ⟨θ.codRestrict _ hmem, ?_, ?_⟩
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hf0 A]
        exact (qts_theta_gl_fork_rev E hm (by rw [Fin.lt_def]; omega) hi hj A).symm
      · apply MonoidHom.ext
        intro A
        apply Subtype.ext
        simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_mk]
        rw [hf1 A]
        exact (qts_theta_gl_chain (a := m - 2) E hm (by omega)
          (by rw [Fin.lt_def]; omega) hj hk' A).symm
  farNodeEdge i j k h1 h2 h3 a b := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, coe_qTwoStdIota] using
      qtwoStd_farNodeEdge E m hm i j k h1 h2 h3
        ((stdFamilyV E m hm).ι i a) ⟨a, rfl⟩
        ((qTwoStdTheta E m hm j k b :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qts_theta_mem_qtwoStdW E hm h1 b)
  farEdgeEdge i k j l h1 h2 h3 h4 h5 h6 a b := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      qtwoStd_farEdgeEdge E m hm i k j l h1 h2 h3 h4 h5 h6
        ((qTwoStdTheta E m hm i k a :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qts_theta_mem_qtwoStdW E hm h1 a)
        ((qTwoStdTheta E m hm j l b :
          ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
          (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (qts_theta_mem_qtwoStdW E hm h2 b)

end CFSG.ClassicalInvolution.PhanDn.QTwo
