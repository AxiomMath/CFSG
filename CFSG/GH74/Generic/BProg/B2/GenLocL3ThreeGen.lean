module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3ThreeShape
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicExc

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial Matrix GenLocL3Pair GenLocL3Good
open scoped MatrixGroups

namespace GenLocL3Three

theorem mem_gammaAct_of_fixed {J : Type} [Group J] (D : Subgroup (MulAut J)) [Finite ↥D]
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (h4 : Nat.card ↥D = 4) (e : D) (he : e ≠ 1) {x : J}
    (hx : (e : MulAut J) x = x) : x ∈ gammaAct D.subtype := by
  set E : Subgroup ↥D := (MulAction.stabilizer (MulAut J) x).comap D.subtype with hE
  have heE : e ∈ E := by
    rw [hE, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    exact hx
  have hne : E ≠ ⊥ := fun h => he (by simpa [h] using heE)
  have hcard : 1 < Nat.card ↥E := (Subgroup.one_lt_card_iff_ne_bot E).2 hne
  have hidx : E.index ≤ 2 := by
    have h1 := Subgroup.index_mul_card E
    rw [h4] at h1
    by_contra hlt
    push Not at hlt
    have : 3 * 2 ≤ E.index * Nat.card ↥E := Nat.mul_le_mul hlt hcard
    omega
  have hadm : pRank 2 ↥D - 1 ≤ pRank 2 ↥E := (GenLocBasic.adm_iff_index hD E).2 hidx
  refine le_gammaAct D.subtype hadm ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  have := (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 ha))
  exact this

theorem diag3_mul (v u : Fin 3 → K3ˣ) : diag3 v * diag3 u = diag3 (fun i => v i * u i) := by
  apply Units.ext
  rw [Units.val_mul, coe_diag3, coe_diag3, coe_diag3, Matrix.diagonal_mul_diagonal]
  rfl

theorem cU_mul (v u : Fin 3 → K3ˣ) : cU v * cU u = cU (fun i => v i * u i) := by
  unfold cU
  rw [← map_mul, diag3_mul]

theorem crd_ne (k : Fin 3) : crd k 0 ≠ crd k 1 := by fin_cases k <;> decide

theorem crd_ne_self (k : Fin 3) (i : Fin 2) : crd k i ≠ k := by fin_cases k <;> fin_cases i <;> decide

theorem diagonal_mul_transvection (d : Fin 3 → K3) {i j : Fin 3} (hd : d i = d j) (c : K3) :
    Matrix.diagonal d * (1 + Matrix.single i j c) = (1 + Matrix.single i j c) * Matrix.diagonal d := by
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [hd, mul_comm]
  · simp [h]

theorem cT_fixes_rt (k : Fin 3) {i j : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (c : K3) :
    cT k (rt i j hij c) = rt i j hij c := by
  unfold cT cU rt
  rw [conjAut_fixed_iff, coe_diag3, CFSG.LinearGroups.coe_transvection]
  refine diagonal_mul_transvection _ ?_ c
  simp only [tauU_val, hik, hjk, ite_false]

theorem fullPair_of_cT (H : Subgroup P3) (k : Fin 3) (hk : ∀ x : P3, cT k x = x → x ∈ H) :
    FullPair H (crd k 0) (crd k 1) (crd_ne k) :=
  ⟨fun c => hk _ (cT_fixes_rt k _ (crd_ne_self k 0) (crd_ne_self k 1) c),
    fun c => hk _ (cT_fixes_rt k _ (crd_ne_self k 1) (crd_ne_self k 0) c)⟩

theorem wMat_sandwich {p q : Fin 3} (hpq : p ≠ q) (u : Fin 3 → K3) (h : u p = u q) :
    wMat p q (1 : K3) * Matrix.diagonal u * (wMat p q (1 : K3)).transpose = Matrix.diagonal u := by
  rcases (by decide : ∀ p : Fin 3, p = 0 ∨ p = 1 ∨ p = 2) p with rfl | rfl | rfl <;>
    rcases (by decide : ∀ p : Fin 3, p = 0 ∨ p = 1 ∨ p = 2) q with rfl | rfl | rfl <;>
    first | exact absurd rfl hpq | skip
  all_goals
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [wMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply] <;>
        first | exact h | exact h.symm

theorem fixed_mono (u : Fin 3 → K3ˣ) {p q : Fin 3} (hpq : p ≠ q) (h : (u p : K3) = u q) :
    (cU u * dl) (LinearFlag.proj 3 K3 (wSL p q hpq (one_ne_zero : (1 : K3) ≠ 0))) =
      LinearFlag.proj 3 K3 (wSL p q hpq (one_ne_zero : (1 : K3) ≠ 0)) := by
  unfold cU dl
  rw [conjAut_dual_fixed_iff, coe_diag3]
  exact wMat_sandwich hpq (fun i => (u i : K3)) h

theorem unit_cases : ∀ x y : K3ˣ, (x : K3) = y ∨ (x : K3) = -(y : K3) := by decide

theorem top_of_two_blocks3 (H : Subgroup P3) {k m : Fin 3} (hkm : k ≠ m)
    (hk : ∀ x : P3, cT k x = x → x ∈ H) (hm : ∀ x : P3, cT m x = x → x ∈ H) : H = ⊤ := by
  have h0 : (∀ x : P3, cT 0 x = x → x ∈ H) → FullPair H 1 2 (by decide) := fullPair_of_cT H 0
  have h1 : (∀ x : P3, cT 1 x = x → x ∈ H) → FullPair H 0 2 (by decide) := fullPair_of_cT H 1
  have h2 : (∀ x : P3, cT 2 x = x → x ∈ H) → FullPair H 0 1 (by decide) := fullPair_of_cT H 2
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl <;>
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) m with rfl | rfl | rfl
  · exact absurd rfl hkm
  · exact top_of_two_pairs (i := 2) (by decide) (h0 hk).symm (h1 hm).symm
  · exact top_of_fullPair_adj (h2 hm) (h0 hk)
  · exact top_of_two_pairs (i := 2) (by decide) (h1 hk).symm (h0 hm).symm
  · exact absurd rfl hkm
  · exact top_of_two_pairs (i := 0) (by decide) (h2 hm) (h1 hk)
  · exact top_of_fullPair_adj (h2 hk) (h0 hm)
  · exact top_of_two_pairs (i := 0) (by decide) (h2 hk) (h1 hm)
  · exact absurd rfl hkm

theorem gammaAct_subtype_rank2_three (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3)
    (hD : IsRank23 ↥D) (h4 : Nat.card ↥D = 4) : gammaAct D.subtype = ⊤ := by
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hfix : ∀ e : D, e ≠ 1 → ∀ x : P3, (e : MulAut P3) x = x → x ∈ gammaAct D.subtype :=
    fun e he x hx => mem_gammaAct_of_fixed D hD.1 h4 e he hx
  have h2 : 2 < Nat.card ↥(⊤ : Subgroup ↥D) := by rw [Subgroup.card_top, h4]; norm_num
  obtain ⟨s, -, t, -, hs, ht, hst⟩ := GenLocBasic.exists_two_ne_one h2
  obtain ⟨a, b, ha, hb, hab, -, hshape⟩ := pair_shape D hfs hD.1 s t hs ht hst
  rcases hshape with ⟨k, m, hkm, hak, hbm⟩ | ⟨k, u, hak, hbu⟩
  · exact top_of_two_blocks3 _ hkm (fun x hx => hfix a ha x (by rw [hak]; exact hx))
      (fun x hx => hfix b hb x (by rw [hbm]; exact hx))
  · have hFP := fullPair_of_cT (gammaAct D.subtype) k fun x hx => hfix a ha x (by rw [hak]; exact hx)
    have hpk : crd k 0 ≠ k := crd_ne_self k 0
    have hw : LinearFlag.proj 3 K3 (wSL (crd k 0) k hpk (one_ne_zero : (1 : K3) ≠ 0)) ∈
        gammaAct D.subtype := by
      rcases unit_cases (u (crd k 0)) (u k) with h | h
      · exact hfix b hb _ (by rw [hbu]; exact fixed_mono u hpk h)
      · have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD.1 b
        have hab1 : a * b ≠ 1 := by
          intro h1
          apply hab
          calc a = a * (b * b) := by rw [hbb, mul_one]
            _ = (a * b) * b := by rw [mul_assoc]
            _ = b := by rw [h1, one_mul]
        have hprod : ((a * b : D) : MulAut P3) = cU (fun i => tauU k i * u i) * dl := by
          rw [Subgroup.coe_mul, hak, hbu, ← mul_assoc]
          unfold cT
          rw [cU_mul]
        refine hfix (a * b) hab1 _ (by
          rw [hprod]
          refine fixed_mono (fun i => tauU k i * u i) hpk ?_
          have e1 : ((tauU k (crd k 0) : K3ˣ) : K3) = 1 := by rw [tauU_val]; simp [hpk]
          have e2 : ((tauU k k : K3ˣ) : K3) = -1 := by rw [tauU_val]; simp
          simp only [Units.val_mul, e1, e2, h]
          ring)
    have hFP2 := fullPair_of_mono (r := crd k 1) (s := crd k 0) (q := k) (hrs := (crd_ne k).symm) hpk
      (crd_ne_self k 1) (one_ne_zero : (1 : K3) ≠ 0) hw hFP.symm
    exact top_of_two_pairs hpk hFP.symm hFP2

end GenLocL3Three

end CFSG.GH74.Generic.BProg.B2
