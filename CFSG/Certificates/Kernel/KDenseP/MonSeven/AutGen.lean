module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
public import CFSG.Certificates.Kernel.MonsterPcSeven.Coll
public import Certificates.Kernel.MonsterPcSeven.Fus

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.KDenseP.MonSeven.AutGen

open CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks _root_.Timmesfeld.Mon7
  CFSG.KC.MonPcSeven
open CFSG.KC.BM.PcFive (V6 QV nth psi nfQ)

theorem gw_powL (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k := by
  induction k with
  | zero => simp [powL, gw_nil]
  | succ k ih =>
    have hs : powL (k + 1) w = w ++ powL k w := by simp [powL, List.replicate_succ]
    rw [hs, gw_append, ih, pow_succ]

theorem gw_flatten_reverse (Ls : List (List Native.Gen)) :
    gw (Ls.reverse.flatten) = (Ls.map gw).prod := by
  induction Ls with
  | nil => simp [gw_nil]
  | cons x xs ih => simp [List.reverse_cons, gw_append, ih]

theorem gw_Wrho (wo : List ℕ) : gw (Wrho wo) = (wo.map fun k => gw (wq[k]!)).prod := by
  unfold Wrho
  rw [gw_flatten_reverse, List.map_map]
  rfl

@[expose, reducible] noncomputable def gq (k : ℕ) : Gmat := gw wq[k]!

section Pc

variable (hpc : agreeAll pcPairs = true)
include hpc

theorem gq_pow {i : ℕ} (hi : i < 6) : gq i ^ 7 = 1 := by
  have h := agreeAll_sound hpc (powL 7 wq[i]!, [])
    (by
      unfold pcPairs
      exact List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  rw [gw_powL, gw_nil] at h
  exact h

theorem gq_conj {i j : ℕ} (hi : i < 6) (hj : j < 6) (hij : i < j) :
    gq i * gq j * (gq i)⁻¹ = (((wordOfVec 6 (cw7[i * 6 + j]!)).map gq).prod) := by
  have h := agreeAll_sound hpc
    (wq[j]! ++ wq[i]!, wq[i]! ++ Wrho (wordOfVec 6 (cw7[i * 6 + j]!)))
    (by
      unfold pcPairs
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩)
      exact List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, by simp [hij]⟩)
  rw [gw_append, gw_append, gw_Wrho] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h

end Pc

@[expose] def vWord (v : V6) : List ℕ :=
  List.replicate v.e 0 ++ List.replicate v.q.a0 1 ++ List.replicate v.q.a1 2 ++
    List.replicate v.q.a2 3 ++ List.replicate v.q.a3 4 ++ List.replicate v.q.c 5

theorem swap_of_conj {G : Type*} [Group G] {a b z : G} (hza : z * a = a * z) (hz : z ^ 7 = 1)
    {k n : ℕ} (h : a * b * a⁻¹ = b * z ^ k) (hkn : (k + n) % 7 = 0) : b * a = a * b * z ^ n := by
  have e1 : a * b = b * z ^ k * a := mul_inv_eq_iff_eq_mul.1 h
  have hc : z ^ k * a = a * z ^ k := (Commute.pow_left hza k).eq
  have e2 : z ^ (k + n) = 1 := by rw [pow_eq_pow_mod _ hz, hkn, pow_zero]
  calc b * a = b * a * z ^ (k + n) := by rw [e2, mul_one]
    _ = b * (z ^ k * a) * z ^ n := by rw [hc, pow_add]; simp only [mul_assoc]
    _ = a * b * z ^ n := by rw [← mul_assoc b, e1]

@[expose, reducible] noncomputable def qR : Fin 4 → Gmat := fun i => gq (i.val + 1)

theorem prod_vWord (v : V6) : ((vWord v).map gq).prod = psi (gq 0) qR (gq 5) v := by
  have e0 : qR 0 = gq 1 := rfl
  have e1 : qR 1 = gq 2 := rfl
  have e2 : qR 2 = gq 3 := rfl
  have e3 : qR 3 = gq 4 := rfl
  simp only [vWord, psi, nfQ, e0, e1, e2, e3,
    List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, mul_assoc]

section Pc

variable (hpc : agreeAll pcPairs = true)
include hpc

theorem gq_conj_vWord {i j : ℕ} (hi : i < 6) (hj : j < 6)
    (hij : i < j) {a : QV} (hw : wordOfVec 6 (cw7[i * 6 + j]!) = vWord ⟨0, a⟩) :
    gq i * gq j * (gq i)⁻¹ = nfQ qR (gq 5) a := by
  rw [gq_conj hpc hi hj hij, hw, prod_vWord]
  simp [psi]

theorem gq_comm_five {i : ℕ} (hi : i < 5) : gq i * gq 5 = gq 5 * gq i := by
  have h := gq_conj hpc (by omega) (by norm_num : 5 < 6) hi
  have hw : wordOfVec 6 (cw7[i * 6 + 5]!) = [5] := by interval_cases i <;> decide +kernel
  rw [hw, List.map_singleton, List.prod_singleton] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem gq_swap {i j k n : ℕ} (hi : i < 5) (hj : j < 6)
    (hij : i < j) (hw : wordOfVec 6 (cw7[i * 6 + j]!) = j :: List.replicate k 5)
    (hkn : (k + n) % 7 = 0) : gq j * gq i = gq i * gq j * gq 5 ^ n := by
  have h := gq_conj hpc (by omega) hj hij
  rw [hw, List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate] at h
  exact swap_of_conj (gq_comm_five hpc hi).symm (gq_pow hpc (by norm_num)) h hkn

theorem pcHyp_gq : PcHyp (gq 0) qR (gq 5) where
  rel :=
    { z7 := gq_pow hpc (by norm_num)
      q7 := fun i => gq_pow hpc (by have := i.isLt; omega)
      zc := fun i => (gq_comm_five hpc (by have := i.isLt; omega)).symm
      s01 := gq_swap hpc (k := 6) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl
      s02 := gq_swap hpc (k := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl
      s03 := gq_swap hpc (k := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl
      s12 := gq_swap hpc (k := 6) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl
      s13 := gq_swap hpc (k := 0) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl
      s23 := gq_swap hpc (k := 0) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) rfl }
  u7 := gq_pow hpc (by norm_num)
  c0 := gq_conj_vWord hpc (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  c1 := gq_conj_vWord hpc (i := 0) (j := 2) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  c2 := gq_conj_vWord hpc (i := 0) (j := 3) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  c3 := gq_conj_vWord hpc (i := 0) (j := 4) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  cz := by
    rw [mul_inv_eq_iff_eq_mul]
    exact gq_comm_five hpc (by norm_num)

end Pc

@[expose] def mv (ws : List ℕ) (W : List ℕ) : V6 :=
  W.foldr (fun j acc => mulV (dec (nth ws j)) acc) ⟨0, ⟨0, 0, 0, 0, 0⟩⟩

@[expose] def wsQ : List ℕ := [16807, 2401, 343, 49, 7, 1]

@[expose] def wD : List ℕ := List.replicate 6 1 ++ [0, 1] ++ List.replicate 6 0

@[expose] def wK (k : ℕ) : List ℕ :=
  if k = 5 then
    (List.replicate 6 (([0] ++ List.replicate 6 1 ++ List.replicate 6 0 ++ [1]) ++ [1] ++ wD ++
      List.replicate 6 1)).flatten
  else if k = 2 then wD ++ List.replicate 4 5
  else if k = 3 then List.replicate 6 2 ++ [0, 2] ++ List.replicate 6 0 ++ List.replicate 3 5
  else List.replicate 6 3 ++ [0, 3] ++ List.replicate 6 0 ++ List.replicate 2 5

theorem prod_psi {G : Type*} [Group G] {u z : G} {q : Fin 4 → G} (H : PcHyp u q z)
    (C : ∀ k < 7, phiOK (343 * k) 343 = true) (ws : List ℕ) {y : ℕ → G} :
    ∀ W : List ℕ, (∀ j ∈ W, y j = psi u q z (dec (nth ws j))) →
      (W.map y).prod = psi u q z (mv ws W)
  | [], _ => by simp [mv, psi_zero]
  | j :: W, h => by
    have hW : (W.map y).prod = psi u q z (mv ws W) :=
      prod_psi H C ws W fun j' hj' => h j' (List.mem_cons_of_mem _ hj')
    have hr : redV (mv ws W) := by
      cases W with
      | nil => exact one_red
      | cons _ _ => exact mulV_red _ _
    rw [List.map_cons, List.prod_cons, hW, h j List.mem_cons_self, H.psi_mul C (dec_red _) hr]
    rfl

theorem psi_wsQ : ∀ j < 6,
    gq j = psi (gq 0) qR (gq 5) (dec (nth wsQ j)) := by
  intro j hj
  rw [← prod_vWord]
  interval_cases j <;> simp [wsQ, nth, dec, CFSG.KC.MonPcSeven.decQ, vWord]

theorem mv_wK_beq : ∀ k ∈ [5, 2, 3, 4], (mv wsQ (wK k)).beq (dec (nth wsQ k)) = true := by
  decide +kernel

theorem mv_aut_beq : ∀ a < 2, ∀ k ∈ [5, 2, 3, 4],
    (mv (autAt a) (wK k)).beq (dec (nth (autAt a) k)) = true := by
  decide +kernel

theorem mv_wK (k : ℕ) (hk : k ∈ [5, 2, 3, 4]) : mv wsQ (wK k) = dec (nth wsQ k) :=
  CFSG.KC.BM.PcFive.V6.beq_eq (mv_wK_beq k hk)

theorem mv_aut (a : ℕ) (ha : a < 2) (k : ℕ) (hk : k ∈ [5, 2, 3, 4]) :
    mv (autAt a) (wK k) = dec (nth (autAt a) k) :=
  CFSG.KC.BM.PcFive.V6.beq_eq (mv_aut_beq a ha k hk)

theorem wK_lt : ∀ k ∈ [5, 2, 3, 4], ∀ j ∈ wK k, j < 6 := by decide +kernel

theorem wK_prev : ∀ k ∈ [5, 2, 3, 4], ∀ j ∈ wK k, j = 0 ∨ j = 1 ∨
    (k ≠ 5 ∧ j = 5) ∨ (k = 3 ∧ j = 2) ∨ (k = 4 ∧ j = 3) := by decide +kernel

theorem img_of_wK (hpc : agreeAll pcPairs = true) {g : Gmat} {a : ℕ} (ha : a < 2) {k : ℕ}
    (hk : k ∈ [5, 2, 3, 4])
    (h : ∀ j ∈ wK k, g * gq j * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) j))) :
    g * gq k * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) k)) := by
  have H := pcHyp_gq hpc
  have C := CFSG.KC.MonPcSevenD.m7phi
  have hk6 : k < 6 := by simp at hk; omega
  have e1 : gq k = ((wK k).map gq).prod := by
    rw [prod_psi H C wsQ (wK k) fun j hj => psi_wsQ j (wK_lt k hk j hj), mv_wK k hk,
      ← psi_wsQ k hk6]
  have e2 : g * ((wK k).map gq).prod * g⁻¹ = ((wK k).map fun j => g * gq j * g⁻¹).prod := by
    rw [← MulAut.conj_apply, map_list_prod, List.map_map]
    rfl
  rw [e1, e2, prod_psi H C (autAt a) (wK k) h, mv_aut a ha k hk]

theorem gq_aut_of_gens (hpc : agreeAll pcPairs = true) {g : Gmat} {a : ℕ} (ha : a < 2)
    (h01 : ∀ i < 2, g * gq i * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) i))) :
    ∀ i < 6, g * gq i * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) i)) := by
  have h0 := h01 0 (by norm_num)
  have h1 := h01 1 (by norm_num)
  have step : ∀ k ∈ [5, 2, 3, 4], (∀ j, j < 6 → (j = 0 ∨ j = 1 ∨ (k ≠ 5 ∧ j = 5) ∨
      (k = 3 ∧ j = 2) ∨ (k = 4 ∧ j = 3)) →
        g * gq j * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) j))) →
      g * gq k * g⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) k)) := fun k hk hj =>
    img_of_wK hpc ha hk fun j hjW => hj j (wK_lt k hk j hjW) (wK_prev k hk j hjW)
  have h5 := step 5 (by simp) fun j _ hj => by
    rcases hj with rfl | rfl | hj | hj | hj
    · exact h0
    · exact h1
    all_goals omega
  have h2 := step 2 (by simp) fun j _ hj => by
    rcases hj with rfl | rfl | ⟨-, rfl⟩ | hj | hj
    · exact h0
    · exact h1
    · exact h5
    all_goals omega
  have h3 := step 3 (by simp) fun j _ hj => by
    rcases hj with rfl | rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩ | hj
    · exact h0
    · exact h1
    · exact h5
    · exact h2
    · omega
  have h4 := step 4 (by simp) fun j _ hj => by
    rcases hj with rfl | rfl | ⟨-, rfl⟩ | hj | ⟨-, rfl⟩
    · exact h0
    · exact h1
    · exact h5
    · omega
    · exact h3
  intro i hi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem wordOfVec_aut : ∀ a < 2, ∀ i < 6, wordOfVec 6 ((alphaVecs[a]!)[i]!) =
    vWord (dec (nth (autAt a) i)) := by
  decide +kernel

theorem gw_aut_iff {a i : ℕ} (ha : a < 2) (hi : i < 6) :
    gw (wq[i]! ++ autW[a]!) = gw (autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!))) ↔
      gw autW[a]! * gq i * (gw autW[a]!)⁻¹ = psi (gq 0) qR (gq 5) (dec (nth (autAt a) i)) := by
  rw [gw_append, gw_append, gw_Wrho, wordOfVec_aut a ha i hi, ← prod_vWord, mul_inv_eq_iff_eq_mul]

theorem autPairs_of_gens (hpc : agreeAll pcPairs = true)
    (h01 : ∀ a < 2, ∀ i < 2,
      gw (wq[i]! ++ autW[a]!) = gw (autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!)))) :
    ∀ a < 2, ∀ i < 6,
      gw (wq[i]! ++ autW[a]!) = gw (autW[a]! ++ Wrho (wordOfVec 6 ((alphaVecs[a]!)[i]!))) :=
  fun a ha i hi => (gw_aut_iff ha hi).2 (gq_aut_of_gens hpc ha
    (fun i' hi' => (gw_aut_iff ha (by omega)).1 (h01 a ha i' hi')) i hi)

end CFSG.KC.KDenseP.MonSeven.AutGen

end
