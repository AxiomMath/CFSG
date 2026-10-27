module

public import CFSG.GF2Type.Smith1979.IdxFourIdentFLDefs
public import CFSG.GF2Type.Smith1979.IdxFourIdentMon

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace FLStructAux

open MonAux

def pcode (j : Fin 6) (p : ZMod 2 × ZMod 2) : ℕ :=
  (if p.1 = 1 then 2 ^ (j : ℕ) else 0) + (if p.2 = 1 then 2 ^ (6 + (j : ℕ)) else 0)

theorem pr_vecOf_pcode : ∀ (j l : Fin 6) (p : ZMod 2 × ZMod 2),
    pr (vecOf (pcode j p)) l = if l = j then p else 0 := by
  decide +kernel

theorem pairVec_eq_vecOf (j : Fin 6) (p : ZMod 2 × ZMod 2) :
    pairVec j p = vecOf (pcode j p) :=
  ext_pr fun l => by rw [pr_pairVec, pr_vecOf_pcode]

noncomputable def fv (a b : Fin 4) (j : Fin 6) (k : ZMod 3) : V12 :=
  Umat a b (pairVec j (omegaPow k (1, 0)))

def uc (a b : Fin 4) (j : Fin 6) (k : ZMod 3) : ℕ :=
  appN (uRowsTable[4 * (a : ℕ) + (b : ℕ)]!) (pcode j (omegaPow k (1, 0)))

theorem fv_eq (a b : Fin 4) (j : Fin 6) (k : ZMod 3) : fv a b j k = vecOf (uc a b j k) := by
  rw [fv, Umat_apply, pairVec_eq_vecOf, ← vecOf_appN]
  rfl

def f0b (m n : ℕ) : Bool := q0b (m ^^^ n) ^^ q0b m ^^ q0b n

theorem f0_vecOf (m n : ℕ) : f0 (vecOf m) (vecOf n) = if f0b m n then 1 else 0 := by
  rw [← polar_q0, QuadraticMap.polar, ← vecOf_xor, q0_vecOf, q0_vecOf, q0_vecOf, f0b]
  generalize q0b (m ^^^ n) = A
  generalize q0b m = B
  generalize q0b n = C
  revert A B C
  decide

theorem eq_false_of_ite {b : Bool} (h : (if b then (1 : ZMod 2) else 0) = 0) : b = false := by
  revert h
  cases b <;> decide

theorem q0b_of_q0 {n : ℕ} (h : q0 (vecOf n) = 1) : q0b n = true := by
  rw [q0_vecOf] at h
  by_contra hn
  rw [if_neg hn] at h
  exact absurd h (by decide)

theorem uc_theta : ∀ (a b : Fin 4) (j : Fin 6) (k : ZMod 3),
    uc a b j k < 4096 ∧ theta0N (uc a b j k) = uc a b j (k + 1) := by
  decide +kernel

theorem uc_blk1 : ∀ (a b : Fin 4) (j : Fin 6), (j : ℕ) < 3 → ∀ k : ZMod 3,
    uc a b j k = uc a 0 j k := by
  decide +kernel

theorem uc_blk2 : ∀ (a b : Fin 4) (j : Fin 6), 3 ≤ (j : ℕ) → ∀ k : ZMod 3,
    uc a b j k = uc 0 b j k := by
  decide +kernel

theorem single1_check : ∀ p0 p1 p2 : ZMod 2 × ZMod 2,
    q0b (pcode 0 p0 ^^^ pcode 1 p1 ^^^ pcode 2 p2) = true →
      ∃ (a : Fin 4) (j : Fin 6), (j : ℕ) < 3 ∧ ∃ k : ZMod 3,
        pcode 0 p0 ^^^ pcode 1 p1 ^^^ pcode 2 p2 = uc a 0 j k := by
  decide +kernel

theorem single2_check : ∀ p3 p4 p5 : ZMod 2 × ZMod 2,
    q0b (pcode 3 p3 ^^^ pcode 4 p4 ^^^ pcode 5 p5) = true →
      ∃ (b : Fin 4) (j : Fin 6), 3 ≤ (j : ℕ) ∧ ∃ k : ZMod 3,
        pcode 3 p3 ^^^ pcode 4 p4 ^^^ pcode 5 p5 = uc 0 b j k := by
  decide +kernel

theorem pair1_check : ∀ (a a' : Fin 4) (j j' : Fin 6), (j : ℕ) < 3 → (j' : ℕ) < 3 →
    ∀ k k' : ZMod 3, f0b (uc a 0 j k) (uc a' 0 j' k') = false →
      f0b (theta0N (uc a 0 j k)) (uc a' 0 j' k') = false → a = a' ∧ j ≠ j' := by
  decide +kernel

theorem pair2_check : ∀ (b b' : Fin 4) (j j' : Fin 6), 3 ≤ (j : ℕ) → 3 ≤ (j' : ℕ) →
    ∀ k k' : ZMod 3, f0b (uc 0 b j k) (uc 0 b' j' k') = false →
      f0b (theta0N (uc 0 b j k)) (uc 0 b' j' k') = false → b = b' ∧ j ≠ j' := by
  decide +kernel

theorem fv_theta (a b : Fin 4) (j : Fin 6) (k : ZMod 3) :
    theta0 (fv a b j k) = fv a b j (k + 1) := by
  rw [fv_eq, fv_eq, ← vecOf_theta0N (uc_theta a b j k).1, (uc_theta a b j k).2]

theorem fv_blk1 (a b : Fin 4) {j : Fin 6} (hj : (j : ℕ) < 3) (k : ZMod 3) :
    fv a b j k = fv a 0 j k := by
  rw [fv_eq, fv_eq, uc_blk1 a b j hj k]

theorem fv_blk2 (a b : Fin 4) {j : Fin 6} (hj : 3 ≤ (j : ℕ)) (k : ZMod 3) :
    fv a b j k = fv 0 b j k := by
  rw [fv_eq, fv_eq, uc_blk2 a b j hj k]

def Orth (v w : V12) : Prop := f0 v w = 0 ∧ f0 (theta0 v) w = 0

theorem orth_fv {a b a' b' : Fin 4} {j j' : Fin 6} {k k' : ZMod 3}
    (h : Orth (fv a b j k) (fv a' b' j' k')) :
    f0b (uc a b j k) (uc a' b' j' k') = false ∧
      f0b (theta0N (uc a b j k)) (uc a' b' j' k') = false := by
  obtain ⟨h1, h2⟩ := h
  rw [fv_eq, fv_eq, f0_vecOf] at h1
  rw [fv_eq, fv_eq, ← vecOf_theta0N (uc_theta a b j k).1, f0_vecOf] at h2
  exact ⟨eq_false_of_ite h1, eq_false_of_ite h2⟩

theorem pair1 {a a' : Fin 4} {j j' : Fin 6} (hj : (j : ℕ) < 3) (hj' : (j' : ℕ) < 3)
    {k k' : ZMod 3} (h : Orth (fv a 0 j k) (fv a' 0 j' k')) : a = a' ∧ j ≠ j' :=
  pair1_check a a' j j' hj hj' k k' (orth_fv h).1 (orth_fv h).2

theorem pair2 {b b' : Fin 4} {j j' : Fin 6} (hj : 3 ≤ (j : ℕ)) (hj' : 3 ≤ (j' : ℕ))
    {k k' : ZMod 3} (h : Orth (fv 0 b j k) (fv 0 b' j' k')) : b = b' ∧ j ≠ j' :=
  pair2_check b b' j j' hj hj' k k' (orth_fv h).1 (orth_fv h).2

theorem single1 {v : V12} (hv : ∀ l : Fin 6, 3 ≤ (l : ℕ) → pr v l = 0) (hq : q0 v = 1) :
    ∃ (a : Fin 4) (j : Fin 6) (k : ZMod 3), (j : ℕ) < 3 ∧ v = fv a 0 j k := by
  have hv' : v = vecOf (pcode 0 (pr v 0) ^^^ pcode 1 (pr v 1) ^^^ pcode 2 (pr v 2)) := by
    rw [vecOf_xor, vecOf_xor, ← pairVec_eq_vecOf, ← pairVec_eq_vecOf, ← pairVec_eq_vecOf]
    conv_lhs => rw [← sum_pairVec v]
    simp only [Fin.sum_univ_six, hv 3 (by decide), hv 4 (by decide), hv 5 (by decide),
      pairVec_zero, add_zero]
  rw [hv'] at hq
  obtain ⟨a, j, hj, k, hk⟩ := single1_check _ _ _ (q0b_of_q0 hq)
  exact ⟨a, j, k, hj, hv'.trans (by rw [hk, fv_eq])⟩

theorem single2 {v : V12} (hv : ∀ l : Fin 6, (l : ℕ) < 3 → pr v l = 0) (hq : q0 v = 1) :
    ∃ (b : Fin 4) (j : Fin 6) (k : ZMod 3), 3 ≤ (j : ℕ) ∧ v = fv 0 b j k := by
  have hv' : v = vecOf (pcode 3 (pr v 3) ^^^ pcode 4 (pr v 4) ^^^ pcode 5 (pr v 5)) := by
    rw [vecOf_xor, vecOf_xor, ← pairVec_eq_vecOf, ← pairVec_eq_vecOf, ← pairVec_eq_vecOf]
    conv_lhs => rw [← sum_pairVec v]
    simp only [Fin.sum_univ_six, hv 0 (by decide), hv 1 (by decide), hv 2 (by decide),
      pairVec_zero, zero_add]
  rw [hv'] at hq
  obtain ⟨b, j, hj, k, hk⟩ := single2_check _ _ _ (q0b_of_q0 hq)
  exact ⟨b, j, k, hj, hv'.trans (by rw [hk, fv_eq])⟩

theorem omegaPow_cancel : ∀ (a b : ZMod 3) (p : ZMod 2 × ZMod 2), p ≠ 0 →
    omegaPow a p = omegaPow b p → a = b := by
  decide

theorem omegaPow_unit_hi_succ :
    ∀ k : ZMod 3, omegaPow k (0, 1) = omegaPow (k + 1) (1, 0) := by
  decide

theorem f0_map {g : G12} (hg : g ∈ gammaU) (u v : V12) : f0 (g u) (g v) = f0 u v := by
  rw [← polar_q0, ← polar_q0, QuadraticMap.polar, QuadraticMap.polar, ← map_add,
    (mem_gammaU.1 hg).1, (mem_gammaU.1 hg).1, (mem_gammaU.1 hg).1]

theorem f0_pairVec_ne {i i' : Fin 6} (h : i ≠ i') (p q : ZMod 2 × ZMod 2) :
    f0 (pairVec i p) (pairVec i' q) = 0 := by
  show ∑ l : Fin 6, ((pr (pairVec i p) l).1 * (pr (pairVec i' q) l).2 +
    (pr (pairVec i p) l).2 * (pr (pairVec i' q) l).1) = 0
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [pr_pairVec, pr_pairVec]
  by_cases hl : l = i
  · rw [if_neg fun hl' => h (hl.symm.trans hl')]
    simp
  · rw [if_neg hl]
    simp

theorem comm_scalar {y : G12} (hθ : ∀ v, y (theta0 v) = theta0 (y v)) (k : ZMod 3) (v : V12) :
    y (diagE (fun _ => k) v) = diagE (fun _ => k) (y v) := by
  have h3 : ∀ k : ZMod 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have h2 : (fun _ : Fin 6 => (2 : ZMod 3)) = (fun _ => 1) + (fun _ => 1) := by
    funext x
    show (2 : ZMod 3) = 1 + 1
    decide
  rcases h3 k with rfl | rfl | rfl
  · show y (diagE 0 v) = diagE 0 (y v)
    rw [diagE_zero]
    rfl
  · rw [diagE_const_one, theta0e_apply, theta0e_apply]
    exact hθ v
  · rw [h2, diagE_add, diagE_const_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      theta0e_apply, theta0e_apply, theta0e_apply, theta0e_apply, hθ, hθ]

end FLStructAux

open MonAux FLStructAux

theorem adjacent_structure {y : G12} (hy : y ∈ gammaU) (hyu : y * theta0e = theta0e * y)
    (hd : y⁻¹ * diagE chStd * y ∈ D5) :
    ∃ (a b : Fin 4) (s : ZMod 3) (c : Fin 6 → ZMod 3) (π : Equiv.Perm (Fin 6)),
      (∑ i, c i) = 0 ∧ y = Umat a b * Delta0 s * (diagE c * permE π) := by
  have hθ : ∀ v, y (theta0 v) = theta0 (y v) := fun v => congrArg (fun g : G12 => g v) hyu
  obtain ⟨c', -, hc'⟩ := hd
  have hconj : ∀ v, diagE chStd (y v) = y (diagE c' v) := fun v => by
    have h1 : diagE chStd * y = y * diagE c' := by
      rw [← hc']
      group
    exact congrArg (fun g : G12 => g v) h1
  have hkey : ∀ i l, pr (y (pairVec i (1, 0))) l ≠ 0 → chStd l = c' i := by
    intro i l hl
    have h1 : diagE chStd (y (pairVec i (1, 0))) =
        diagE (fun _ => c' i) (y (pairVec i (1, 0))) := by
      rw [hconj, diagE_pairVec, ← comm_scalar hθ, diagE_pairVec]
    have h2 := congrArg (fun v => pr v l) h1
    simp only [pr_diagE] at h2
    exact omegaPow_cancel _ _ _ hl h2
  have hW : ∀ i, (∀ l : Fin 6, 3 ≤ (l : ℕ) → pr (y (pairVec i (1, 0))) l = 0) ∨
      (∀ l : Fin 6, (l : ℕ) < 3 → pr (y (pairVec i (1, 0))) l = 0) := by
    intro i
    by_cases h : ∃ l : Fin 6, (l : ℕ) < 3 ∧ pr (y (pairVec i (1, 0))) l ≠ 0
    · obtain ⟨l₀, hl₀, hne⟩ := h
      refine Or.inl fun l hl => ?_
      by_contra hne'
      have h1 : chStd l = 0 := if_neg (by omega)
      have h2 : chStd l₀ = 1 := if_pos hl₀
      have h3 := (hkey i l hne').trans (hkey i l₀ hne).symm
      rw [h1, h2] at h3
      exact absurd h3 (by decide)
    · exact Or.inr fun l hl => by
        by_contra hne
        exact h ⟨l, hl, hne⟩
  have hq : ∀ i, q0 (y (pairVec i (1, 0))) = 1 := fun i => by
    rw [(mem_gammaU.1 hy).1]
    exact q0_eq_one_of_mem_plane (pairVec_mem_plane i _) (pairVec_ne_zero i (by decide))
  have horth : ∀ i i', i ≠ i' → Orth (y (pairVec i (1, 0))) (y (pairVec i' (1, 0))) :=
    fun i i' h => by
      refine ⟨?_, ?_⟩
      · rw [f0_map hy]
        exact f0_pairVec_ne h _ _
      · rw [← hθ, theta0_pairVec, f0_map hy]
        exact f0_pairVec_ne h _ _
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Fin 4, ∀ i, (∀ l : Fin 6, 3 ≤ (l : ℕ) →
      pr (y (pairVec i (1, 0))) l = 0) →
        ∃ (j : Fin 6) (k : ZMod 3), (j : ℕ) < 3 ∧ y (pairVec i (1, 0)) = fv a₀ 0 j k := by
    by_cases h : ∃ i, ∀ l : Fin 6, 3 ≤ (l : ℕ) → pr (y (pairVec i (1, 0))) l = 0
    · obtain ⟨i₀, hi₀⟩ := h
      obtain ⟨a₀, j₀, k₀, hj₀, he₀⟩ := single1 hi₀ (hq i₀)
      refine ⟨a₀, fun i hi => ?_⟩
      obtain ⟨a, j, k, hj, he⟩ := single1 hi (hq i)
      by_cases hii : i₀ = i
      · subst hii
        exact ⟨j₀, k₀, hj₀, he₀⟩
      · have h1 := horth i₀ i hii
        rw [he₀, he] at h1
        obtain ⟨rfl, -⟩ := pair1 hj₀ hj h1
        exact ⟨j, k, hj, he⟩
    · exact ⟨0, fun i hi => absurd ⟨i, hi⟩ h⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Fin 4, ∀ i, (∀ l : Fin 6, (l : ℕ) < 3 →
      pr (y (pairVec i (1, 0))) l = 0) →
        ∃ (j : Fin 6) (k : ZMod 3), 3 ≤ (j : ℕ) ∧ y (pairVec i (1, 0)) = fv 0 b₀ j k := by
    by_cases h : ∃ i, ∀ l : Fin 6, (l : ℕ) < 3 → pr (y (pairVec i (1, 0))) l = 0
    · obtain ⟨i₀, hi₀⟩ := h
      obtain ⟨b₀, j₀, k₀, hj₀, he₀⟩ := single2 hi₀ (hq i₀)
      refine ⟨b₀, fun i hi => ?_⟩
      obtain ⟨b, j, k, hj, he⟩ := single2 hi (hq i)
      by_cases hii : i₀ = i
      · subst hii
        exact ⟨j₀, k₀, hj₀, he₀⟩
      · have h1 := horth i₀ i hii
        rw [he₀, he] at h1
        obtain ⟨rfl, -⟩ := pair2 hj₀ hj h1
        exact ⟨j, k, hj, he⟩
    · exact ⟨0, fun i hi => absurd ⟨i, hi⟩ h⟩
  have hfk : ∀ i, ∃ (j : Fin 6) (k : ZMod 3), y (pairVec i (1, 0)) = fv a₀ b₀ j k := by
    intro i
    rcases hW i with h | h
    · obtain ⟨j, k, hj, he⟩ := ha₀ i h
      exact ⟨j, k, he.trans (fv_blk1 a₀ b₀ hj k).symm⟩
    · obtain ⟨j, k, hj, he⟩ := hb₀ i h
      exact ⟨j, k, he.trans (fv_blk2 a₀ b₀ hj k).symm⟩
  choose f k hfk using hfk
  have hinj : Function.Injective f := by
    intro i i' hii'
    by_contra hne
    have h1 := horth i i' hne
    rw [hfk i, hfk i', ← hii'] at h1
    by_cases hj : (f i : ℕ) < 3
    · rw [fv_blk1 a₀ b₀ hj, fv_blk1 a₀ b₀ hj] at h1
      exact (pair1 hj hj h1).2 rfl
    · have hj' : 3 ≤ (f i : ℕ) := by omega
      rw [fv_blk2 a₀ b₀ hj', fv_blk2 a₀ b₀ hj'] at h1
      exact (pair2 hj' hj' h1).2 rfl
  let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : ∀ i, π i = f i := fun _ => rfl
  set c'' : Fin 6 → ZMod 3 := fun j => k (π.symm j)
  have hc''π : ∀ i, c'' (π i) = k i := fun i => congrArg k (π.symm_apply_apply i)
  have hyeq : y = Umat a₀ b₀ * (diagE c'' * permE π) := by
    refine ext_pairVec (fun i => ?_) (fun i => ?_)
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, permE_pairVec, diagE_pairVec, hc''π,
        hπ, hfk i]
      rfl
    · have e01 : ((0 : ZMod 2), (1 : ZMod 2)) = thPair (1, 0) := by decide
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, permE_pairVec, diagE_pairVec, hc''π,
        hπ, omegaPow_unit_hi_succ, e01, ← theta0_pairVec, hθ, hfk i, fv_theta]
      rfl
  refine ⟨a₀, b₀, ∑ i, c'' i, c'' - fun i => if i = 0 then ∑ i, c'' i else 0, π, ?_, ?_⟩
  · simp [Finset.sum_sub_distrib]
  · rw [hyeq, Delta0, mul_assoc (Umat a₀ b₀), ← mul_assoc (diagE _), ← diagE_add,
      add_sub_cancel]

end CFSG.GF2Type.Smith1979.IdxFour
