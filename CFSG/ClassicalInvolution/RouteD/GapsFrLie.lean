module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (coe_upperSL2_eq_transvection coe_lowerSL2_eq_transvection
  spinAction_comp_longSL2)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame)
open scoped MatrixGroups commutatorElement

section Generation

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem longSL2_range_eq_sup (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    (F.longSL2 hij s t).range =
      (F.longRoot hij s t).range ⊔ (F.longRoot hij.symm (!t) (!s)).range := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨A, rfl⟩
    refine Frame.sl2_apply_mem (F.longSL2 hij s t) _ (fun c => ?_) (fun c => ?_) A
    · rw [← coe_upperSL2_eq_transvection, HypFrame.longSL2_upperSL2]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · rw [← coe_lowerSL2_eq_transvection, HypFrame.longSL2_lowerSL2]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd c), by rw [HypFrame.longSL2_upperSL2]; rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd c), by rw [HypFrame.longSL2_lowerSL2]; rfl⟩

end Generation

section Chain

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  (F : HypFrame Q m) (Fix : Subgroup (spinGroup Q))

@[expose] def RootInN (a b : ℕ) (s t : Bool) : Prop :=
  ∃ (ha : a < m) (hb : b < m) (hab : a ≠ b),
    ∀ c : K, F.longRoot (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (fun h => hab (congrArg Fin.val h)) s t
      (.ofAdd c) ∈ Fix

variable {F Fix}

theorem RootInN.swap {a b : ℕ} {s t : Bool} (h : RootInN F Fix a b s t) : RootInN F Fix b a t s := by
  obtain ⟨ha, hb, hab, h⟩ := h
  refine ⟨hb, ha, fun e => hab e.symm, fun c => ?_⟩
  have := h (-c)
  rw [HypFrame.longRoot_swap, neg_neg] at this
  exact this

theorem RootInN.comm {a j k : ℕ} {s t u : Bool} (h1 : RootInN F Fix a j s t)
    (h2 : RootInN F Fix j k (!t) u) (hak : a ≠ k) : RootInN F Fix a k s u := by
  obtain ⟨ha, hj, haj, h1⟩ := h1
  obtain ⟨hj', hk, hjk, h2⟩ := h2
  refine ⟨ha, hk, hak, fun c => ?_⟩
  have hc := HypFrame.commutator_longRoot_longRoot F (i := ⟨a, ha⟩) (j := ⟨j, hj⟩)
    (k := ⟨k, hk⟩) (fun h => haj (congrArg Fin.val h)) (fun h => hjk (congrArg Fin.val h))
    (fun h => hak (congrArg Fin.val h)) s t u c 1
  rw [mul_one] at hc
  rw [← hc, commutatorElement_def]
  exact Fix.mul_mem (Fix.mul_mem (Fix.mul_mem (h1 c) (h2 1)) (Fix.inv_mem (h1 c)))
    (Fix.inv_mem (h2 1))

end Chain

section Closure

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  {F : HypFrame Q m} {Fix : Subgroup (spinGroup Q)}

theorem rootInN_of_chain {n : ℕ} (hn2 : 2 ≤ n)
    (hA : ∀ a, 1 ≤ a → a < n →
      RootInN F Fix a (a + 1) true false ∧ RootInN F Fix (a + 1) a true false)
    (hT : RootInN F Fix (n - 1) n true true ∧ RootInN F Fix n (n - 1) false false) :
    ∀ a b (s t : Bool), 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≠ b → RootInN F Fix a b s t := by
  have st1 : ∀ d a, 1 ≤ a → a + d + 1 ≤ n → RootInN F Fix a (a + d + 1) true false := by
    intro d
    induction d with
    | zero => exact fun a ha h => (hA a ha (by omega)).1
    | succ d ih =>
      intro a ha h
      have h1 := ih a ha (by omega)
      have h2 := (hA (a + d + 1) (by omega) (by omega)).1
      have := RootInN.comm (u := false) (t := false) h1 h2 (by omega)
      have e : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [e]
      exact this
  have st2 : ∀ d a, 1 ≤ a → a + d + 1 ≤ n → RootInN F Fix (a + d + 1) a true false := by
    intro d
    induction d with
    | zero => exact fun a ha h => (hA a ha (by omega)).2
    | succ d ih =>
      intro a ha h
      have h1 := (hA (a + d + 1) (by omega) (by omega)).2
      have h2 := ih a ha (by omega)
      have := RootInN.comm (u := false) (t := false) h1 h2 (by omega)
      have e : a + (d + 1) + 1 = a + d + 1 + 1 := by omega
      rw [e]
      exact this
  have stA : ∀ a b, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≠ b → RootInN F Fix a b true false := by
    intro a b ha ha' hb hb' hab
    rcases lt_or_gt_of_ne hab with h | h
    · obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
      exact st1 d a ha hb'
    · obtain ⟨d, rfl⟩ : ∃ d, a = b + d + 1 := ⟨a - b - 1, by omega⟩
      exact st2 d b hb ha'
  have st3 : ∀ a b, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≠ b → RootInN F Fix a b false true :=
    fun a b ha ha' hb hb' hab => (stA b a hb hb' ha ha' (fun e => hab e.symm)).swap
  have p1 : ∀ i, 1 ≤ i → i < n → RootInN F Fix i n true true := by
    intro i hi hin
    by_cases hi1 : i = n - 1
    · subst hi1
      exact hT.1
    · have h1 := stA i (n - 1) hi (by omega) (by omega) (by omega) (by omega)
      exact RootInN.comm (u := true) (t := false) h1 hT.1 (by omega)
  have p2 : ∀ i j, 1 ≤ i → i < j → j < n → RootInN F Fix i j true true := by
    intro i j hi hij hjn
    have h1 := stA i n hi (by omega) (by omega) le_rfl (by omega)
    have h2 := (p1 j (by omega) hjn).swap
    exact RootInN.comm (u := true) (t := false) h1 h2 (by omega)
  have p3 : ∀ a b, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≠ b → RootInN F Fix a b true true := by
    intro a b ha ha' hb hb' hab
    by_cases han : a = n
    · subst han
      exact (p1 b hb (by omega)).swap
    · by_cases hbn : b = n
      · subst hbn
        exact p1 a ha (by omega)
      · rcases lt_or_gt_of_ne hab with h | h
        · exact p2 a b ha h (by omega)
        · exact (p2 b a hb h (by omega)).swap
  have m0 : RootInN F Fix (n - 1) n false false := hT.2.swap
  have m1 : ∀ k, 1 ≤ k → k < n → RootInN F Fix k n false false := by
    intro k hk hkn
    by_cases hk1 : k = n - 1
    · subst hk1
      exact m0
    · have h1 := st3 k (n - 1) hk (by omega) (by omega) (by omega) (by omega)
      exact RootInN.comm (u := false) (t := true) h1 m0 (by omega)
  have m2 : ∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → i ≠ j → RootInN F Fix i j false false := by
    intro i j hi hin hj hjn hij
    have h1 := st3 i n hi (by omega) (by omega) le_rfl (by omega)
    have h2 := (m1 j hj hjn).swap
    exact RootInN.comm (u := false) (t := true) h1 h2 (by omega)
  have m3 : ∀ a b, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≠ b → RootInN F Fix a b false false := by
    intro a b ha ha' hb hb' hab
    by_cases han : a = n
    · subst han
      exact (m1 b hb (by omega)).swap
    · by_cases hbn : b = n
      · subst hbn
        exact m1 a ha (by omega)
      · exact m2 a b ha (by omega) hb (by omega) hab
  intro a b s t ha ha' hb hb' hab
  cases s <;> cases t
  · exact m3 a b ha ha' hb hb' hab
  · exact st3 a b ha ha' hb hb' hab
  · exact stA a b ha ha' hb hb' hab
  · exact p3 a b ha ha' hb hb' hab

end Closure

section Centralizer

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem mem_lowerRoot_of_comm_central (F : HypFrame Q m)
    (hscal : ∀ z ∈ Subgroup.center (spinGroup Q), ∃ η : K, ∀ v, spinAction Q z v = η • v)
    {i j k : Fin m} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {g : spinGroup Q}
    (hg : g ∈ (F.longSL2 hij true false).range)
    (hc : ∀ c : K, ⁅g, F.longRoot hjk true false (.ofAdd c)⁆ ∈ Subgroup.center (spinGroup Q)) :
    ∃ c : K, g = F.longRoot hij.symm true false (.ofAdd c) := by
  obtain ⟨M, rfl⟩ := hg
  have hπ : ∀ A, spinAction Q (F.longSL2 hij true false A) = (F.toFrame hij true false).La A :=
    fun A => DFunLike.congr_fun (spinAction_comp_longSL2 F hij true false) A
  set fr := F.toFrame hij true false with hfr
  obtain ⟨η, hη⟩ := hscal _ (hc 1)
  set w := F.longRoot hjk true false (.ofAdd (1 : K)) with hwdef
  have hk0 : ∀ u : Bool, fr.coords (F.vec k u) = 0 := by
    intro u
    rw [Frame.coords_apply]
    have a1 : polar Q (F.vec k u) fr.f₁ = 0 := F.polar_vec_of_ne hik.symm u (!true)
    have a2 : polar Q (F.vec k u) fr.f₂ = 0 := F.polar_vec_of_ne hjk.symm u (!false)
    have a3 : polar Q (F.vec k u) fr.e₂ = 0 := F.polar_vec_of_ne hjk.symm u false
    have a4 : polar Q (F.vec k u) fr.e₁ = 0 := F.polar_vec_of_ne hik.symm u true
    rw [a1, a2, a3, a4]
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have hgk : spinAction Q (F.longSL2 hij true false M) (F.vec k true) = F.vec k true := by
    rw [hπ]
    exact Frame.La_apply_of_coords_eq_zero fr M (hk0 true)
  have hw : spinAction Q w (F.vec k true) = F.vec k true + F.vec j true := by
    have := F.spinAction_longRoot_vec_not_right hjk true false (1 : K)
    simpa using this
  have key : ∀ a b c : spinGroup Q, ∀ v, spinAction Q a (spinAction Q b (spinAction Q c v)) =
      spinAction Q (a * b * c) v := by
    intro a b c v
    simp [map_mul, LinearEquiv.mul_apply]
  have hcomm : spinAction Q (F.longSL2 hij true false M) (spinAction Q w (F.vec k true)) =
      η • spinAction Q w (spinAction Q (F.longSL2 hij true false M) (F.vec k true)) := by
    have h1 := hη (spinAction Q w (spinAction Q (F.longSL2 hij true false M) (F.vec k true)))
    rw [key] at h1
    have e : ⁅F.longSL2 hij true false M, w⁆ * w * F.longSL2 hij true false M =
        F.longSL2 hij true false M * w := by
      simp only [commutatorElement_def]
      group
    rw [e, map_mul, LinearEquiv.mul_apply] at h1
    exact h1
  rw [hw, map_add, hgk, hw] at hcomm
  have hMj : spinAction Q (F.longSL2 hij true false M) (F.vec j true) =
      F.vec j true + fr.incl ((M : Matrix (Fin 2) (Fin 2) K) * fr.coords (F.vec j true) -
        fr.coords (F.vec j true)) := by
    rw [hπ]
    exact Frame.La_apply fr M _
  have hpk : ∀ Y, polar Q (F.vec k false) (fr.incl Y) = 0 := by
    intro Y
    rw [Frame.polar_incl_right, hk0 false]
    simp
  have hη1 : η = 1 := by
    have h1 := congrArg (fun v => polar Q v (F.vec k false)) hcomm
    simp only [polar_add_left, polar_smul_left_eq] at h1
    have e1 : polar Q (F.vec k true) (F.vec k false) = 1 := F.polar_vec_not k true
    have e2 : polar Q (F.vec j true) (F.vec k false) = 0 := F.polar_vec_of_ne hjk true false
    have e3 : polar Q (spinAction Q (F.longSL2 hij true false M) (F.vec j true))
        (F.vec k false) = 0 := by
      rw [hMj, polar_add_left, e2, zero_add, polar_comm]
      exact hpk _
    rw [e3, e1, e2] at h1
    simpa using h1.symm
  rw [hη1, one_smul] at hcomm
  have hgj : spinAction Q (F.longSL2 hij true false M) (F.vec j true) = F.vec j true :=
    add_left_cancel hcomm
  have hX : fr.coords (F.vec j true) = !![0, 0; 1, 0] := by
    rw [Frame.coords_apply]
    have a1 : polar Q (F.vec j true) fr.f₁ = 0 := F.polar_vec_of_ne hij.symm true (!true)
    have a2 : polar Q (F.vec j true) fr.f₂ = 0 := F.polar_vec_self j true
    have a3 : polar Q (F.vec j true) fr.e₂ = 1 := F.polar_vec_not j true
    have a4 : polar Q (F.vec j true) fr.e₁ = 0 := F.polar_vec_of_ne hij.symm true true
    rw [a1, a2, a3, a4]
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have h0 : fr.incl ((M : Matrix (Fin 2) (Fin 2) K) * fr.coords (F.vec j true) -
      fr.coords (F.vec j true)) = 0 := by
    have h := hMj
    rw [hgj] at h
    have h' : F.vec j true + 0 = F.vec j true + fr.incl ((M : Matrix (Fin 2) (Fin 2) K) *
        fr.coords (F.vec j true) - fr.coords (F.vec j true)) := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h').symm
  have hMX : (M : Matrix (Fin 2) (Fin 2) K) * fr.coords (F.vec j true) -
      fr.coords (F.vec j true) = 0 :=
    Frame.incl_injective fr (h0.trans (map_zero fr.incl).symm)
  rw [hX] at hMX
  have h00 := congrFun (congrFun hMX 0) 0
  have h10 := congrFun (congrFun hMX 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  have hdet := M.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := h10
    linear_combination this
  have h00' : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [h11, h00] at hdet
    simpa using hdet
  have hM : M = lowerSL2 ((M : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    apply Subtype.ext
    ext r c
    fin_cases r <;> fin_cases c <;> simp [coe_lowerSL2, h00', h00, h11]
  exact ⟨(M : Matrix (Fin 2) (Fin 2) K) 1 0,
    (congrArg (F.longSL2 hij true false) hM).trans (HypFrame.longSL2_lowerSL2 F hij true false _)⟩

end Centralizer

end CFSG.ClassicalInvolution.RouteD.Gaps
