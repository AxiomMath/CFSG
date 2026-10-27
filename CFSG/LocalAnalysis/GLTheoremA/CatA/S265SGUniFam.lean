module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGUniEig
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniLevi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni

variable {K : Type} [Field K] {σ : K ≃+* K} {n k : ℕ} {ι : Type}
  {S : ι → (Fin n → K) →ₗ[K] (Fin n → K)} {u w : Fin k → Fin n → K}

private structure SG.HypPairsF (σ : K ≃+* K) (S : ι → (Fin n → K) →ₗ[K] (Fin n → K))
    (u w : Fin k → Fin n → K) : Prop where
  uu : ∀ i j, herm σ (u i) (u j) = 0
  ww : ∀ i j, herm σ (w i) (w j) = 0
  uw : ∀ i j, herm σ (u i) (w j) = if i = j then 1 else 0
  eu : ∀ i s, ∃ a : K, S s (u i) = a • u i
  ew : ∀ i s, ∃ a : K, S s (w i) = a • w i

private theorem SG.HypPairsF.hyp (h : SG.HypPairsF σ S u w) (s : ι) : HypPairs σ (S s) u w :=
  ⟨h.uu, h.ww, h.uw, fun i => h.eu i s, fun i => h.ew i s⟩

private theorem SG.HypPairsF.wu (h : SG.HypPairsF σ S u w) (hinv : ∀ c, σ (σ c) = c) (i j : Fin k) :
    herm σ (w i) (u j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hinv (u j) (w i), h.uw j i]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

private theorem SG.HypPairsF.paired [DecidableEq ι] (h : SG.HypPairsF σ S u w)
    (hinv : ∀ c, σ (σ c) = c) : SG.PFam σ S (Sum.elim u w) Sum.swap := by
  refine ⟨fun i => Sum.swap_swap i, fun i j => ?_, fun s i => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · simp [h.uu i j]
    · rw [Sum.elim_inl, Sum.elim_inr, h.uw i j]
      simp only [Sum.swap_inl, Sum.inr.injEq]
      exact if_congr eq_comm rfl rfl
    · rw [Sum.elim_inr, Sum.elim_inl, h.wu hinv i j]
      simp only [Sum.swap_inr, Sum.inl.injEq]
      exact if_congr eq_comm rfl rfl
    · simp [h.ww i j]
  · rcases i with i | i
    · exact h.eu i s
    · exact h.ew i s

private theorem SG.exists_hypPairsF (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hσω : σ ω = ω) [Fintype ι] (hcomm : ∀ i j, Commute (S i) (S j)) (hSp : ∀ i, S i ^ 3 = 1)
    (hS : ∀ i x y, herm σ (S i x) (S i y) = herm σ x y) :
    ∀ k : ℕ, 2 * k ≤ n → ∃ u w : Fin k → Fin n → K, SG.HypPairsF σ S u w := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨u, w, h⟩ := ih (by omega)
    obtain ⟨u0, w0, hu, hw, hu0, hw0, huw0, hperp⟩ := SG.exists_pair_family hσ hω hσω hcomm hSp hS
      (κ := Fin k ⊕ Fin k) (by simp [Fintype.card_sum]; omega) (h.paired hσ.invol)
    have hu0u : ∀ i, herm σ (u i) u0 = 0 := fun i => (hperp (Sum.inl i)).1
    have hu0w : ∀ i, herm σ (u i) w0 = 0 := fun i => (hperp (Sum.inl i)).2
    have hw0u : ∀ i, herm σ (w i) u0 = 0 := fun i => (hperp (Sum.inr i)).1
    have hw0w : ∀ i, herm σ (w i) w0 = 0 := fun i => (hperp (Sum.inr i)).2
    refine ⟨Fin.snoc (α := fun _ => Fin n → K) u u0, Fin.snoc (α := fun _ => Fin n → K) w w0,
      ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i => ?_, fun i => ?_⟩⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using hu0
        | cast j => simpa using herm_eq_zero_comm σ hσ.invol (hu0u j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using hu0u i
        | cast j => simpa using h.uu i j
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using hw0
        | cast j => simpa using herm_eq_zero_comm σ hσ.invol (hw0w j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using hw0w i
        | cast j => simpa using h.ww i j
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simpa using huw0
        | cast j =>
          have := herm_eq_zero_comm σ hσ.invol (hw0u j)
          simp [Fin.snoc_last, Fin.snoc_castSucc, this, (Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [Fin.snoc_last, Fin.snoc_castSucc, hu0w i, (Fin.castSucc_lt_last i).ne]
        | cast j => simpa using h.uw i j
    · induction i using Fin.lastCases with
      | last => simpa using hu
      | cast i => simpa using h.eu i
    · induction i using Fin.lastCases with
      | last => simpa using hw
      | cast i => simpa using h.ew i

private theorem SG.HypPairsF.swap (h : SG.HypPairsF σ S u w) (hinv : ∀ c, σ (σ c) = c)
    (P : Fin k → Prop) [DecidablePred P] :
    SG.HypPairsF σ S (fun j => if P j then w j else u j) (fun j => if P j then u j else w j) := by
  have hne : ∀ i j, (P i ↔ ¬ P j) → i ≠ j := fun i j hij e => by
    subst e
    by_cases hi : P i
    · exact (hij.1 hi) hi
    · exact hi (hij.2 hi)
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i => ?_, fun i => ?_⟩
  · by_cases hi : P i <;> by_cases hj : P j
    · simp only [if_pos hi, if_pos hj, h.ww i j]
    · simp only [if_pos hi, if_neg hj, h.wu hinv, if_neg (hne i j ⟨fun _ => hj, fun _ => hi⟩)]
    · simp only [if_neg hi, if_pos hj, h.uw, if_neg (hne i j ⟨fun h' => (hi h').elim,
        fun h' => (h' hj).elim⟩)]
    · simp only [if_neg hi, if_neg hj, h.uu i j]
  · by_cases hi : P i <;> by_cases hj : P j
    · simp only [if_pos hi, if_pos hj, h.uu i j]
    · simp only [if_pos hi, if_neg hj, h.uw, if_neg (hne i j ⟨fun _ => hj, fun _ => hi⟩)]
    · simp only [if_neg hi, if_pos hj, h.wu hinv, if_neg (hne i j ⟨fun h' => (hi h').elim,
        fun h' => (h' hj).elim⟩)]
    · simp only [if_neg hi, if_neg hj, h.ww i j]
  · by_cases hi : P i <;> by_cases hj : P j
    · simp only [if_pos hi, if_pos hj, h.wu hinv i j]
    · simp only [if_pos hi, if_neg hj, h.ww, if_neg (hne i j ⟨fun _ => hj, fun _ => hi⟩)]
    · simp only [if_neg hi, if_pos hj, h.uu, if_neg (hne i j ⟨fun h' => (hi h').elim,
        fun h' => (h' hj).elim⟩)]
    · simp only [if_neg hi, if_neg hj, h.uw i j]
  · by_cases hi : P i
    · simpa only [if_pos hi] using h.ew i
    · simpa only [if_neg hi] using h.eu i
  · by_cases hi : P i
    · simpa only [if_pos hi] using h.eu i
    · simpa only [if_neg hi] using h.ew i

theorem SG.exists_hypPairs_family (hσ : IsUnitaryInvolution σ) {ω : K}
    (hω : IsPrimitiveRoot ω 3) (hσω : σ ω = ω) [Finite ι]
    (hcomm : ∀ i j, Commute (S i) (S j)) (hSp : ∀ i, S i ^ 3 = 1)
    (hS : ∀ i x y, herm σ (S i x) (S i y) = herm σ x y) (hk : 2 * k ≤ n) (i₀ : ι) :
    ∃ u w : Fin k → Fin n → K, (∀ i, HypPairs σ (S i) u w) ∧
      ∀ j, S i₀ (u j) = u j ∨ S i₀ (u j) = ω • u j := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨u, w, h⟩ := SG.exists_hypPairsF hσ hω hσω hcomm hSp hS k hk
  refine ⟨_, _, fun s => (h.swap hσ.invol fun j => S i₀ (u j) = ω ^ 2 • u j).hyp s, fun j => ?_⟩
  have hu0 : u j ≠ 0 := fun h0 => by
    have := h.uw j j
    rw [h0, herm_zero_left] at this
    simp at this
  by_cases hj : S i₀ (u j) = ω ^ 2 • u j
  · simp only [hj, if_true]
    right
    obtain ⟨b, hb⟩ := h.ew j i₀
    have h1 := hS i₀ (u j) (w j)
    rw [hj, hb, herm_smul_left, herm_smul_right, h.uw j j, if_pos rfl, map_pow, hσω] at h1
    have hb' : b = ω := by
      have h3 : ω ^ 3 = 1 := hω.pow_eq_one
      linear_combination (ω : K) * h1 - b * h3
    rw [hb, hb']
  · simp only [hj, if_false]
    obtain ⟨a, ha⟩ := h.eu j i₀
    obtain ⟨i, hi3, hia⟩ := hω.eq_pow_of_pow_eq_one (eigen_cube (hSp i₀) ha hu0)
    interval_cases i
    · left
      rw [ha, ← hia, pow_zero, one_smul]
    · right
      rw [ha, ← hia, pow_one]
    · exact (hj (by rw [ha, ← hia])).elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end
