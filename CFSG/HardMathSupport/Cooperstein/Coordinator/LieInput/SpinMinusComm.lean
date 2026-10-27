module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusComm

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section SM
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

@[expose] def BAdj (n : ℕ) (i j : Fin (n - 1)) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

theorem dotE_boolSign_self {N : ℕ} (x : Fin N) (s : Bool) :
    dotE (Pi.single x (boolSign s) : Fin N → ℤ) (Pi.single x (boolSign s)) = 1 := by
  rw [dotE_single, if_pos rfl]
  cases s <;> simp [boolSign]

theorem dotE_eps_self_B (n : ℕ) (i : Fin (n - 1)) :
    dotE (toStdB (n - 1) (Pi.single i 1)) (toStdB (n - 1) (Pi.single i 1)) =
      if i.val + 1 < n - 1 then 2 else 1 := by
  by_cases hi : i.val + 1 < n - 1
  · rw [if_pos hi, toStdB_single_of_lt' n hi]
    exact dotE_root (succ_ne_of_lt n hi) true false
  · rw [if_neg hi, toStdB_single_of_not_lt' n hi]
    exact dotE_boolSign_self _ _

theorem dotE_eps_ne_B (n : ℕ) {i j : Fin (n - 1)} (hij : i ≠ j) (hadj : ¬ BAdj n i j) :
    dotE (toStdB (n - 1) (Pi.single i 1)) (toStdB (n - 1) (Pi.single j 1)) = 0 := by
  have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
  unfold BAdj at hadj
  by_cases hi : i.val + 1 < n - 1 <;> by_cases hj : j.val + 1 < n - 1
  · rw [toStdB_single_of_lt' n hi, toStdB_single_of_lt' n hj, dotE_add_left, dotE_add_right,
      dotE_add_right, dotE_single, dotE_single, dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> simp_all [boolSign] <;> omega
  · rw [toStdB_single_of_lt' n hi, toStdB_single_of_not_lt' n hj, dotE_add_left,
      dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> simp_all [boolSign] <;> omega
  · rw [toStdB_single_of_not_lt' n hi, toStdB_single_of_lt' n hj, dotE_add_right,
      dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> simp_all [boolSign] <;> omega
  · exact absurd (Fin.ext (by omega)) hij

theorem no_root_comb_B (n : ℕ) {i j : Fin (n - 1)} (hij : i ≠ j) (hadj : ¬ BAdj n i j) (p q : ℤ)
    (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a • (p • (Pi.single i 1 : Fin (n - 1) → ℤ)) + b • (q • (Pi.single j 1 : Fin (n - 1) → ℤ)) :
      Fin (n - 1) → ℤ) ∉ roots (isFiniteType_cartanB (n - 1)) ∅ := by
  intro hroot
  have e1 : (a • (p • (Pi.single i 1 : Fin (n - 1) → ℤ)) + b • (q • (Pi.single j 1 : Fin (n - 1) → ℤ)) :
      Fin (n - 1) → ℤ) = ((a : ℤ) * p) • (Pi.single i 1 : Fin (n - 1) → ℤ) +
        ((b : ℤ) * q) • Pi.single j 1 := by
    simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  have hL : ∀ c1 c2 : ℤ, dotE (c1 • toStdB (n - 1) (Pi.single i 1) + c2 • toStdB (n - 1) (Pi.single j 1))
      (c1 • toStdB (n - 1) (Pi.single i 1) + c2 • toStdB (n - 1) (Pi.single j 1)) =
        c1 ^ 2 * (if i.val + 1 < n - 1 then 2 else 1) +
        c2 ^ 2 * (if j.val + 1 < n - 1 then 2 else 1) := by
    intro c1 c2
    simp only [dotE_add_left, dotE_add_right, dotE_smul_left, dotE_smul_right]
    rw [dotE_eps_self_B, dotE_eps_self_B, dotE_eps_ne_B n hij hadj,
      dotE_comm (toStdB (n - 1) (Pi.single j 1)), dotE_eps_ne_B n hij hadj]
    ring
  rw [e1] at hroot
  rcases exists_toStdB_eq_of_mem_roots n hroot with ⟨x, y, hxy, s, t, h⟩ | ⟨x, s, h⟩
  · rw [toStdB_add, toStdB_smul, toStdB_smul] at h
    have h2 := congrArg (fun v => dotE v v) h
    rw [hL, dotE_root hxy s t] at h2
    have hp2 : p * p = 1 := by rcases hp with rfl | rfl <;> norm_num
    have hq2 : q * q = 1 := by rcases hq with rfl | rfl <;> norm_num
    have hna : ((a : ℤ) * p) ^ 2 = (a : ℤ) ^ 2 := by
      have : ((a : ℤ) * p) ^ 2 = (a : ℤ) ^ 2 * (p * p) := by ring
      rw [this, hp2, mul_one]
    have hnb : ((b : ℤ) * q) ^ 2 = (b : ℤ) ^ 2 := by
      have : ((b : ℤ) * q) ^ 2 = (b : ℤ) ^ 2 * (q * q) := by ring
      rw [this, hq2, mul_one]
    rw [hna, hnb] at h2
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hnotboth : i.val + 1 < n - 1 ∨ j.val + 1 < n - 1 := by
      by_contra hc
      push Not at hc
      have := i.isLt
      have := j.isLt
      exact hij (Fin.ext (by omega))
    by_cases hi : i.val + 1 < n - 1 <;> by_cases hj : j.val + 1 < n - 1
    · simp only [hi, hj, if_true] at h2; nlinarith
    · simp only [hi, hj, if_true, if_false] at h2; nlinarith
    · simp only [hi, hj, if_true, if_false] at h2; nlinarith
    · exact absurd hnotboth (by tauto)
  · rw [toStdB_add, toStdB_smul, toStdB_smul] at h
    have h2 := congrArg (fun v => dotE v v) h
    rw [hL, dotE_boolSign_self] at h2
    have hp2 : p * p = 1 := by rcases hp with rfl | rfl <;> norm_num
    have hq2 : q * q = 1 := by rcases hq with rfl | rfl <;> norm_num
    have hna : ((a : ℤ) * p) ^ 2 = (a : ℤ) ^ 2 := by
      have : ((a : ℤ) * p) ^ 2 = (a : ℤ) ^ 2 * (p * p) := by ring
      rw [this, hp2, mul_one]
    have hnb : ((b : ℤ) * q) ^ 2 = (b : ℤ) ^ 2 := by
      have : ((b : ℤ) * q) ^ 2 = (b : ℤ) ^ 2 * (q * q) := by ring
      rw [this, hq2, mul_one]
    rw [hna, hnb] at h2
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hnotboth : i.val + 1 < n - 1 ∨ j.val + 1 < n - 1 := by
      by_contra hc
      push Not at hc
      have := i.isLt
      have := j.isLt
      exact hij (Fin.ext (by omega))
    by_cases hi : i.val + 1 < n - 1 <;> by_cases hj : j.val + 1 < n - 1
    · simp only [hi, hj, if_true] at h2; nlinarith
    · simp only [hi, hj, if_true, if_false] at h2; nlinarith
    · simp only [hi, hj, if_true, if_false] at h2; nlinarith
    · exact absurd hnotboth (by tauto)

section Groups

variable (n : ℕ) {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem commute_rootGroups_B {i j : Fin (n - 1)} (hij : i ≠ j) (hadj : ¬ BAdj n i j)
    {γ δ : Fin (n - 1) → ℤ} (hγ : γ = Pi.single i 1 ∨ γ = -Pi.single i 1)
    (hδ : δ = Pi.single j 1 ∨ δ = -Pi.single j 1) {x y : spinGroup (quadMinus n F b c)}
    (hx : x ∈ (minusDatum n hirr).rootGroup γ) (hy : y ∈ (minusDatum n hirr).rootGroup δ) :
    x * y = y * x := by
  let hΦ := RootSystem.ofCartan (minusDatum n hirr).isFiniteType (minusDatum n hirr).divisible
  have hγr : γ ∈ (minusDatum n hirr).roots := by
    rcases hγ with rfl | rfl
    · exact hΦ.single_mem i
    · exact hΦ.neg_mem _ (hΦ.single_mem i)
  have hδr : δ ∈ (minusDatum n hirr).roots := by
    rcases hδ with rfl | rfl
    · exact hΦ.single_mem j
    · exact hΦ.neg_mem _ (hΦ.single_mem j)
  have hind : LinIndepPair γ δ := by
    intro a b hab
    have h1 := congrFun hab i
    have h2 := congrFun hab j
    have hij' : j ≠ i := Ne.symm hij
    rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
    · simp [Pi.single_apply, hij, hij'] at h1 h2
      exact ⟨h1, h2⟩
  have hcomm := (minusDatum_steinbergExtras n hirr).commutator_mem γ hγr δ hδr hind x hx y hy
  have hnone : ∀ ε, ε ∉ openCone (minusDatum n hirr).roots γ δ := by
    rintro ε ⟨hroot, a, b, ha, hb, rfl⟩
    have hp : ∃ p : ℤ, (p = 1 ∨ p = -1) ∧ γ = p • (Pi.single i 1 : Fin (n - 1) → ℤ) := by
      rcases hγ with rfl | rfl
      · exact ⟨1, Or.inl rfl, by simp⟩
      · exact ⟨-1, Or.inr rfl, by simp⟩
    have hq : ∃ q : ℤ, (q = 1 ∨ q = -1) ∧ δ = q • (Pi.single j 1 : Fin (n - 1) → ℤ) := by
      rcases hδ with rfl | rfl
      · exact ⟨1, Or.inl rfl, by simp⟩
      · exact ⟨-1, Or.inr rfl, by simp⟩
    obtain ⟨p, hp1, hpe⟩ := hp
    obtain ⟨q, hq1, hqe⟩ := hq
    have := no_root_comb_B n hij hadj p q hp1 hq1 a b ha hb
    rw [← hpe, ← hqe] at this
    exact this hroot
  have hbot : (⨆ ε ∈ openCone (minusDatum n hirr).roots γ δ, (minusDatum n hirr).rootGroup ε) = ⊥ :=
    iSup_eq_bot.mpr fun ε => iSup_eq_bot.mpr fun hε => absurd hε (hnone ε)
  rw [hbot, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

theorem rankOne_commute_B {i j : Fin (n - 1)} (hij : i ≠ j) (hadj : ¬ BAdj n i j) :
    rankOne (minusDatum n hirr).rootGroup i ≤
      Subgroup.centralizer (rankOne (minusDatum n hirr).rootGroup j :
        Set (spinGroup (quadMinus n F b c))) := by
  have key : ∀ γ : Fin (n - 1) → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ x ∈ (minusDatum n hirr).rootGroup γ,
      rankOne (minusDatum n hirr).rootGroup j ≤
        Subgroup.centralizer ({x} : Set (spinGroup (quadMinus n F b c))) := by
    intro γ hγ x hx
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (commute_rootGroups_B n hirr hij hadj hγ (Or.inl rfl) hx hy)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (commute_rootGroups_B n hirr hij hadj hγ (Or.inr rfl) hx hy)
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := key _ (Or.inl rfl) x hx hy
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x rfl).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := key _ (Or.inr rfl) x hx hy
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this x rfl).symm

end Groups
end SM
end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
