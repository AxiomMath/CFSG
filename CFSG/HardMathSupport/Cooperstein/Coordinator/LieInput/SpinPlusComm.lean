module

public import CFSG.LieType.CurtisTits.Spin
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMatrix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section P140
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock CFSG.LieType.Steinberg


section DComm

variable {n : ℕ}

@[expose] def DAdj (n : ℕ) (i j : Fin n) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 2 ≤ n) ∨ (j.val + 1 = i.val ∧ i.val + 2 ≤ n) ∨
    (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)

@[expose] def dotE (u w : Fin n → ℤ) : ℤ := ∑ c, u c * w c

theorem dotE_comm (u w : Fin n → ℤ) : dotE u w = dotE w u := by
  unfold dotE; exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem dotE_add_left (u v w : Fin n → ℤ) : dotE (u + v) w = dotE u w + dotE v w := by
  unfold dotE; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotE_add_right (u v w : Fin n → ℤ) : dotE u (v + w) = dotE u v + dotE u w := by
  unfold dotE; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dotE_smul_left (a : ℤ) (u w : Fin n → ℤ) : dotE (a • u) w = a * dotE u w := by
  unfold dotE; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

theorem dotE_smul_right (a : ℤ) (u w : Fin n → ℤ) : dotE u (a • w) = a * dotE u w := by
  rw [dotE_comm, dotE_smul_left, dotE_comm]

theorem dotE_sub_left (u v w : Fin n → ℤ) : dotE (u - v) w = dotE u w - dotE v w := by
  unfold dotE; simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dotE_sub_right (u v w : Fin n → ℤ) : dotE u (v - w) = dotE u v - dotE u w := by
  unfold dotE; simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dotE_single (x y : Fin n) (a b : ℤ) :
    dotE (Pi.single x a : Fin n → ℤ) (Pi.single y b) = if x = y then a * b else 0 := by
  unfold dotE
  by_cases hxy : x = y
  · subst hxy; simp [Pi.single_apply]
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = x
    · subst hc; simp [Pi.single_apply, Ne.symm hxy]
    · simp [Pi.single_apply, hc]

theorem dotE_root {x y : Fin n} (hxy : x ≠ y) (s t : Bool) :
    dotE (Pi.single x (boolSign s) + Pi.single y (boolSign t) : Fin n → ℤ)
      (Pi.single x (boolSign s) + Pi.single y (boolSign t)) = 2 := by
  rw [dotE_add_left, dotE_add_right, dotE_add_right, dotE_single, dotE_single, dotE_single,
    dotE_single, if_pos rfl, if_pos rfl, if_neg hxy, if_neg (Ne.symm hxy)]
  cases s <;> cases t <;> simp [boolSign]


theorem dotE_eps_self (hn : 3 ≤ n) (i : Fin n) :
    dotE (toStdD n (Pi.single i 1)) (toStdD n (Pi.single i 1)) = 2 := by
  by_cases hi : i.val + 1 < n
  · rw [toStdD_single_of_lt n hi, dotE_sub_left, dotE_sub_right, dotE_sub_right, dotE_single,
      dotE_single, dotE_single, dotE_single]
    have : i ≠ ⟨i.val + 1, hi⟩ := fun e => by have := congrArg Fin.val e; simp at this
    simp [this, Ne.symm this]
  · rw [toStdD_single_of_not_lt n hi (by omega), dotE_add_left, dotE_add_right, dotE_add_right,
      dotE_single, dotE_single, dotE_single, dotE_single]
    have : (⟨n - 2, by omega⟩ : Fin n) ≠ i := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    simp [this, Ne.symm this]

theorem dotE_eps_ne (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hadj : ¬ DAdj n i j) :
    dotE (toStdD n (Pi.single i 1)) (toStdD n (Pi.single j 1)) = 0 := by
  have hi' := i.isLt
  have hj' := j.isLt
  have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
  unfold DAdj at hadj
  by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
  · rw [toStdD_single_of_lt n hi, toStdD_single_of_lt n hj, dotE_sub_left, dotE_sub_right,
      dotE_sub_right, dotE_single, dotE_single, dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [toStdD_single_of_lt n hi, toStdD_single_of_not_lt n hj (by omega), dotE_sub_left,
      dotE_add_right, dotE_add_right, dotE_single, dotE_single, dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [toStdD_single_of_not_lt n hi (by omega), toStdD_single_of_lt n hj, dotE_add_left,
      dotE_sub_right, dotE_sub_right, dotE_single, dotE_single, dotE_single, dotE_single]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · exact absurd (Fin.ext (by omega)) hij


theorem no_root_comb (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hadj : ¬ DAdj n i j) (p q : ℤ)
    (hp : p = 1 ∨ p = -1) (hq : q = 1 ∨ q = -1) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a • (p • (Pi.single i 1 : Fin n → ℤ)) + b • (q • (Pi.single j 1 : Fin n → ℤ)) : Fin n → ℤ) ∉
      roots (isFiniteType_cartanD n) ∅ := by
  intro hroot
  obtain ⟨x, y, hxy, s, t, h⟩ := exists_toStdD_eq_of_mem_rootsD (by omega) hroot
  have e1 : (a • (p • (Pi.single i 1 : Fin n → ℤ)) + b • (q • (Pi.single j 1 : Fin n → ℤ)) :
      Fin n → ℤ) = ((a : ℤ) * p) • (Pi.single i 1 : Fin n → ℤ) + ((b : ℤ) * q) • Pi.single j 1 := by
    simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  rw [e1, toStdD_add, toStdD_smul, toStdD_smul] at h
  have hL : ∀ c1 c2 : ℤ, dotE (c1 • toStdD n (Pi.single i 1) + c2 • toStdD n (Pi.single j 1))
      (c1 • toStdD n (Pi.single i 1) + c2 • toStdD n (Pi.single j 1)) = 2 * c1 ^ 2 + 2 * c2 ^ 2 := by
    intro c1 c2
    simp only [dotE_add_left, dotE_add_right, dotE_smul_left, dotE_smul_right]
    rw [dotE_eps_self hn, dotE_eps_self hn, dotE_eps_ne hn hij hadj,
      dotE_comm (toStdD n (Pi.single j 1)), dotE_eps_ne hn hij hadj]
    ring
  have h2 := congrArg (fun v => dotE v v) h
  rw [hL, dotE_root hxy s t] at h2
  have hp2 : p * p = 1 := by rcases hp with rfl | rfl <;> norm_num
  have hq2 : q * q = 1 := by rcases hq with rfl | rfl <;> norm_num
  have : (a : ℤ) * a * (p * p) * 2 + (b : ℤ) * b * (q * q) * 2 = 2 := by
    linear_combination h2
  rw [hp2, hq2] at this
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

end DComm

section DCommGroups

variable {n : ℕ} {F : Type} [Field F]

theorem commute_rootGroups (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hadj : ¬ DAdj n i j)
    {γ δ : Fin n → ℤ} (hγ : γ = Pi.single i 1 ∨ γ = -Pi.single i 1)
    (hδ : δ = Pi.single j 1 ∨ δ = -Pi.single j 1) {x y : spinGroup (quadPlus n F)}
    (hx : x ∈ (plusDatum n F hn).rootGroup γ) (hy : y ∈ (plusDatum n F hn).rootGroup δ) :
    x * y = y * x := by
  let hΦ := RootSystem.ofCartan (plusDatum n F hn).isFiniteType (plusDatum n F hn).divisible
  have hγr : γ ∈ (plusDatum n F hn).roots := by
    rcases hγ with rfl | rfl
    · exact hΦ.single_mem i
    · exact hΦ.neg_mem _ (hΦ.single_mem i)
  have hδr : δ ∈ (plusDatum n F hn).roots := by
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
  have hcomm := (plusDatum_steinbergExtras (K := F) hn).commutator_mem γ hγr δ hδr hind x hx y hy
  have hnone : ∀ ε, ε ∉ openCone (plusDatum n F hn).roots γ δ := by
    rintro ε ⟨hroot, a, b, ha, hb, rfl⟩
    have hp : ∃ p : ℤ, (p = 1 ∨ p = -1) ∧ γ = p • (Pi.single i 1 : Fin n → ℤ) := by
      rcases hγ with rfl | rfl
      · exact ⟨1, Or.inl rfl, by simp⟩
      · exact ⟨-1, Or.inr rfl, by simp⟩
    have hq : ∃ q : ℤ, (q = 1 ∨ q = -1) ∧ δ = q • (Pi.single j 1 : Fin n → ℤ) := by
      rcases hδ with rfl | rfl
      · exact ⟨1, Or.inl rfl, by simp⟩
      · exact ⟨-1, Or.inr rfl, by simp⟩
    obtain ⟨p, hp1, hpe⟩ := hp
    obtain ⟨q, hq1, hqe⟩ := hq
    have := no_root_comb hn hij hadj p q hp1 hq1 a b ha hb
    rw [← hpe, ← hqe] at this
    exact this hroot
  have hbot : (⨆ ε ∈ openCone (plusDatum n F hn).roots γ δ, (plusDatum n F hn).rootGroup ε) = ⊥ :=
    iSup_eq_bot.mpr fun ε => iSup_eq_bot.mpr fun hε => absurd hε (hnone ε)
  rw [hbot, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm


theorem rankOne_commute (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hadj : ¬ DAdj n i j) :
    CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i ≤
      Subgroup.centralizer (CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup j :
        Set (spinGroup (quadPlus n F))) := by
  have key : ∀ γ : Fin n → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ x ∈ (plusDatum n F hn).rootGroup γ,
      CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup j ≤
        Subgroup.centralizer ({x} : Set (spinGroup (quadPlus n F))) := by
    intro γ hγ x hx
    refine sup_le ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (commute_rootGroups hn hij hadj hγ (Or.inl rfl) hx hy)
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (commute_rootGroups hn hij hadj hγ (Or.inr rfl) hx hy)
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

end DCommGroups






end P140

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
