module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainAbelCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1N
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainTransfer

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def s0Mat (ε : Eps) (i : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  toMat 6 6 (s0Get ε i)

section Facts

variable (ε : Eps)

theorem s0_facts :
    s0Get ε 0 = id6 ∧
    (∀ i < 64, ∀ j < 64, i ≠ j → ∃ z < 64,
      bmulVec 6 6 (s0Get ε i) z ≠ bmulVec 6 6 (s0Get ε j) z) ∧
    (∀ k < 6, s0Idx ε (uRows ε k) < 64 ∧ s0Get ε (s0Idx ε (uRows ε k)) = uRows ε k) ∧
    (∀ i < 64, ∀ j < 64, tabGet (mulTab ε) i j < 64 ∧
      s0Get ε (tabGet (mulTab ε) i j) = bmul 6 6 (s0Get ε i) (s0Get ε j)) ∧
    (∀ i < 64, ∃ j < 64, tabGet (mulTab ε) i j = 0) ∧
    (∀ y < 64, tabGet (mulTab ε) 0 y = y) ∧
    (∀ i < 63, treeOk ε (i + 1) = true) := by
  have h := s0Check_spec ε
  simp only [s0Check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.any_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h0⟩, hd⟩, hu⟩, ht⟩, hinv⟩, hid⟩, htree⟩ := h
  refine ⟨h0, fun i hi j hj hij => ?_, hu, ht, hinv, hid, htree⟩
  rcases hd i hi j hj with h | h
  · exact absurd h hij
  · exact h

theorem s0Mat_zero : s0Mat ε 0 = 1 := by
  rw [s0Mat, (s0_facts ε).1, toMat_id6]

theorem tab_lt {i j : ℕ} (hi : i < 64) (hj : j < 64) : tabGet (mulTab ε) i j < 64 :=
  ((s0_facts ε).2.2.2.1 i hi j hj).1

theorem s0Mat_mul {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    s0Mat ε i * s0Mat ε j = s0Mat ε (tabGet (mulTab ε) i j) := by
  rw [s0Mat, s0Mat, s0Mat, ((s0_facts ε).2.2.2.1 i hi j hj).2, toMat_bmul]

theorem uRows_eq_s0Mat {k : ℕ} (hk : k < 6) :
    toMat 6 6 (uRows ε k) = s0Mat ε (s0Idx ε (uRows ε k)) := by
  rw [s0Mat, ((s0_facts ε).2.2.1 k hk).2]

theorem s0Idx_lt {k : ℕ} (hk : k < 6) : s0Idx ε (uRows ε k) < 64 :=
  ((s0_facts ε).2.2.1 k hk).1

theorem exists_inv {i : ℕ} (hi : i < 64) : ∃ j < 64, s0Mat ε i * s0Mat ε j = 1 := by
  obtain ⟨j, hj, h⟩ := (s0_facts ε).2.2.2.2.1 i hi
  refine ⟨j, hj, ?_⟩
  rw [s0Mat_mul ε hi hj, h, s0Mat_zero]

theorem tab_zero_left {y : ℕ} (hy : y < 64) : tabGet (mulTab ε) 0 y = y :=
  (s0_facts ε).2.2.2.2.2.1 y hy

theorem eq_of_mulVec_eq {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (h : ∀ v, s0Mat ε i *ᵥ v = s0Mat ε j *ᵥ v) : i = j := by
  by_contra hij
  obtain ⟨z, -, hz⟩ := (s0_facts ε).2.1 i hi j hj hij
  apply hz
  have := h (toVec 6 z)
  rw [s0Mat, s0Mat, mulVec_toVec, mulVec_toVec] at this
  exact toVec_injective (bmulVec_lt _ _) (bmulVec_lt _ _) this

theorem tab_comm_of_commute {i j : ℕ} (hi : i < 64) (hj : j < 64)
    (h : s0Mat ε i * s0Mat ε j = s0Mat ε j * s0Mat ε i) :
    tabGet (mulTab ε) i j = tabGet (mulTab ε) j i := by
  refine eq_of_mulVec_eq ε (tab_lt ε hi hj) (tab_lt ε hj hi) fun v => ?_
  rw [← s0Mat_mul ε hi hj, ← s0Mat_mul ε hj hi, h]

end Facts

section Masks

@[expose] def maskOf (X : Finset ℕ) : ℕ := bitsOf 64 fun i => decide (i ∈ X)

theorem testBit_maskOf (X : Finset ℕ) (i : ℕ) :
    (maskOf X).testBit i = (decide (i < 64) && decide (i ∈ X)) := by
  rw [maskOf, testBit_bitsOf]

theorem testBit_imgMask (T : Array (Array ℕ)) (m y b : ℕ) :
    (imgMask T m y).testBit b = true ↔
      b < 64 ∧ ∃ a < 64, m.testBit a = true ∧ tabGet T a y = b := by
  simp [imgMask, testBit_bitsOf, List.any_eq_true, List.mem_range]

theorem closeY_mono (T : Array (Array ℕ)) (y : ℕ) (n : ℕ) {m a : ℕ}
    (h : m.testBit a = true) : (closeY T y n m).testBit a = true := by
  induction n generalizing m with
  | zero => exact h
  | succ n ih =>
    rw [closeY]
    exact ih (by rw [Nat.testBit_or, h, Bool.true_or])

theorem closeY_subset (T : Array (Array ℕ)) (y : ℕ) (X : ℕ → Prop)
    (hX : ∀ a < 64, X a → X (tabGet T a y)) (n : ℕ) {m : ℕ}
    (hm : ∀ a, m.testBit a = true → a < 64 ∧ X a) :
    ∀ a, (closeY T y n m).testBit a = true → a < 64 ∧ X a := by
  induction n generalizing m with
  | zero => exact hm
  | succ n ih =>
    rw [closeY]
    refine ih fun b hb => ?_
    rw [Nat.testBit_or, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hm b hb
    · obtain ⟨hb64, a, ha, ham, rfl⟩ := (testBit_imgMask T m y b).1 hb
      exact ⟨hb64, hX a ha (hm a ham).2⟩

theorem closeY_mem (T : Array (Array ℕ)) {y : ℕ} (hy : y < 64) (hT : tabGet T 0 y = y)
    (n : ℕ) {m : ℕ} (hm : m.testBit 0 = true) : (closeY T y (n + 1) m).testBit y = true := by
  rw [closeY]
  refine closeY_mono T y n ?_
  rw [Nat.testBit_or, Bool.or_eq_true]
  exact Or.inr ((testBit_imgMask T m y y).2 ⟨hy, 0, by norm_num, hm, hT⟩)

theorem testBit_one_iff (a : ℕ) : (1 : ℕ).testBit a = true ↔ a = 0 := by
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
  simp [eq_comm]

variable (ε : Eps)

theorem abel_facts :
    1 ∈ abelMasks ε ∧ (∀ m ∈ abelMasks ε, m < 2 ^ 64) ∧
    (∀ m ∈ abelMasks ε, ∀ y < 64, m.testBit y = false → commAll (mulTab ε) m y = true →
      closeY (mulTab ε) y 8 m ∈ abelMasks ε) ∧
    (∀ m ∈ abelMasks ε, popcount64 m * fixMask ε m ≤ 64) := by
  have h := abelCheck_spec ε
  simp only [abelCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    decide_eq_true_eq, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun m hm y hy hmy hc => ?_, h4⟩
  rcases h3 m hm y hy with (h | h) | h
  · rw [hmy] at h; exact absurd h Bool.false_ne_true
  · rw [hc] at h; exact absurd h Bool.noConfusion
  · exact h

theorem maskOf_mem_abelMasks {X : Finset ℕ} (hX64 : ∀ a ∈ X, a < 64) (h0 : 0 ∈ X)
    (hmul : ∀ a ∈ X, ∀ b ∈ X, tabGet (mulTab ε) a b ∈ X)
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, tabGet (mulTab ε) a b = tabGet (mulTab ε) b a) :
    maskOf X ∈ abelMasks ε := by
  obtain ⟨h1, hlt, hstep, -⟩ := abel_facts ε
  suffices key : ∀ n, ∀ m ∈ abelMasks ε, (∀ a, m.testBit a = true → a < 64 ∧ a ∈ X) →
      m.testBit 0 = true → (X.filter fun a => m.testBit a = false).card ≤ n →
      maskOf X ∈ abelMasks ε from
    key _ 1 h1 (fun a ha => by rw [(testBit_one_iff a).1 ha]; exact ⟨by norm_num, h0⟩)
      ((testBit_one_iff 0).2 rfl) le_rfl
  intro n
  induction n with
  | zero =>
    intro m hm hmX hm0 hcard
    have hall : ∀ a ∈ X, m.testBit a = true := fun a ha => by
      by_contra hne
      have : a ∈ X.filter fun a => m.testBit a = false :=
        Finset.mem_filter.2 ⟨ha, by simpa using hne⟩
      have := Finset.card_pos.2 ⟨a, this⟩
      omega
    have : m = maskOf X := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [testBit_maskOf]
      by_cases hi : i < 64
      · by_cases hiX : i ∈ X
        · simp [hi, hiX, hall i hiX]
        · have : m.testBit i = false := by
            by_contra hne
            exact hiX (hmX i (by simpa using hne)).2
          simp [hi, hiX, this]
      · have : m.testBit i = false :=
          Nat.testBit_lt_two_pow ((hlt m hm).trans_le (Nat.pow_le_pow_right (by norm_num)
            (by omega)))
        simp [hi, this]
    exact this ▸ hm
  | succ n ih =>
    intro m hm hmX hm0 hcard
    by_cases hall : ∀ a ∈ X, m.testBit a = true
    · refine ih m hm hmX hm0 ?_
      have : X.filter (fun a => m.testBit a = false) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun a ha => by simp [hall a ha]
      rw [this, Finset.card_empty]
      exact Nat.zero_le _
    · push Not at hall
      obtain ⟨y, hyX, hym⟩ := hall
      have hy := hX64 y hyX
      have hym' : m.testBit y = false := by simpa using hym
      have hc : commAll (mulTab ε) m y = true := by
        simp only [commAll, List.all_eq_true, List.mem_range, Bool.or_eq_true,
          Bool.not_eq_true', beq_iff_eq]
        intro a ha
        by_cases hma : m.testBit a = true
        · exact Or.inr (hcomm a (hmX a hma).2 y hyX)
        · exact Or.inl (by simpa using hma)
      have hm' := hstep m hm y hy hym' hc
      have hsub := closeY_subset (mulTab ε) y (· ∈ X) (fun a _ ha => hmul a ha y hyX) 8 hmX
      refine ih _ hm' hsub (closeY_mono _ _ _ hm0) ?_
      have hyc := closeY_mem (mulTab ε) hy (tab_zero_left ε hy) 7 hm0
      have hlt' : (X.filter fun a => (closeY (mulTab ε) y 8 m).testBit a = false).card <
          (X.filter fun a => m.testBit a = false).card := by
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun h => ?_⟩
        · simp only [Finset.mem_filter] at ha ⊢
          refine ⟨ha.1, ?_⟩
          by_contra hne
          have := closeY_mono (mulTab ε) y 8 (m := m) (a := a) (by simpa using hne)
          rw [this] at ha
          exact Bool.noConfusion ha.2
        · have : y ∈ X.filter fun a => m.testBit a = false := Finset.mem_filter.2 ⟨hyX, hym'⟩
          have := Finset.mem_filter.1 (h this)
          rw [hyc] at this
          exact Bool.noConfusion this.2
      omega

theorem popcount64_maskOf {X : Finset ℕ} (hX64 : ∀ a ∈ X, a < 64) :
    popcount64 (maskOf X) = X.card := by
  have h : popcount64 (maskOf X) =
      ((Finset.range 64).filter fun a => (maskOf X).testBit a = true).card := by
    rw [popcount64, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp only [Bool.decide_eq_true]
  rw [h]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, testBit_maskOf, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨hX64 a h, hX64 a h, h⟩⟩

theorem fixMask_maskOf (ε : Eps) {X : Finset ℕ} (hX64 : ∀ a ∈ X, a < 64) :
    fixMask ε (maskOf X) =
      (Finset.univ.filter fun v : V6 => ∀ a ∈ X, s0Mat ε a *ᵥ v = v).card := by
  have h : fixMask ε (maskOf X) = ((Finset.range 64).filter fun z =>
      ((List.range 64).all fun a => !(maskOf X).testBit a ||
        bmulVec 6 6 (s0Get ε a) z == z) = true).card := by
    rw [fixMask, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    simp only [Bool.decide_eq_true]
  rw [h, ← card_filter_vecBits]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, testBit_maskOf, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · intro hv a ha
    rcases hv a (hX64 a ha) with (h | h) | h
    · exact absurd (hX64 a ha) h
    · exact absurd ha h
    · rw [← toVec_vecBits (s0Mat ε a *ᵥ v), s0Mat, vecBits_mulVec, h, toVec_vecBits]
  · intro hv a ha
    by_cases haX : a ∈ X
    · refine Or.inr ?_
      have := congrArg vecBits (hv a haX)
      rwa [s0Mat, vecBits_mulVec] at this
    · exact Or.inl (Or.inr haX)

end Masks

section Group

variable {G : Type*} [Group G]

structure UData (ε : Eps) (U Q : Subgroup G) (ψ : V6 → G) (u : Fin 6 → G) : Prop where
  u_mem : ∀ k, u k ∈ U
  u_act : ∀ k v, u k * ψ v * (u k)⁻¹ = ψ (toMat 6 6 (uRows ε k) *ᵥ v)
  U_le : U ≤ closure ((Q : Set G) ∪ Set.range u)

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p : Fin 6 → G} {u : Fin 6 → G}

theorem UData.closure_le_P (hR : RadicalData ε L U Q P a ψ p) (hu : UData ε U Q ψ u) :
    closure ((Q : Set G) ∪ Set.range u) ≤ P := by
  rw [closure_le]
  rintro x (hx | ⟨k, rfl⟩)
  · exact hR.U_le_P (hR.Q_le_U hx)
  · exact hR.U_le_P (hu.u_mem k)

theorem UData.exists_s0 (hR : RadicalData ε L U Q P a ψ p) (hu : UData ε U Q ψ u) {x : G}
    (hx : x ∈ U) : ∃ i < 64, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v := by
  have hN : ∀ y ∈ closure ((Q : Set G) ∪ Set.range u), y ∈ normalizer (Q : Set G) :=
    fun y hy => hR.P_le_normalizer (hu.closure_le_P hR hy)
  have key : ∀ y ∈ closure ((Q : Set G) ∪ Set.range u),
      ∃ i < 64, ∀ v, lin ψ y v = s0Mat ε i *ᵥ v := by
    intro y hy
    induction hy using closure_induction with
    | mem y hy =>
      rcases hy with hy | ⟨k, rfl⟩
      · exact ⟨0, by norm_num, fun v => by rw [hR.lin_of_mem_Q hy, s0Mat_zero, one_mulVec]⟩
      · refine ⟨s0Idx ε (uRows ε k), s0Idx_lt ε k.isLt, fun v => ?_⟩
        rw [← uRows_eq_s0Mat ε k.isLt,
          hR.lin_eq_iff (hN _ (subset_closure (Or.inr ⟨k, rfl⟩)))]
        exact hu.u_act k v
    | one => exact ⟨0, by norm_num, fun v => by rw [hR.lin_one, s0Mat_zero, one_mulVec]⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨i, hi, hyi⟩ := ihy
      obtain ⟨j, hj, hzj⟩ := ihz
      refine ⟨_, tab_lt ε hi hj, fun v => ?_⟩
      rw [hR.lin_mul (hN y hy) (hN z hz), hzj, hyi, mulVec_mulVec, s0Mat_mul ε hi hj]
    | inv y hy ihy =>
      obtain ⟨i, hi, hyi⟩ := ihy
      obtain ⟨j, hj, hij⟩ := exists_inv ε hi
      refine ⟨j, hj, fun v => ?_⟩
      have h1 : lin ψ y (s0Mat ε j *ᵥ v) = v := by rw [hyi, mulVec_mulVec, hij, one_mulVec]
      conv_lhs => rw [← h1]
      rw [hR.lin_inv' (hN y hy)]
  exact key x (hu.U_le hx)

theorem UData.exists_mem_U (hR : RadicalData ε L U Q P a ψ p) (hu : UData ε U Q ψ u) {i : ℕ}
    (hi : i < 64) : ∃ x ∈ U, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, one_mem _, fun v => by rw [hR.lin_one, s0Mat_zero, one_mulVec]⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have ht := (s0_facts ε).2.2.2.2.2.2 i' (by omega)
      simp only [treeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
      obtain ⟨⟨hj, hk⟩, he⟩ := ht
      obtain ⟨x, hxU, hx⟩ := ih _ hj (by omega)
      refine ⟨u ⟨_, hk⟩ * x, mul_mem (hu.u_mem _) hxU, fun v => ?_⟩
      have hNu := hR.P_le_normalizer (hR.U_le_P (hu.u_mem ⟨_, hk⟩))
      have hNx := hR.P_le_normalizer (hR.U_le_P hxU)
      rw [hR.lin_mul hNu hNx, hx]
      have hlu : ∀ w, lin ψ (u ⟨_, hk⟩) w =
          toMat 6 6 (uRows ε ((s0Tree ε).getD (i' + 1) (0, 0)).1) *ᵥ w := fun w => by
        rw [hR.lin_eq_iff hNu]
        exact hu.u_act _ _
      rw [hlu, mulVec_mulVec, s0Mat, s0Mat, ← toMat_bmul, he]

theorem UData.card_le_of_abelian [Finite G] {t : G} (hS : Setup ε t L U Q P a ψ p)
    (hu : UData ε U Q ψ u) {A : Subgroup G} (hAU : A ≤ U)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 64 := by
  classical
  have hR := hS.rad
  have hAN' : A ≤ normalizer (Q : Set G) := fun x hx => hR.P_le_normalizer (hR.U_le_P (hAU hx))
  set X : Finset ℕ := (Finset.range 64).filter
    fun i => ∃ x ∈ A, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v with hXdef
  have hmemX : ∀ {i}, i ∈ X ↔ i < 64 ∧ ∃ x ∈ A, ∀ v, lin ψ x v = s0Mat ε i *ᵥ v := by
    intro i
    rw [hXdef, Finset.mem_filter, Finset.mem_range]
  have hX64 : ∀ i ∈ X, i < 64 := fun i hi => (hmemX.1 hi).1
  have h0 : 0 ∈ X :=
    hmemX.2 ⟨by norm_num, 1, one_mem _, fun v => by rw [hR.lin_one, s0Mat_zero, one_mulVec]⟩
  have hmul : ∀ i ∈ X, ∀ j ∈ X, tabGet (mulTab ε) i j ∈ X := by
    intro i hi j hj
    obtain ⟨hi64, x, hx, hxi⟩ := hmemX.1 hi
    obtain ⟨hj64, y, hy, hyj⟩ := hmemX.1 hj
    refine hmemX.2 ⟨tab_lt ε hi64 hj64, x * y, mul_mem hx hy, fun v => ?_⟩
    rw [hR.lin_mul (hAN' hx) (hAN' hy), hyj, hxi, mulVec_mulVec, s0Mat_mul ε hi64 hj64]
  have hcomm : ∀ i ∈ X, ∀ j ∈ X, tabGet (mulTab ε) i j = tabGet (mulTab ε) j i := by
    intro i hi j hj
    obtain ⟨hi64, x, hx, hxi⟩ := hmemX.1 hi
    obtain ⟨hj64, y, hy, hyj⟩ := hmemX.1 hj
    refine tab_comm_of_commute ε hi64 hj64 (Matrix.ext_iff_mulVec.2 fun v => ?_)
    have e1 : lin ψ (x * y) v = (s0Mat ε i * s0Mat ε j) *ᵥ v := by
      rw [hR.lin_mul (hAN' hx) (hAN' hy), hyj, hxi, mulVec_mulVec]
    have e2 : lin ψ (y * x) v = (s0Mat ε j * s0Mat ε i) *ᵥ v := by
      rw [hR.lin_mul (hAN' hy) (hAN' hx), hxi, hyj, mulVec_mulVec]
    rw [← e1, ← e2, hAc x hx y hy]
  have hb := (abel_facts ε).2.2.2 _ (maskOf_mem_abelMasks ε hX64 h0 hmul hcomm)
  rw [popcount64_maskOf hX64, fixMask_maskOf ε hX64] at hb
  let φ : A →* Equiv.Perm V6 := hR.linHom.comp (Subgroup.inclusion hAN')
  have hφ : ∀ (x : A) v, φ x v = lin ψ x v := fun x v => rfl
  have hrange : Nat.card φ.range ≤ X.card := by
    have : ∀ σ : φ.range, ∃ i : X, ∀ v, (σ : Equiv.Perm V6) v = s0Mat ε i *ᵥ v := by
      rintro ⟨σ, x, rfl⟩
      obtain ⟨i, hi, hxi⟩ := hu.exists_s0 hR (hAU x.2)
      exact ⟨⟨i, hmemX.2 ⟨hi, x, x.2, hxi⟩⟩, fun v => by rw [hφ]; exact hxi v⟩
    choose f hf using this
    have hinj : Function.Injective f := by
      intro σ τ h
      exact Subtype.ext (Equiv.ext fun v => by rw [hf σ v, hf τ v, h])
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_eq_finsetCard] at this
  have hker : Nat.card φ.ker ≤
      (Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v).card := by
    have hQ : ∀ x : φ.ker, ((x : A) : G) ∈ Q := by
      intro x
      have h1 : ∀ v, lin ψ (x : A) v = v := fun v => by
        rw [← hφ, MonoidHom.mem_ker.1 x.2]; rfl
      refine hS.mem_Q_of_mem_P (hR.U_le_P (hAU (x : A).2)) (mem_centralizer_iff.2 fun q hq => ?_)
      obtain ⟨v, rfl⟩ := hR.mem_ψ q hq
      have := (hR.lin_eq_iff (hAN' (x : A).2) v v).1 (h1 v)
      calc ψ v * ((x : A) : G) = (x : A) * ψ v * ((x : A) : G)⁻¹ * (x : A) := by rw [this]
        _ = (x : A) * ψ v := by group
    have hfix : ∀ x : φ.ker, coord ψ ((x : A) : G) ∈
        Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v := by
      intro x
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩
      obtain ⟨-, y, hy, hyi⟩ := hmemX.1 hi
      rw [← hyi, hR.lin_eq_iff (hAN' hy), hR.ψ_coord (hQ x)]
      rw [hAc y hy _ (x : A).2, mul_inv_cancel_right]
    let f : φ.ker → {v // v ∈ Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v} :=
      fun x => ⟨_, hfix x⟩
    have hinj : Function.Injective f := by
      intro x y h
      have h' : coord ψ ((x : A) : G) = coord ψ ((y : A) : G) := congrArg Subtype.val h
      have := congrArg ψ h'
      rw [hR.ψ_coord (hQ x), hR.ψ_coord (hQ y)] at this
      exact Subtype.ext (Subtype.ext this)
    have := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_eq_finsetCard] at this
  have hcard : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard]
  calc Nat.card φ.ker * Nat.card φ.range ≤
        (Finset.univ.filter fun v : V6 => ∀ i ∈ X, s0Mat ε i *ᵥ v = v).card * X.card :=
        Nat.mul_le_mul hker hrange
    _ ≤ 64 := by rw [mul_comm]; exact hb

theorem relIndex_U_TH {t : G} (hS : Setup ε t L U Q P a ψ p) :
    U.relIndex (U ⊔ zpowers t) = 2 := by
  have htU : t ∉ U := fun h => hS.shape.not_mem (hS.rad.U_le_L h)
  rw [relIndex_eq_two_iff]
  refine ⟨t, mem_sup_right (mem_zpowers t), fun b hb => ?_⟩
  obtain ⟨y, hy, rfl | rfl⟩ := (hS.shape.mem_sup_iff hS.rad.U_le_L).1 hb
  · exact Or.inr ⟨hy, fun h => htU (by simpa using mul_mem (inv_mem hy) h)⟩
  · refine Or.inl ⟨by rw [mul_assoc, hS.shape.mul_self, mul_one]; exact hy, fun h => htU ?_⟩
    simpa using mul_mem (inv_mem hy) h

theorem UData.abelBound [Finite G] {t : G} (hS : Setup ε t L U Q P a ψ p)
    (hu : UData ε U Q ψ u) : AbelBound t := by
  intro B hBC hB2 hBc
  have hR := hS.rad
  have hDK : U ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (hR.U_le_L.trans hS.shape.le_centralizer)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hD : IsPGroup 2 (U ⊔ zpowers t : Subgroup G) := hS.shape.isPGroup_sup hR.U_le_L hR.U_pgroup
  obtain ⟨k, -, hkB⟩ := exists_conj_le_of_maximal hDK hD
    (fun T hT hT2 hDT => hS.shape.sylow T hT hT2 hDT) hBC hB2
  set B' : Subgroup G := B.map (MulAut.conj k).toMonoidHom with hB'
  have hcardB : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hB'D : B' ≤ U ⊔ zpowers t := by
    rintro _ ⟨x, hx, rfl⟩
    exact hkB x hx
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show k * x * k⁻¹ * (k * y * k⁻¹) = k * (x * y) * k⁻¹ by group, hBc x hx y hy]
    group
  have hA : Nat.card (U ⊓ B' : Subgroup G) ≤ 64 :=
    hu.card_le_of_abelian hS inf_le_left fun x hx y hy => hB'c x hx.2 y hy.2
  have hUD := relIndex_U_TH hS
  have hidx : U.relIndex B' ≤ 2 :=
    (relIndex_le_of_le_right hB'D (by rw [hUD]; norm_num)).trans hUD.le
  have hm := relIndex_mul_card (H := U) (K := B')
  rw [← hcardB, ← hm]
  calc U.relIndex B' * Nat.card (U ⊓ B' : Subgroup G) ≤ 2 * 64 := Nat.mul_le_mul hidx hA
    _ = 128 := by norm_num

end Group

end CFSG.EvenSmallLie.OmegaEight.Chain
