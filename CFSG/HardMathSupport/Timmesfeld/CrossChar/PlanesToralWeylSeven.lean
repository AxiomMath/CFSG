module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralCycle

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {M : Type*} [CommGroup M]


section Orbit

variable {w : WeylGroup τ} {α : Fin τ.rank → ℤ}

omit [CommGroup M] in
private theorem pow_mul_smul_of_fix7 {x : Fin τ.rank → ℤ} {d : ℕ} (h : w ^ d • x = x) :
    ∀ e : ℕ, w ^ (d * e) • x = x
  | 0 => by rw [mul_zero, pow_zero, one_smul]
  | e + 1 => by rw [Nat.mul_succ, pow_add, mul_smul, h, pow_mul_smul_of_fix7 h e]

omit [CommGroup M] in
private theorem iform_self_nonneg7 (v : Fin τ.rank → ℤ) : 0 ≤ iform v v := by
  by_cases h : v = 0
  · rw [h]
    simp [iform]
  · exact (iform_self_pos h).le

omit [CommGroup M] in
private theorem iform_pow_add_smul7 (x : Fin τ.rank → ℤ) (i d : ℕ) :
    iform (w ^ i • x) (w ^ (i + d) • x) = iform x (w ^ d • x) := by
  rw [pow_add, mul_smul, iform_smul]

omit [CommGroup M] in
theorem iform_pow_seven_sub (hP : OrbitZero 7 w) (hαp : ∀ v, w • v = v → iform α v = 0)
    {d e : ℕ} (hde : d + e = 7) : iform α (w ^ e • α) = iform α (w ^ d • α) := by
  have h : w ^ d • w ^ e • α = α := by
    rw [← mul_smul, ← pow_add, hde, hP.pow_smul_self hαp]
  calc iform α (w ^ e • α) = iform (w ^ d • α) (w ^ d • w ^ e • α) := (iform_smul _ _ _).symm
    _ = iform α (w ^ d • α) := by rw [h, iform_comm]

omit [CommGroup M] in
theorem iform_pow_pow_seven (hP : OrbitZero 7 w) (hαp : ∀ v, w • v = v → iform α v = 0)
    {i j : ℕ} (hi : i < 7) (hj : j < 7) :
    iform (w ^ i • α) (w ^ j • α) = iform α (w ^ ((j + 7 - i) % 7) • α) := by
  rcases le_or_gt i j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [iform_pow_add_smul7, show (i + d + 7 - i) % 7 = d by omega]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [iform_comm, iform_pow_add_smul7, show (j + 7 - (j + d)) % 7 = 7 - d by omega,
      iform_pow_seven_sub hP hαp (show d + (7 - d) = 7 by omega)]

omit [CommGroup M] in
theorem iform_orbit_sum_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) (hP : OrbitZero 7 w)
    (hα : IsRoot τ α) (hαp : ∀ v, w • v = v → iform α v = 0) :
    iform α (w ^ 1 • α) + iform α (w ^ 2 • α) + iform α (w ^ 3 • α) = -1 := by
  have hs : iform α (∑ k ∈ Finset.range 7, w ^ k • α) = 0 := by
    rw [hP α hαp]
    simp [iform]
  rw [iform_finset_sum_right] at hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul] at hs
  rw [hSL α hα, iform_pow_seven_sub hP hαp (show 3 + 4 = 7 from rfl),
    iform_pow_seven_sub hP hαp (show 2 + 5 = 7 from rfl),
    iform_pow_seven_sub hP hαp (show 1 + 6 = 7 from rfl)] at hs
  omega

omit [CommGroup M] in
theorem smul_eq_of_pow_smul_eq_seven (hP : OrbitZero 7 w)
    (hαp : ∀ v, w • v = v → iform α v = 0) {d : ℕ} (hd : d % 7 ≠ 0) (h : w ^ d • α = α) :
    w • α = α := by
  obtain ⟨e, he⟩ : ∃ e, d * e % 7 = 1 := by
    have : d % 7 = 1 ∨ d % 7 = 2 ∨ d % 7 = 3 ∨ d % 7 = 4 ∨ d % 7 = 5 ∨ d % 7 = 6 := by omega
    rcases this with h1 | h1 | h1 | h1 | h1 | h1
    exacts [⟨1, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
      ⟨6, by omega⟩]
  have h1 := pow_mul_smul_of_fix7 h e
  have h7 : w ^ 7 • w • α = w • α := hP.pow_smul_self (perp_smul hαp)
  rw [← Nat.div_add_mod (d * e) 7, he, pow_succ, mul_smul, pow_mul_smul_of_fix7 h7] at h1
  exact h1

omit [CommGroup M] in
theorem orbit_bounds_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) (hP : OrbitZero 7 w)
    (hα : IsRoot τ α) (hαp : ∀ v, w • v = v → iform α v = 0) {d : ℕ} (hd : d % 7 ≠ 0) :
    -1 ≤ iform α (w ^ d • α) ∧ iform α (w ^ d • α) ≤ 1 := by
  have hr : IsRoot τ (w ^ d • α) := IsRoot.smul hα _
  have hfix : w • α ≠ α := fun e => by
    have := hαp α e
    rw [hSL α hα] at this
    omega
  have n1 : w ^ d • α ≠ α := fun e => hfix (smul_eq_of_pow_smul_eq_seven hP hαp hd e)
  have n2 : w ^ d • α ≠ -α := fun e => by
    have e2 : w ^ (2 * d) • α = α := by
      rw [two_mul, pow_add, mul_smul, e, smul_neg, e, neg_neg]
    exact hfix (smul_eq_of_pow_smul_eq_seven hP hαp (by omega) e2)
  exact iform_le_one_SL hSL hα hr (Ne.symm n1) fun e => n2 (neg_eq_iff_eq_neg.2 e).symm

omit [CommGroup M] in
theorem orbit_cases_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) (hP : OrbitZero 7 w)
    (hα : IsRoot τ α) (hαp : ∀ v, w • v = v → iform α v = 0) :
    (iform α (w ^ 1 • α) = -1 ∧ iform α (w ^ 2 • α) = 0 ∧ iform α (w ^ 3 • α) = 0) ∨
      (iform α (w ^ 1 • α) = 0 ∧ iform α (w ^ 2 • α) = -1 ∧ iform α (w ^ 3 • α) = 0) ∨
      (iform α (w ^ 1 • α) = 0 ∧ iform α (w ^ 2 • α) = 0 ∧ iform α (w ^ 3 • α) = -1) := by
  have hs := iform_orbit_sum_seven hSL hP hα hαp
  obtain ⟨b1, b1'⟩ := orbit_bounds_seven hSL hP hα hαp (d := 1) (by norm_num)
  obtain ⟨b2, b2'⟩ := orbit_bounds_seven hSL hP hα hαp (d := 2) (by norm_num)
  obtain ⟨b3, b3'⟩ := orbit_bounds_seven hSL hP hα hαp (d := 3) (by norm_num)
  have G := fun (i j : ℕ) (hi : i < 7) (hj : j < 7) => iform_pow_pow_seven hP hαp hi hj
  have g0 : iform α (w ^ 0 • α) = 2 := by rw [pow_zero, one_smul, hSL α hα]
  have g4 := iform_pow_seven_sub hP hαp (show 3 + 4 = 7 from rfl)
  have g5 := iform_pow_seven_sub hP hαp (show 2 + 5 = 7 from rfl)
  have g6 := iform_pow_seven_sub hP hαp (show 1 + 6 = 7 from rfl)
  have nb1 : ¬ (iform α (w ^ 1 • α) = -1 ∧ iform α (w ^ 2 • α) = -1 ∧
      iform α (w ^ 3 • α) = 1) := by
    rintro ⟨h1, h2, h3⟩
    have := iform_self_nonneg7 (w ^ 0 • α + w ^ 1 • α + w ^ 2 • α - w ^ 4 • α - w ^ 5 • α)
    simp (disch := decide) only [iform_add_left, iform_add_right, iform_sub_left, iform_sub_right,
      G, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, g0, g4, g5, g6, h1, h2, h3] at this
    norm_num at this
  have nb2 : ¬ (iform α (w ^ 1 • α) = -1 ∧ iform α (w ^ 2 • α) = 1 ∧
      iform α (w ^ 3 • α) = -1) := by
    rintro ⟨h1, h2, h3⟩
    have := iform_self_nonneg7 (w ^ 0 • α + w ^ 1 • α - w ^ 2 • α + w ^ 4 • α - w ^ 6 • α)
    simp (disch := decide) only [iform_add_left, iform_add_right, iform_sub_left, iform_sub_right,
      G, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, g0, g4, g5, g6, h1, h2, h3] at this
    norm_num at this
  have nb3 : ¬ (iform α (w ^ 1 • α) = 1 ∧ iform α (w ^ 2 • α) = -1 ∧
      iform α (w ^ 3 • α) = -1) := by
    rintro ⟨h1, h2, h3⟩
    have := iform_self_nonneg7 (w ^ 0 • α + w ^ 3 • α - w ^ 4 • α + w ^ 5 • α - w ^ 6 • α)
    simp (disch := decide) only [iform_add_left, iform_add_right, iform_sub_left, iform_sub_right,
      G, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, g0, g4, g5, g6, h1, h2, h3] at this
    norm_num at this
  omega

end Orbit

theorem exists_good_root_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ)
    (hP : OrbitZero 7 w) {α₀ : Fin τ.rank → ℤ} (hα₀ : α₀ ∈ kernelRoots χ)
    (hα₀p : ∀ v, w • v = v → iform α₀ v = 0) :
    ∃ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) ∧ iform γ (w ^ 1 • γ) = -1 := by
  have hwχ : w ∈ charStabilizer χ := kernelWeylGroup_le hw
  have hS : ∀ k : ℕ, w ^ k • α₀ ∈ kernelRoots χ := fun k =>
    smul_mem_kernelRoots (pow_mem hwχ k) hα₀
  have hp : ∀ k : ℕ, ∀ v, w • v = v → iform (w ^ k • α₀) v = 0 := perp_pow_smul hα₀p
  have G := fun (i j : ℕ) (hi : i < 7) (hj : j < 7) => iform_pow_pow_seven hP hα₀p hi hj
  have g4 := iform_pow_seven_sub hP hα₀p (show 3 + 4 = 7 from rfl)
  have g5 := iform_pow_seven_sub hP hα₀p (show 2 + 5 = 7 from rfl)
  have g6 := iform_pow_seven_sub hP hα₀p (show 1 + 6 = 7 from rfl)
  have hsh : ∀ k : ℕ, w ^ 1 • w ^ k • α₀ = w ^ (k + 1) • α₀ := fun k => by
    rw [← mul_smul, ← pow_add, add_comm]
  rcases orbit_cases_seven hSL hP hα₀.1 hα₀p with ⟨h1, -, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨α₀, hα₀, hα₀p, h1⟩
  ·
    have e13 : iform (w ^ 1 • α₀) (w ^ 3 • α₀) = -1 := by
      rw [G 1 3 (by norm_num) (by norm_num)]
      exact h2
    have r13 : IsRoot τ (w ^ 1 • α₀ + w ^ 3 • α₀) := by
      refine isRoot_add_of_iform_neg (hS 1).1 (hS 3).1 (fun e' => ?_) (by rw [e13]; norm_num)
      rw [e', iform_neg_fst, hSL _ (hS 3).1] at e13
      omega
    have e135 : iform (w ^ 1 • α₀ + w ^ 3 • α₀) (w ^ 5 • α₀) = -1 := by
      rw [iform_add_left, G 1 5 (by norm_num) (by norm_num), G 3 5 (by norm_num) (by norm_num),
        show (5 + 7 - 1) % 7 = 4 from rfl, show (5 + 7 - 3) % 7 = 2 from rfl, g4, h3, h2]
      norm_num
    have r135 : IsRoot τ (w ^ 1 • α₀ + w ^ 3 • α₀ + w ^ 5 • α₀) := by
      refine isRoot_add_of_iform_neg r13 (hS 5).1 (fun e' => ?_) (by rw [e135]; norm_num)
      rw [e', iform_neg_fst, hSL _ (hS 5).1] at e135
      omega
    refine ⟨-(w ^ 1 • α₀ + w ^ 3 • α₀ + w ^ 5 • α₀), ⟨IsRoot.neg r135, ?_⟩, fun v hv => ?_, ?_⟩
    · rw [ofAdd_neg, map_inv, ofAdd_add, ofAdd_add, map_mul, map_mul, (hS 1).2, (hS 3).2,
        (hS 5).2]
      simp
    · rw [iform_neg_fst, iform_add_left, iform_add_left, hp 1 v hv, hp 3 v hv, hp 5 v hv]
      simp
    · rw [smul_neg, smul_add, smul_add, iform_neg_fst, iform_neg_snd, neg_neg]
      simp (disch := decide) only [hsh, Nat.reduceAdd, iform_add_left, iform_add_right, G,
        Nat.reduceSub, Nat.reduceMod, g4, g5, g6, h1, h2, h3]
      norm_num
  ·
    have e14 : iform (w ^ 1 • α₀) (w ^ 4 • α₀) = -1 := by
      rw [G 1 4 (by norm_num) (by norm_num)]
      exact h3
    have r14 : IsRoot τ (w ^ 1 • α₀ + w ^ 4 • α₀) := by
      refine isRoot_add_of_iform_neg (hS 1).1 (hS 4).1 (fun e' => ?_) (by rw [e14]; norm_num)
      rw [e', iform_neg_fst, hSL _ (hS 4).1] at e14
      omega
    refine ⟨-(w ^ 1 • α₀ + w ^ 4 • α₀), ⟨IsRoot.neg r14, ?_⟩, fun v hv => ?_, ?_⟩
    · rw [ofAdd_neg, map_inv, ofAdd_add, map_mul, (hS 1).2, (hS 4).2]
      simp
    · rw [iform_neg_fst, iform_add_left, hp 1 v hv, hp 4 v hv]
      simp
    · rw [smul_neg, smul_add, iform_neg_fst, iform_neg_snd, neg_neg]
      simp (disch := decide) only [hsh, Nat.reduceAdd, iform_add_left, iform_add_right, G,
        Nat.reduceSub, Nat.reduceMod, g4, g5, h1, h2, h3]
      norm_num

theorem isAChain_orbit_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {w : WeylGroup τ}
    (hP : OrbitZero 7 w) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγp : ∀ v, w • v = v → iform γ v = 0) (h1 : iform γ (w ^ 1 • γ) = -1) :
    IsAChain (fun i : Fin 6 => w ^ (i : ℕ) • γ) := by
  have h23 : iform γ (w ^ 2 • γ) = 0 ∧ iform γ (w ^ 3 • γ) = 0 := by
    rcases orbit_cases_seven hSL hP hγ hγp with ⟨-, h2, h3⟩ | ⟨h1', -, -⟩ | ⟨h1', -, -⟩
    · exact ⟨h2, h3⟩
    · rw [h1] at h1'
      norm_num at h1'
    · rw [h1] at h1'
      norm_num at h1'
  have g4 := iform_pow_seven_sub hP hγp (show 3 + 4 = 7 from rfl)
  have g5 := iform_pow_seven_sub hP hγp (show 2 + 5 = 7 from rfl)
  refine ⟨fun i => IsRoot.smul hγ _, fun i j hij => ?_, fun i j hij => ?_⟩
  · have hi := i.isLt
    have hj := j.isLt
    change iform (w ^ (i : ℕ) • γ) (w ^ (j : ℕ) • γ) = -1
    rw [iform_pow_pow_seven hP hγp (by omega) (by omega),
      show ((j : ℕ) + 7 - i) % 7 = 1 by omega]
    exact h1
  · have hi := i.isLt
    have hj := j.isLt
    change iform (w ^ (i : ℕ) • γ) (w ^ (j : ℕ) • γ) = 0
    rw [iform_pow_pow_seven hP hγp (by omega) (by omega)]
    obtain h | h | h | h : ((j : ℕ) + 7 - i) % 7 = 2 ∨ ((j : ℕ) + 7 - i) % 7 = 3 ∨
        ((j : ℕ) + 7 - i) % 7 = 4 ∨ ((j : ℕ) + 7 - i) % 7 = 5 := by omega
    · rw [h]
      exact h23.1
    · rw [h]
      exact h23.2
    · rw [h, g4]
      exact h23.2
    · rw [h, g5]
      exact h23.1

theorem exists_orbitChain_seven (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (w : WeylGroup τ) (hw : w ∈ kernelWeylGroup χ)
    (hP : OrbitZero 7 w) (hw1 : w ≠ 1) :
    ∃ γ ∈ kernelRoots χ, (∀ v, w • v = v → iform γ v = 0) ∧
      IsAChain (fun i : Fin 6 => w ^ (i : ℕ) • γ) := by
  obtain ⟨α₀, hα₀, hα₀p⟩ := exists_kernelRoot_perp hw hw1
  obtain ⟨γ, hγ, hγp, h1⟩ := exists_good_root_seven hSL hw hP hα₀ hα₀p
  exact ⟨γ, hγ, hγp, isAChain_orbit_seven hSL hP hγ.1 hγp h1⟩

theorem exists_a6Blocks (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {w : WeylGroup τ} (hw : w ∈ kernelWeylGroup χ)
    (h7 : w ^ 7 = 1) :
    ∃ B : List (Fin 6 → Fin τ.rank → ℤ),
      (∀ β ∈ B, IsAChain β ∧ aChainRoots β ⊆ kernelRoots χ) ∧
      B.Pairwise ChainsStrOrth ∧ w = (B.map chainRefl).prod :=
  exists_chainBlocks (n := 5) hSL (fun w hw hP hw1 => exists_orbitChain_seven hSL w hw hP hw1)
    hw (orbitZero_of_pow h7)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
