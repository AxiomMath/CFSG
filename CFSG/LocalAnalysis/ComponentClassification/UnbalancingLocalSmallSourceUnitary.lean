module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

section Hyperbolic

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (r ε : ℕ)

@[expose] def skewHermitian : AddSubgroup (Matrix (Fin r) (Fin r) K) where
  carrier := {C | C + (C.map h.bar)ᵀ = 0}
  add_mem' {C D} hC hD := by
    change C + (C.map h.bar)ᵀ = 0 at hC
    change D + (D.map h.bar)ᵀ = 0 at hD
    change C + D + ((C + D).map h.bar)ᵀ = 0
    rw [Matrix.map_add _ (map_add h.bar), transpose_add]
    calc C + D + ((C.map h.bar)ᵀ + (D.map h.bar)ᵀ) =
        (C + (C.map h.bar)ᵀ) + (D + (D.map h.bar)ᵀ) := by abel
      _ = 0 := by rw [hC, hD, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin r) (Fin r) K) + ((0 : Matrix (Fin r) (Fin r) K).map h.bar)ᵀ = 0
    rw [Matrix.map_zero _ (map_zero h.bar), transpose_zero, add_zero]
  neg_mem' {C} hC := by
    change C + (C.map h.bar)ᵀ = 0 at hC
    change -C + ((-C).map h.bar)ᵀ = 0
    rw [Matrix.map_neg _ (map_neg h.bar), transpose_neg, ← neg_add, hC, neg_zero]

variable {h r} in
theorem uMat_gram {C : Matrix (Fin r) (Fin r) K} (hC : C ∈ skewHermitian h r) :
    ((blk3 (1 : Matrix (Fin r) (Fin r) K) (0 : Matrix (Fin r) (Fin ε) K) C 1 0 1).map
        h.bar)ᵀ * hypGram r ε K * blk3 1 0 C 1 0 1 = hypGram r ε K := by
  have h1 : ∀ {m : ℕ}, ((1 : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * 1 = 1 := by
    intro m
    rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, mul_one]
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨h1, h1, ?_, ?_⟩
  · simp [Matrix.map_zero _ (map_zero h.bar)]
  · rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one, Matrix.mul_one,
      Matrix.one_mul, Matrix.map_zero _ (map_zero h.bar), transpose_zero, Matrix.zero_mul,
      add_zero, add_comm]
    exact hC

@[expose] def uElt (C : skewHermitian h r) : hypSU h r ε :=
  mkHypSU h (blk3 1 0 (C : Matrix (Fin r) (Fin r) K) 1 0 1) (uMat_gram ε C.2) (by
    rw [det_blk3]
    simp)

theorem coe_uElt (C : skewHermitian h r) :
    (((uElt h r ε C : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = blk3 1 0 (C : Matrix (Fin r) (Fin r) K) 1 0 1 :=
  rfl

@[expose] def uHom : Multiplicative (skewHermitian h r) →* hypSU h r ε where
  toFun C := uElt h r ε C.toAdd
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_uElt]
    ext a b
    rcases a with i | k | i <;> rcases b with j | l | j <;> simp [one_apply]
  map_mul' C D := by
    apply Subtype.ext
    apply Units.ext
    change blk3 1 0 ((C.toAdd + D.toAdd : skewHermitian h r) : Matrix (Fin r) (Fin r) K) 1 0 1 =
      blk3 1 0 (C.toAdd : Matrix (Fin r) (Fin r) K) 1 0 1 *
        blk3 1 0 (D.toAdd : Matrix (Fin r) (Fin r) K) 1 0 1
    rw [blk3_mul]
    simp [add_comm]

variable {h r ε} in
theorem eq_zero_of_uElt_mem_hypScalars (hr : 1 ≤ r) {C : skewHermitian h r}
    (hC : uElt h r ε C ∈ hypScalars h r ε) : C = 0 := by
  obtain ⟨c, -, -, hc⟩ := hC
  have hmat := congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε)
    (HypIndex r ε) K)) hc
  simp only [coe_uElt, Matrix.GeneralLinearGroup.coe_scalar] at hmat
  have hc1 : (c : K) = 1 := by
    have := congrFun (congrFun hmat (.inl ⟨0, hr⟩)) (.inl ⟨0, hr⟩)
    simpa using this.symm
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun hmat (.inl i)) (.inr (.inr j))
  simpa [hc1] using this

variable {h r} in
theorem exists_elementary_hypPSU [CharP K 2] (hr : 1 ≤ r) :
    ∃ E : Subgroup (hypPSU h r ε), IsElementaryAbelian 2 E ∧
      Nat.card E = (p ^ f) ^ (r * r) := by
  set φ := (hypProj h r ε).comp (uHom h r ε) with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro C hC
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_hypProj] at hC
    rw [Subgroup.mem_bot, ← ofAdd_toAdd C, eq_zero_of_uElt_mem_hypScalars hr hC, ofAdd_zero]
  have hE : IsElementaryAbelian 2 φ.range := by
    refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      change φ a * φ b = φ b * φ a
      rw [← map_mul, ← map_mul, mul_comm a b]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, a, rfl⟩ := x
      apply Subtype.ext
      change φ a ^ 2 = 1
      have ha : a ^ 2 = 1 := by
        rw [pow_two, ← ofAdd_toAdd a, ← ofAdd_add]
        have h0 : a.toAdd + a.toAdd = 0 := by
          apply Subtype.ext
          ext i j
          change (a.toAdd : Matrix (Fin r) (Fin r) K) i j + (a.toAdd : Matrix (Fin r) (Fin r) K) i j
            = 0
          exact CharTwo.add_self_eq_zero _
        rw [h0, ofAdd_zero]
      rw [← map_pow, ha, map_one]
  refine ⟨φ.range, hE, ?_⟩
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd]
  have hcount := ClassicalGroups.UnitaryFlag.card_add_conjTranspose_eq h (r := r)
    (M := 0) (fun i j => by simp)
  exact hcount

variable {h r ε} in
theorem pow_dvd_card_hypPSU (hr : 1 ≤ r) (hε : ε ≤ 1) :
    (p ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) ∣ Nat.card (hypPSU h r ε) := by
  obtain ⟨hU, -, -, ⟨e, -⟩, -⟩ := unitary_order_and_Sylow h hr hε
  rw [← hU, Nat.card_congr e.toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Hyperbolic

theorem card_psu_three_four {K : Type} [Field K] (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ 2) K)) = 62400 := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num) hK
    (by norm_num)]
  decide

theorem card_psu_four_two {K : Type} [Field K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (StatedProj (StatedSU 4 (2 ^ 1) K)) = 25920 := by
  rw [Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num) hK
    (by norm_num)]
  decide

theorem small_standard_source_even_unitary_model_exclusion_stated {X : Type} [Group X]
    {n g : ℕ} (hX : StatedClassicalModel X .PSU n 2 g) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧ ¬ StatedClassicalModel X .PSL 3 2 2 := by
  obtain ⟨⟨-, hg, hn3, hn32⟩, K, _, _, hK, ⟨φ⟩⟩ := hX
  have h : UnitaryFieldData 2 g K := ⟨Nat.prime_two, hg, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := h.charP
  have hXcard : ∀ {K' : Type} [Field K'] (_ : Nat.card K' = (2 ^ g) ^ 2)
      (_ : X ≃* StatedProj (StatedSU n (2 ^ g) K')), Nat.card X =
        Nat.card (StatedProj (StatedSU n (2 ^ g) K')) := fun _ e => Nat.card_congr e.toEquiv
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  let θ : X ≃* hypPSU h r ε := φ.trans (hypPSUEquivStatedProj h hR (by omega)).symm
  have hdvd : 2 ^ (g * ((2 * r + ε) * (2 * r + ε - 1) / 2)) ∣ Nat.card X := by
    rw [pow_mul, Nat.card_congr θ.toEquiv]
    exact pow_dvd_card_hypPSU hr hε
  have hn : 3 ≤ (2 * r + ε) * (2 * r + ε - 1) / 2 := by
    have : 6 ≤ (2 * r + ε) * (2 * r + ε - 1) :=
      le_trans (by norm_num) (Nat.mul_le_mul hn3 (by omega : 2 ≤ 2 * r + ε - 1))
    omega
  refine ⟨fun p f hp2 hY => ?_, ⟨fun e => ?_⟩, fun hZ => ?_⟩
  ·
    obtain ⟨⟨hp, hf, -⟩, K₀, _, _, hK₀, ⟨ψ⟩⟩ := hY
    have hq : Odd (Nat.card K₀) := by
      rw [hK₀]
      exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨E, hE, hEcard⟩ := exists_elementary_hypPSU (h := h) (r := r) ε hr
    have : IsElementaryAbelian 2 (E.map θ.symm.toMonoidHom) := IsElementaryAbelian.map _
    have h4 := card_le_four_of_odd_psl_two hq ψ (E.map θ.symm.toMonoidHom)
    rw [Subgroup.card_map_of_injective θ.symm.injective, hEcard] at h4
    have hq2 : 2 ≤ 2 ^ g := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    rcases Nat.lt_or_ge 1 r with hr2 | hr1
    ·
      have : 16 ≤ (2 ^ g) ^ (r * r) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ (2 ^ g) ^ 4 := Nat.pow_le_pow_left hq2 4
          _ ≤ (2 ^ g) ^ (r * r) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      omega
    ·
      have hr1' : r = 1 := by omega
      subst hr1'
      have hε1 : ε = 1 := by omega
      subst hε1
      have hg2 : g = 2 := by
        have hle : 2 ^ g ≤ 2 ^ 2 := by simpa using h4
        have hle' : g ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
        have hne : g ≠ 1 := fun h1 => hn32 (by rw [h1, pow_one])
        omega
      subst hg2
      have hX62 : Nat.card X = 62400 := (hXcard hK φ).trans (card_psu_three_four hK)
      have hXq : Nat.card X * 2 = Nat.card K₀ * (Nat.card K₀ ^ 2 - 1) := by
        rw [Nat.card_congr ψ.toEquiv]
        exact two_mul_card_psl_two_of_odd K₀ hq
      exact cubeSub_ne_of_between (a := 49) (N := 124800) (by norm_num) (by norm_num)
        (by norm_num) (Nat.card K₀) (by rw [← hXq, hX62])
  ·
    have hX7 : Nat.card X = 2520 := (Nat.card_congr e.toEquiv).trans card_alternating_seven
    rw [hX7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num] at hdvd
    have hle := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd
    have hg1 : g = 1 := by nlinarith
    have hn' : (2 * r + ε) * (2 * r + ε - 1) / 2 = 3 := by nlinarith
    subst hg1
    have h3 : 2 * r + ε = 3 := by
      rcases Nat.lt_or_ge (2 * r + ε) 4 with h' | h'
      · omega
      · have : 12 ≤ (2 * r + ε) * (2 * r + ε - 1) :=
          le_trans (by norm_num) (Nat.mul_le_mul h' (by omega : 3 ≤ 2 * r + ε - 1))
        omega
    exact hn32 (by rw [h3, pow_one])
  ·
    obtain ⟨-, K₃, _, _, hK₃, ⟨χ⟩⟩ := hZ
    have hX3 : Nat.card X = 20160 :=
      (Nat.card_congr χ.toEquiv).trans (card_psl_three_four K₃ (by rw [hK₃]; norm_num))
    have hdvd' := hdvd
    rw [hX3, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at hdvd'
    have hle := two_pow_dvd_of_dvd_mul_odd (by decide) hdvd'
    have hm : 2 * r + ε = 3 ∨ 2 * r + ε = 4 := by
      rcases Nat.lt_or_ge (2 * r + ε) 5 with h' | h'
      · omega
      · have : 20 ≤ (2 * r + ε) * (2 * r + ε - 1) :=
          le_trans (by norm_num) (Nat.mul_le_mul h' (by omega : 4 ≤ 2 * r + ε - 1))
        have : 10 ≤ (2 * r + ε) * (2 * r + ε - 1) / 2 := by omega
        nlinarith
    rcases hm with hm | hm
    ·
      have hr1 : r = 1 := by omega
      have hε1 : ε = 1 := by omega
      subst hr1 hε1
      have hg2 : g = 2 := by
        have : g * 3 ≤ 6 := by simpa using hle
        have hne : g ≠ 1 := fun h1 => hn32 (by rw [h1, pow_one])
        omega
      subst hg2
      have := (hXcard hK φ).trans (card_psu_three_four hK)
      omega
    ·
      have hr2 : r = 2 := by omega
      have hε0 : ε = 0 := by omega
      subst hr2 hε0
      have hg1 : g = 1 := by
        have : g * 6 ≤ 6 := by simpa using hle
        omega
      subst hg1
      have := (hXcard hK φ).trans (card_psu_four_two hK)
      omega

theorem small_standard_source_even_unitary_model_exclusion {X : Type} [Group X] {n g : ℕ}
    (hX : Assembly.ComponentType.ClassicalModel X .PSU n 2 g) :
    (∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 →
        ¬ Assembly.ComponentType.ClassicalModel X .PSL 2 p f) ∧
      IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      ¬ Assembly.ComponentType.ClassicalModel X .PSL 3 2 2 := by
  obtain ⟨h1, h2, h3⟩ := small_standard_source_even_unitary_model_exclusion_stated
    (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSU n 2 g hX)
  exact ⟨fun p f _ hp2 hY => h1 p f hp2
      (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 2 p f hY), h2,
    fun hZ => h3 (ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel .PSL 3 2 2 hZ)⟩

end CFSG.ComponentClassification.UnbalancingLocal
