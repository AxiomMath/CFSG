module

public import CFSG.LieType.Sp6Spin.Setup

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (S : SpinSetting K V)

omit [CharP K 2] in
theorem rootWt_positiveLong (i : Fin 3) :
    rootWt K (.positiveLong i) = Pi.single i (2 : ZMod (Nat.card Kˣ)) := by
  funext b
  simp only [rootWt, castW, stdVec_apply_positiveLong, Pi.single_apply]
  by_cases hb : b = i <;> simp [hb]

omit [CharP K 2] in
theorem rootWt_negativeLong (i : Fin 3) :
    rootWt K (.negativeLong i) = Pi.single i (-2 : ZMod (Nat.card Kˣ)) := by
  funext b
  simp only [rootWt, castW, stdVec_apply_negativeLong, Pi.single_apply]
  by_cases hb : b = i <;> simp [hb]

omit [CharP K 2] in
theorem rootWt_difference_apply {i j : Fin 3} (hij : i ≠ j) (b : Fin 3) :
    rootWt K (.difference i j hij) b =
      if b = i then (1 : ZMod (Nat.card Kˣ)) else if b = j then -1 else 0 := by
  simp only [rootWt, castW, stdVec_apply_difference hij]
  by_cases hbi : b = i
  · simp [hbi]
  · by_cases hbj : b = j <;> simp [hbi, hbj]

omit [CharP K 2] in
theorem rootWt_positiveSum_apply {i j : Fin 3} (hij : i < j) (b : Fin 3) :
    rootWt K (.positiveSum i j hij) b =
      if b = i then (1 : ZMod (Nat.card Kˣ)) else if b = j then 1 else 0 := by
  simp only [rootWt, castW, stdVec_apply_positiveSum hij]
  by_cases hbi : b = i
  · simp [hbi]
  · by_cases hbj : b = j <;> simp [hbi, hbj]

omit [CharP K 2] in
theorem rootWt_negativeSum_apply {i j : Fin 3} (hij : i < j) (b : Fin 3) :
    rootWt K (.negativeSum i j hij) b =
      if b = i then (-1 : ZMod (Nat.card Kˣ)) else if b = j then -1 else 0 := by
  simp only [rootWt, castW, stdVec_apply_negativeSum hij]
  by_cases hbi : b = i
  · simp [hbi]
  · by_cases hbj : b = j <;> simp [hbi, hbj]

omit [Finite K] [CharP K 2] in
private theorem natCast_ne_zero {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < Nat.card Kˣ) :
    (k : ZMod (Nat.card Kˣ)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hk0' : k = 0 := Nat.eq_zero_of_dvd_of_lt h hkN
  omega

private theorem natCast_mul_two_ne_zero {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < Nat.card Kˣ) :
    (k : ZMod (Nat.card Kˣ)) * 2 ≠ 0 := by
  intro h
  have hcop : Nat.Coprime 2 (Nat.card Kˣ) := odd_natCard_units.coprime_two_left
  have h1 : (2 : ZMod (Nat.card Kˣ)) * (2 : ZMod (Nat.card Kˣ))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 hcop
  have hkzero : (k : ZMod (Nat.card Kˣ)) = 0 := by
    have h' : (2 : ZMod (Nat.card Kˣ))⁻¹ * ((k : ZMod (Nat.card Kˣ)) * 2) = 0 := by
      simpa using congrArg (fun z => (2 : ZMod (Nat.card Kˣ))⁻¹ * z) h
    calc (k : ZMod (Nat.card Kˣ))
        = (2 : ZMod (Nat.card Kˣ))⁻¹ * ((k : ZMod (Nat.card Kˣ)) * 2) := by
          rw [mul_comm (k : ZMod (Nat.card Kˣ)) 2, ← mul_assoc,
            mul_comm (2 : ZMod (Nat.card Kˣ))⁻¹ 2, h1, one_mul]
      _ = 0 := h'
  exact natCast_ne_zero hk0 hkN hkzero

private theorem smul_rootWt_ne_zero (r : RootSubgroupIndex 3) {k : ℕ}
    (hk0 : 1 ≤ k) (hkN : k < Nat.card Kˣ) :
    ((k : ZMod (Nat.card Kˣ)) • rootWt K r) ≠ 0 := by
  have hk : (k : ZMod (Nat.card Kˣ)) ≠ 0 := natCast_ne_zero hk0 hkN
  have h2k : (k : ZMod (Nat.card Kˣ)) * 2 ≠ 0 := natCast_mul_two_ne_zero hk0 hkN
  intro h
  cases r with
  | positiveLong i =>
      have hi := congrFun h i
      rw [Pi.smul_apply, rootWt_positiveLong, Pi.single_eq_same, Pi.zero_apply,
        smul_eq_mul] at hi
      exact h2k hi
  | negativeLong i =>
      have hi := congrFun h i
      rw [Pi.smul_apply, rootWt_negativeLong, Pi.single_eq_same, Pi.zero_apply,
        smul_eq_mul] at hi
      have h2k' : (k : ZMod (Nat.card Kˣ)) * 2 = 0 := by
        simpa using congrArg Neg.neg hi
      exact h2k h2k'
  | difference i j hij =>
      have hi := congrFun h i
      rw [Pi.smul_apply, rootWt_difference_apply hij, if_pos rfl, Pi.zero_apply,
        smul_eq_mul, mul_one] at hi
      exact hk hi
  | positiveSum i j hij =>
      have hi := congrFun h i
      rw [Pi.smul_apply, rootWt_positiveSum_apply hij, if_pos rfl, Pi.zero_apply,
        smul_eq_mul, mul_one] at hi
      exact hk hi
  | negativeSum i j hij =>
      have hi := congrFun h i
      rw [Pi.smul_apply, rootWt_negativeSum_apply hij, if_pos rfl, Pi.zero_apply,
        smul_eq_mul] at hi
      have hk' : (k : ZMod (Nat.card Kˣ)) = 0 := by
        simpa using congrArg Neg.neg hi
      exact hk hk'

omit [CharP K 2] in
private theorem smul_rootWt_two_nonzero {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < Nat.card Kˣ) :
    ∃ i j : Fin 3, i ≠ j ∧ ((k : ZMod (Nat.card Kˣ)) • rootWt K r) i ≠ 0 ∧
      ((k : ZMod (Nat.card Kˣ)) • rootWt K r) j ≠ 0 := by
  have hk : (k : ZMod (Nat.card Kˣ)) ≠ 0 := natCast_ne_zero hk0 hkN
  cases r with
  | positiveLong i => simp [IsShortIndex] at hr
  | negativeLong i => simp [IsShortIndex] at hr
  | difference i j hij =>
      refine ⟨i, j, hij, ?_, ?_⟩
      · rw [Pi.smul_apply, rootWt_difference_apply hij, if_pos rfl, smul_eq_mul, mul_one]
        exact hk
      · rw [Pi.smul_apply, rootWt_difference_apply hij, if_neg (Ne.symm hij), if_pos rfl,
          smul_eq_mul]
        simpa using hk
  | positiveSum i j hij =>
      refine ⟨i, j, hij.ne, ?_, ?_⟩
      · rw [Pi.smul_apply, rootWt_positiveSum_apply hij, if_pos rfl, smul_eq_mul, mul_one]
        exact hk
      · rw [Pi.smul_apply, rootWt_positiveSum_apply hij, if_neg hij.ne', if_pos rfl,
          smul_eq_mul, mul_one]
        exact hk
  | negativeSum i j hij =>
      refine ⟨i, j, hij.ne, ?_, ?_⟩
      · rw [Pi.smul_apply, rootWt_negativeSum_apply hij, if_pos rfl, smul_eq_mul]
        simpa using hk
      · rw [Pi.smul_apply, rootWt_negativeSum_apply hij, if_neg hij.ne', if_pos rfl,
          smul_eq_mul]
        simpa using hk

omit [CharP K 2] in
private theorem smul_rootWt_ne_single {r : RootSubgroupIndex 3} (hr : IsShortIndex r)
    {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < Nat.card Kˣ) {i : Fin 3}
    {y : ZMod (Nat.card Kˣ)} :
    ((k : ZMod (Nat.card Kˣ)) • rootWt K r) ≠ Pi.single i y := by
  obtain ⟨i', j', hij, hi', hj'⟩ := smul_rootWt_two_nonzero hr hk0 hkN
  intro h
  by_cases hii : i' = i
  · have hji : j' ≠ i := fun h' => hij (hii.trans h'.symm)
    have hc := congrFun h j'
    rw [Pi.single_eq_of_ne hji] at hc
    exact hj' hc
  · have hc := congrFun h i'
    rw [Pi.single_eq_of_ne hii] at hc
    exact hi' hc

private theorem exists_mem_ne_zero_of_mult_ne_zero
    {a : Fin 3 → ZMod (Nat.card Kˣ)} (ha : S.mult a ≠ 0) :
    ∃ v ∈ S.X a, v ≠ 0 :=
  (Submodule.ne_bot_iff (S.X a)).mp (fun hbot => ha (S.X_eq_bot_iff.mp hbot))

theorem mult_zero_ne_eight : S.mult 0 ≠ 8 := by
  intro h8
  have hzero : ∀ a : Fin 3 → ZMod (Nat.card Kˣ), a ≠ 0 → S.mult a = 0 := by
    intro a ha
    have hsum := S.sum_mult
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin 3 → ZMod (Nat.card Kˣ))),
      h8] at hsum
    have htail : ∑ b ∈ Finset.univ.erase (0 : Fin 3 → ZMod (Nat.card Kˣ)), S.mult b = 0 := by
      omega
    have hmem : a ∈ Finset.univ.erase (0 : Fin 3 → ZMod (Nat.card Kˣ)) := by
      simp [ha]
    have hle := Finset.single_le_sum (f := S.mult) (fun b _ => Nat.zero_le (S.mult b)) hmem
    rw [htail] at hle
    omega
  have htop : S.X 0 = ⊤ := by
    have : FiniteDimensional K V := S.finiteDimensional
    apply Submodule.eq_top_of_finrank_eq
    rw [S.finrank_eq]
    exact h8
  have hmem0 : ∀ v : V, v ∈ S.X 0 := by
    intro v
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨v, hv0⟩ : ∃ v : V, v ≠ 0 := by
    have : FiniteDimensional K V := S.finiteDimensional
    exact Module.finrank_pos_iff_exists_ne_zero.mp (by rw [S.finrank_eq]; norm_num)
  have hshort : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K, S.ψ (elt r c) v = v := by
    intro r hr c
    refine S.fix_of_forall r (a := 0) (hmem0 v) ?_ c
    intro k hk0 hkN
    rw [zero_add]
    exact hzero _ (smul_rootWt_ne_zero r hk0 hkN)
  have hlong : ∀ c : K, S.ψ (elt (.positiveLong 2) c) v = v := by
    intro c
    refine S.fix_of_forall (.positiveLong 2) (a := 0) (hmem0 v) ?_ c
    intro k hk0 hkN
    rw [zero_add]
    exact hzero _ (smul_rootWt_ne_zero _ hk0 hkN)
  exact hv0 (S.eq_zero_of_fixed hshort hlong)

private theorem natural_pattern_lines (x : ZMod (Nat.card Kˣ)) (hx : x ≠ 0)
    (hpat : ∀ a : Fin 3 → ZMod (Nat.card Kˣ), a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0) :
    ∃ y₁ y₂ : V, y₁ ∈ S.X (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)) ∧ y₁ ≠ 0 ∧
      y₂ ∈ S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) ∧ polar S.Q y₁ y₂ = 1 ∧
      (∀ w ∈ S.X (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)),
        w = polar S.Q w y₂ • y₁) ∧
      (∀ w ∈ S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)),
        w = polar S.Q y₁ w • y₂) := by
  have : FiniteDimensional K V := S.finiteDimensional
  have hY₁ : S.mult (Pi.single 2 x) = 1 := by
    have hne : (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)) ≠ 0 := by
      intro h
      exact hx (by simpa using congrFun h 2)
    rw [hpat (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)) hne]
    exact if_pos ⟨2, Or.inl rfl⟩
  have hY₂ : S.mult (Pi.single 2 (-x)) = 1 := by
    have hne : (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) ≠ 0 := by
      intro h
      have h' : -x = 0 := by simpa using congrFun h 2
      exact hx (neg_eq_zero.mp h')
    rw [hpat (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) hne]
    exact if_pos ⟨2, Or.inr rfl⟩
  obtain ⟨y₁, hy₁mem, hy₁0⟩ :=
    exists_mem_ne_zero_of_mult_ne_zero (S := S)
      (a := (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ))) (by rw [hY₁]; norm_num)
  obtain ⟨y₂, hy₂mem', hy₁₂⟩ := S.exists_polar_eq_one hy₁mem hy₁0
  have hy₂mem : y₂ ∈ S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) := by
    rw [Pi.single_neg]
    exact hy₂mem'
  have hy₂0 : y₂ ≠ 0 := by
    intro h
    rw [h] at hy₁₂
    rw [← QuadraticMap.polarBilin_apply_apply, map_zero] at hy₁₂
    exact one_ne_zero hy₁₂.symm
  refine ⟨y₁, y₂, hy₁mem, hy₁0, hy₂mem, hy₁₂, ?_, ?_⟩
  · intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := K) (V := S.X (Pi.single 2 x))
      ⟨y₁, hy₁mem⟩ (by simpa using hy₁0)).mp hY₁ ⟨w, hw⟩
    have hcw : c • y₁ = w := by
      simpa using congrArg Subtype.val hc
    rw [← hcw]
    have hpol : polar S.Q (c • y₁) y₂ = c := by
      rw [← QuadraticMap.polarBilin_apply_apply, map_smul, LinearMap.smul_apply,
        QuadraticMap.polarBilin_apply_apply, hy₁₂]
      simp
    rw [hpol]
  · intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := K) (V := S.X (Pi.single 2 (-x)))
      ⟨y₂, hy₂mem⟩ (by simpa using hy₂0)).mp hY₂ ⟨w, hw⟩
    have hcw : c • y₂ = w := by
      simpa using congrArg Subtype.val hc
    rw [← hcw]
    have hpol : polar S.Q y₁ (c • y₂) = c := by
      rw [← QuadraticMap.polarBilin_apply_apply, map_smul,
        QuadraticMap.polarBilin_apply_apply, hy₁₂]
      simp
    rw [hpol]

private theorem natural_pattern_operators {x : ZMod (Nat.card Kˣ)}
    {k₁ k₂ : ℕ} (hk₁1 : 1 ≤ k₁) (hk₂1 : 1 ≤ k₂)
    (hsum : k₁ + k₂ = Nat.card Kˣ)
    (hW₁ : (k₁ : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2) =
      (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)))
    (hW₂ : (k₂ : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2) =
      (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)))
    {y₁ y₂ : V} (hy₁mem : y₁ ∈ S.X (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)))
    (hy₂mem : y₂ ∈ S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)))
    (hline₁ : ∀ w ∈ S.X (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)),
      w = polar S.Q w y₂ • y₁)
    (hline₂ : ∀ w ∈ S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)),
      w = polar S.Q y₁ w • y₂) :
    ∃ p₁ p₂ : V, p₁ ∈ S.X 0 ∧ p₂ ∈ S.X 0 ∧
      (∀ v ∈ S.X 0, S.A (.positiveLong 2) k₁ v = polar S.Q v p₁ • y₁) ∧
      (∀ v ∈ S.X 0, S.A (.positiveLong 2) k₂ v = polar S.Q v p₂ • y₂) ∧
      (∀ v ∈ S.X 0, polar S.Q v p₂ • p₁ = polar S.Q v p₁ • p₂) := by
  let p₁ : V := S.A (.positiveLong 2) k₁ y₂
  let p₂ : V := S.A (.positiveLong 2) k₂ y₁
  have hp₁mem : p₁ ∈ S.X 0 := by
    have h := S.A_mem (r := .positiveLong 2)
      (a := (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ))) hy₂mem k₁
    rw [hW₁, ← Pi.single_add, neg_add_cancel, Pi.single_zero] at h
    exact h
  have hp₂mem : p₂ ∈ S.X 0 := by
    have h := S.A_mem (r := .positiveLong 2)
      (a := (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ))) hy₁mem k₂
    rw [hW₂, ← Pi.single_add, add_neg_cancel, Pi.single_zero] at h
    exact h
  have hA₁ : ∀ v ∈ S.X 0, S.A (.positiveLong 2) k₁ v = polar S.Q v p₁ • y₁ := by
    intro v hv
    have hmem : S.A (.positiveLong 2) k₁ v ∈
        S.X (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)) := by
      have h := S.A_mem (r := .positiveLong 2)
        (a := (0 : Fin 3 → ZMod (Nat.card Kˣ))) hv k₁
      rw [zero_add, hW₁] at h
      exact h
    calc S.A (.positiveLong 2) k₁ v = polar S.Q (S.A (.positiveLong 2) k₁ v) y₂ • y₁ :=
          hline₁ _ hmem
      _ = polar S.Q v p₁ • y₁ := by rw [S.polar_A (.positiveLong 2) v y₂ k₁]
  have hA₂ : ∀ v ∈ S.X 0, S.A (.positiveLong 2) k₂ v = polar S.Q v p₂ • y₂ := by
    intro v hv
    have hmem : S.A (.positiveLong 2) k₂ v ∈
        S.X (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) := by
      have h := S.A_mem (r := .positiveLong 2)
        (a := (0 : Fin 3 → ZMod (Nat.card Kˣ))) hv k₂
      rw [zero_add, hW₂] at h
      exact h
    calc S.A (.positiveLong 2) k₂ v = polar S.Q y₁ (S.A (.positiveLong 2) k₂ v) • y₂ :=
          hline₂ _ hmem
      _ = polar S.Q v p₂ • y₂ := by
          rw [QuadraticMap.polar_comm, S.polar_A (.positiveLong 2) v y₁ k₂]
  have hcomm : ∀ v ∈ S.X 0, polar S.Q v p₂ • p₁ = polar S.Q v p₁ • p₂ := by
    intro v hv
    have hmul : S.A (.positiveLong 2) k₁ * S.A (.positiveLong 2) k₂ =
        S.A (.positiveLong 2) k₂ * S.A (.positiveLong 2) k₁ := by
      have h1 := S.A_mul_card_sub (.positiveLong 2) (i := k₁) (by omega)
      have h2 := S.A_mul_card_sub (.positiveLong 2) (i := k₂) (by omega)
      rw [show Nat.card Kˣ - k₁ = k₂ from by omega] at h1
      rw [show Nat.card Kˣ - k₂ = k₁ from by omega] at h2
      rw [h1, h2]
    have h := congrArg (fun f : Module.End K V => f v) hmul
    simp only [Module.End.mul_apply] at h
    rw [hA₂ v hv, hA₁ v hv, map_smul, map_smul] at h
    exact h
  exact ⟨p₁, p₂, hp₁mem, hp₂mem, hA₁, hA₂, hcomm⟩

private theorem exists_orthogonal_vector {p₁ p₂ : V}
    (hcomm : ∀ v ∈ S.X 0, polar S.Q v p₂ • p₁ = polar S.Q v p₁ • p₂)
    (h0 : S.mult 0 = 2) :
    ∃ v ∈ S.X 0, v ≠ 0 ∧ polar S.Q v p₁ = 0 ∧ polar S.Q v p₂ = 0 := by
  have : FiniteDimensional K V := S.finiteDimensional
  let φ : S.X 0 →ₗ[K] K × K :=
    LinearMap.prod (((QuadraticMap.polarBilin S.Q) p₁).comp (S.X 0).subtype)
      (((QuadraticMap.polarBilin S.Q) p₂).comp (S.X 0).subtype)
  have hφ : ∀ (v : V) (hv : v ∈ S.X 0),
      (φ ⟨v, hv⟩).1 = polar S.Q v p₁ ∧ (φ ⟨v, hv⟩).2 = polar S.Q v p₂ := by
    intro v hv
    constructor
    · simp only [φ, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
        Submodule.subtype_apply, QuadraticMap.polarBilin_apply_apply]
      exact QuadraticMap.polar_comm S.Q p₁ v
    · simp only [φ, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
        Submodule.subtype_apply, QuadraticMap.polarBilin_apply_apply]
      exact QuadraticMap.polar_comm S.Q p₂ v
  have hnotinj : ¬ Function.Injective φ := by
    intro hinj
    have hfin : Module.finrank K (S.X 0) = Module.finrank K (K × K) := by
      rw [show Module.finrank K (S.X 0) = 2 from h0]
      rw [Module.finrank_prod, Module.finrank_self]
    have hsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
    obtain ⟨v₁, hv₁⟩ := hsurj (1, 0)
    obtain ⟨v₂, hv₂⟩ := hsurj (0, 1)
    have hP₁ : polar S.Q v₁.1 p₁ = 1 := by
      rw [← (hφ v₁.1 v₁.2).1, show (φ v₁).1 = 1 from by rw [hv₁]]
    have hP₂ : polar S.Q v₁.1 p₂ = 0 := by
      rw [← (hφ v₁.1 v₁.2).2, show (φ v₁).2 = 0 from by rw [hv₁]]
    have hp₂zero : p₂ = 0 := by
      have h := hcomm v₁.1 v₁.2
      rw [hP₂, hP₁] at h
      simpa using h.symm
    have hQ₁ : polar S.Q v₂.1 p₁ = 0 := by
      rw [← (hφ v₂.1 v₂.2).1, show (φ v₂).1 = 0 from by rw [hv₂]]
    have hQ₂ : polar S.Q v₂.1 p₂ = 1 := by
      rw [← (hφ v₂.1 v₂.2).2, show (φ v₂).2 = 1 from by rw [hv₂]]
    have hp₁zero : p₁ = 0 := by
      have h := hcomm v₂.1 v₂.2
      rw [hQ₂, hQ₁] at h
      simpa using h
    have hzero : φ = 0 := by
      ext v
      · rw [(hφ v.1 v.2).1]
        simp [hp₁zero, QuadraticMap.polar]
      · rw [(hφ v.1 v.2).2]
        simp [hp₂zero, QuadraticMap.polar]
    have hbot : S.X 0 ≠ ⊥ := by
      intro hbot
      have hz : S.mult 0 = 0 := S.X_eq_bot_iff.mp hbot
      omega
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (S.X 0)).mp hbot
    have hEq : (⟨v, hv⟩ : S.X 0) = 0 := hinj (by rw [hzero]; rfl)
    exact hv0 (congrArg Subtype.val hEq)
  have hker : LinearMap.ker φ ≠ ⊥ := fun h => hnotinj (LinearMap.ker_eq_bot.mp h)
  obtain ⟨v₀, hv₀ker, hv₀0⟩ := (Submodule.ne_bot_iff (LinearMap.ker φ)).mp hker
  have hφv₀ : φ v₀ = 0 := LinearMap.mem_ker.mp hv₀ker
  have hP₁ : polar S.Q v₀.1 p₁ = 0 := by
    have h := (hφ v₀.1 v₀.2).1
    rw [hφv₀] at h
    simpa using h.symm
  have hP₂ : polar S.Q v₀.1 p₂ = 0 := by
    have h := (hφ v₀.1 v₀.2).2
    rw [hφv₀] at h
    simpa using h.symm
  exact ⟨v₀.1, v₀.2, fun h => hv₀0 (Subtype.ext h), hP₁, hP₂⟩

private theorem mult_single_two_mul_eq_zero {x y : ZMod (Nat.card Kˣ)} (h2y : 2 * y = x)
    (hpat : ∀ a : Fin 3 → ZMod (Nat.card Kˣ), a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0)
    {k₁ k₂ : ℕ} (hk₁ : (k₁ : ZMod (Nat.card Kˣ)) = y)
    (hk₂ : (k₂ : ZMod (Nat.card Kˣ)) = -y) (hk₁N : k₁ < Nat.card Kˣ)
    (hk₂N : k₂ < Nat.card Kˣ) {k : ℕ} (hk1 : 1 ≤ k) (hklt : k < Nat.card Kˣ)
    (hkk₁ : k ≠ k₁) (hkk₂ : k ≠ k₂) :
    S.mult (Pi.single 2 ((k : ZMod (Nat.card Kˣ)) * 2) :
      Fin 3 → ZMod (Nat.card Kˣ)) = 0 := by
  have hne : (Pi.single 2 ((k : ZMod (Nat.card Kˣ)) * 2) :
      Fin 3 → ZMod (Nat.card Kˣ)) ≠ 0 := by
    intro h
    have h' : (k : ZMod (Nat.card Kˣ)) * 2 = 0 := by simpa using congrFun h 2
    exact natCast_mul_two_ne_zero hk1 hklt h'
  rw [hpat _ hne, if_neg]
  rintro ⟨i, hi | hi⟩
  · by_cases hi2 : i = 2
    · subst hi2
      have h2eq : (k : ZMod (Nat.card Kˣ)) * 2 = x := by
        have := congrFun hi 2
        simpa using this
      have hky : (k : ZMod (Nat.card Kˣ)) = y := by
        have h2eq' : 2 * (k : ZMod (Nat.card Kˣ)) = 2 * y := by
          rw [mul_comm 2 (k : ZMod (Nat.card Kˣ)), h2eq, h2y]
        have hsub : (k : ZMod (Nat.card Kˣ)) - y = 0 := by
          apply (ZMod.add_self_eq_zero_iff_eq_zero odd_natCard_units).mp
          have h2 : 2 * ((k : ZMod (Nat.card Kˣ)) - y) = 0 := by
            rw [mul_sub, h2eq', sub_self]
          simpa [two_mul] using h2
        exact sub_eq_zero.mp hsub
      have hval : k = k₁ := by
        rw [← ZMod.val_natCast_of_lt hklt, hky, ← hk₁, ZMod.val_natCast_of_lt hk₁N]
      exact hkk₁ hval
    · have := congrFun hi 2
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi2)] at this
      exact natCast_mul_two_ne_zero hk1 hklt this
  · by_cases hi2 : i = 2
    · subst hi2
      have h2eq : (k : ZMod (Nat.card Kˣ)) * 2 = -x := by
        have := congrFun hi 2
        simpa using this
      have hky : (k : ZMod (Nat.card Kˣ)) = -y := by
        have h2eq' : 2 * (k : ZMod (Nat.card Kˣ)) = 2 * (-y) := by
          rw [mul_comm 2 (k : ZMod (Nat.card Kˣ)), h2eq]
          rw [show -x = 2 * (-y) from by rw [← h2y]; ring]
        have hsub : (k : ZMod (Nat.card Kˣ)) - (-y) = 0 := by
          apply (ZMod.add_self_eq_zero_iff_eq_zero odd_natCard_units).mp
          have h2 : 2 * ((k : ZMod (Nat.card Kˣ)) - (-y)) = 0 := by
            rw [mul_sub, h2eq', sub_self]
          simpa [two_mul] using h2
        exact sub_eq_zero.mp hsub
      have hval : k = k₂ := by
        rw [← ZMod.val_natCast_of_lt hklt, hky, ← hk₂, ZMod.val_natCast_of_lt hk₂N]
      exact hkk₂ hval
    · have := congrFun hi 2
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hi2)] at this
      exact natCast_mul_two_ne_zero hk1 hklt this

private theorem natural_pattern_kill {x y : ZMod (Nat.card Kˣ)} (h2y : 2 * y = x)
    (hpat : ∀ a : Fin 3 → ZMod (Nat.card Kˣ), a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0)
    {k₁ k₂ : ℕ} (hk₁ : (k₁ : ZMod (Nat.card Kˣ)) = y)
    (hk₂ : (k₂ : ZMod (Nat.card Kˣ)) = -y) (hk₁1 : 1 ≤ k₁) (hk₂1 : 1 ≤ k₂)
    (hk₁N : k₁ < Nat.card Kˣ) (hk₂N : k₂ < Nat.card Kˣ)
    (hsum : k₁ + k₂ = Nat.card Kˣ) {v₀ y₁ y₂ p₁ p₂ : V} (hv₀mem : v₀ ∈ S.X 0)
    (hA₁ : ∀ v ∈ S.X 0, S.A (.positiveLong 2) k₁ v = polar S.Q v p₁ • y₁)
    (hA₂ : ∀ v ∈ S.X 0, S.A (.positiveLong 2) k₂ v = polar S.Q v p₂ • y₂)
    (hP₁ : polar S.Q v₀ p₁ = 0) (hP₂ : polar S.Q v₀ p₂ = 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ Nat.card Kˣ → S.A (.positiveLong 2) k v₀ = 0 := by
  intro k hk1 hkNle
  by_cases hkk₁ : k = k₁
  · subst hkk₁
    rw [hA₁ v₀ hv₀mem, hP₁, zero_smul]
  by_cases hkk₂ : k = k₂
  · subst hkk₂
    rw [hA₂ v₀ hv₀mem, hP₂, zero_smul]
  by_cases hkN : k = Nat.card Kˣ
  · subst hkN
    have hAN : S.A (.positiveLong 2) (Nat.card Kˣ) =
        S.A (.positiveLong 2) k₁ * S.A (.positiveLong 2) k₂ := by
      rw [← S.A_mul_card_sub (.positiveLong 2) (i := k₁) (by omega)]
      rw [show Nat.card Kˣ - k₁ = k₂ from by omega]
    rw [hAN, Module.End.mul_apply, hA₂ v₀ hv₀mem, hP₂, zero_smul, map_zero]
  · have hklt : k < Nat.card Kˣ := by omega
    have hmem : S.A (.positiveLong 2) k v₀ ∈
        S.X (Pi.single 2 ((k : ZMod (Nat.card Kˣ)) * 2) :
          Fin 3 → ZMod (Nat.card Kˣ)) := by
      have h := S.A_mem (r := .positiveLong 2)
        (a := (0 : Fin 3 → ZMod (Nat.card Kˣ))) hv₀mem k
      rw [zero_add, rootWt_positiveLong, ← Pi.single_smul', smul_eq_mul] at h
      exact h
    have hmult0 := mult_single_two_mul_eq_zero S h2y hpat hk₁ hk₂ hk₁N hk₂N hk1 hklt hkk₁ hkk₂
    rw [S.X_eq_bot_iff.mpr hmult0] at hmem
    exact hmem

private theorem false_of_natural_pattern (x : ZMod (Nat.card Kˣ)) (hx : x ≠ 0)
    (h0 : S.mult 0 = 2)
    (hpat : ∀ a : Fin 3 → ZMod (Nat.card Kˣ), a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0) :
    False := by
  have : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨y₁, y₂, hy₁mem, hy₁0, hy₂mem, hy₁₂, hline₁, hline₂⟩ :=
    natural_pattern_lines S x hx hpat
  have hcop : Nat.Coprime 2 (Nat.card Kˣ) := odd_natCard_units.coprime_two_left
  let y : ZMod (Nat.card Kˣ) := (2 : ZMod (Nat.card Kˣ))⁻¹ * x
  have h2y : 2 * y = x := by
    have h2inv : (2 : ZMod (Nat.card Kˣ)) * (2 : ZMod (Nat.card Kˣ))⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one 2 hcop
    change (2 : ZMod (Nat.card Kˣ)) * ((2 : ZMod (Nat.card Kˣ))⁻¹ * x) = x
    rw [← mul_assoc, h2inv, one_mul]
  have hy0 : y ≠ 0 := by
    intro h
    apply hx
    rw [← h2y, h, mul_zero]
  let k₁ : ℕ := y.val
  let k₂ : ℕ := (-y).val
  have hk₁eq : (k₁ : ZMod (Nat.card Kˣ)) = y := ZMod.natCast_zmod_val y
  have hk₂eq : (k₂ : ZMod (Nat.card Kˣ)) = -y := ZMod.natCast_zmod_val (-y)
  have hk₁1 : 1 ≤ k₁ := ZMod.val_pos.mpr hy0
  have hk₁N : k₁ < Nat.card Kˣ := ZMod.val_lt y
  have : NeZero y := ⟨hy0⟩
  have hk₂val : k₂ = Nat.card Kˣ - k₁ := ZMod.val_neg_of_ne_zero y
  have hk₂1 : 1 ≤ k₂ := by rw [hk₂val]; omega
  have hk₂N : k₂ < Nat.card Kˣ := ZMod.val_lt (-y)
  have hsum : k₁ + k₂ = Nat.card Kˣ := by omega
  have hW₁ : (k₁ : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2) =
      (Pi.single 2 x : Fin 3 → ZMod (Nat.card Kˣ)) := by
    rw [rootWt_positiveLong, ← Pi.single_smul', smul_eq_mul]
    congr 1
    rw [hk₁eq, mul_comm, h2y]
  have hW₂ : (k₂ : ZMod (Nat.card Kˣ)) • rootWt K (.positiveLong 2) =
      (Pi.single 2 (-x) : Fin 3 → ZMod (Nat.card Kˣ)) := by
    rw [rootWt_positiveLong, ← Pi.single_smul', smul_eq_mul]
    congr 1
    rw [hk₂eq, show (-y) * 2 = -(2 * y) from by ring, h2y]
  obtain ⟨p₁, p₂, hp₁mem, hp₂mem, hA₁, hA₂, hcomm⟩ :=
    natural_pattern_operators S hk₁1 hk₂1 hsum hW₁ hW₂ hy₁mem hy₂mem hline₁ hline₂
  obtain ⟨v₀, hv₀mem, hv₀0, hP₁, hP₂⟩ :=
    exists_orthogonal_vector S hcomm h0
  have hkill := natural_pattern_kill S h2y hpat hk₁eq hk₂eq hk₁1 hk₂1 hk₁N hk₂N hsum
    hv₀mem hA₁ hA₂ hP₁ hP₂
  have hshort : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∀ c : K,
      S.ψ (elt r c) v₀ = v₀ := by
    intro r hr c
    refine S.fix_of_forall r (a := 0) hv₀mem ?_ c
    intro k hk1 hklt
    rw [zero_add]
    have hne : ((k : ZMod (Nat.card Kˣ)) • rootWt K r) ≠ 0 := smul_rootWt_ne_zero r hk1 hklt
    have hsingle : ∀ (i : Fin 3) (z : ZMod (Nat.card Kˣ)),
        ((k : ZMod (Nat.card Kˣ)) • rootWt K r) ≠ Pi.single i z :=
      fun i z => smul_rootWt_ne_single hr hk1 hklt
    rw [hpat _ hne, if_neg]
    rintro ⟨i, hi | hi⟩
    · exact hsingle i x hi
    · exact hsingle i (-x) hi
  have hlong : ∀ c : K, S.ψ (elt (.positiveLong 2) c) v₀ = v₀ :=
    fun c => S.fix_of_A (.positiveLong 2) (v := v₀) hkill c
  exact hv₀0 (S.eq_zero_of_fixed hshort hlong)

theorem not_natural_pattern :
    ¬ ∃ x : ZMod (Nat.card Kˣ), x ≠ 0 ∧ S.mult 0 = 2 ∧ ∀ a, a ≠ 0 →
      S.mult a = if ∃ i, a = Pi.single i x ∨ a = Pi.single i (-x) then 1 else 0 := by
  rintro ⟨x, hx, h0, hpat⟩
  exact false_of_natural_pattern S x hx h0 hpat

theorem exists_isSpinPattern : ∃ x, S.IsSpinPattern x := by
  rcases S.weight_trichotomy with h8 | hnat | hspin
  · exact absurd h8 S.mult_zero_ne_eight
  · exact absurd hnat S.not_natural_pattern
  · obtain ⟨x, hx, h⟩ := hspin
    exact ⟨x, ⟨hx, h⟩⟩

end SpinSetting

end CFSG.LieType.Sp6Spin
