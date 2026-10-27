module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUHyp

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Balance
  CFSG.Assembly.LowTwoRank

section Center

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem exists_smul_one_of_mem_center_su (hE : Nat.card E = 9) {n : ℕ} (hn : 3 ≤ n)
    {z : SU (unitaryInvolution E 3 1) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution E 3 1) n)) :
    ∃ c : E, ((z : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = c • 1 := by
  have hE' := card_sq_of_card_nine hE
  have hnq : (n, 3 ^ 1) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.snd h'
    simp only at this
    omega
  set P := (exists_wittMatrix hE' n).choose with hP
  set e : SU (unitaryInvolution E 3 1) n ≃* StatedSU n (3 ^ 1) E :=
    (conjEquiv P (exists_wittMatrix hE' n).choose_spec).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hE' n)) with he
  have h1 : e z ∈ Subgroup.center (StatedSU n (3 ^ 1) E) := by
    rw [← map_center_mulEquiv e]
    exact ⟨z, hz, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hE' hn hnq).2] at h1
  obtain ⟨u, hu⟩ : ((e z : StatedSU n (3 ^ 1) E) : GL (Fin n) E) ∈ StatedScalars (Fin n) E := h1
  have h4 : ((e z : StatedSU n (3 ^ 1) E) : GL (Fin n) E) = P * (z : GL (Fin n) E) * P⁻¹ := rfl
  have hcent : ∀ g : GL (Fin n) E, g * Matrix.GeneralLinearGroup.scalar (Fin n) u =
      Matrix.GeneralLinearGroup.scalar (Fin n) u * g := fun g => by
    have : Matrix.GeneralLinearGroup.scalar (Fin n) u ∈ Subgroup.center (GL (Fin n) E) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mp this g
  have h5 : (z : GL (Fin n) E) = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    have h6 : P * (z : GL (Fin n) E) * P⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
      rw [← h4, ← hu]
    calc (z : GL (Fin n) E) = P⁻¹ * (P * (z : GL (Fin n) E) * P⁻¹) * P := by group
      _ = P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin n) u * P := by rw [h6]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
        rw [hcent P⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨(u : E), ?_⟩
  rw [h5, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

end Center

section Main

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem cT_antidiag (σ : E ≃+* E) (n : ℕ) :
    cT σ (antidiag n : Matrix (Fin n) (Fin n) E) = antidiag n := by
  ext i j
  simp only [cT, transpose_apply, map_apply, antidiag, of_apply]
  by_cases h : j = Fin.rev i
  · have h' : i = Fin.rev j := by rw [h, Fin.rev_rev]
    rw [ite_eq_left h', ite_eq_left h, map_one]
  · have h' : ¬ i = Fin.rev j := fun h' => h (by rw [h', Fin.rev_rev])
    rw [ite_eq_right h', ite_eq_right h, map_zero]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem isUnit_det_antidiag (n : ℕ) : IsUnit (antidiag n : Matrix (Fin n) (Fin n) E).det :=
  isUnit_iff_ne_zero.mpr (det_antidiag_ne_zero n)

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem isPGroup_center_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPGroup 2 (Subgroup.center Y)) : IsPGroup 2 (Subgroup.center X) := by
  have h1 := h.map e.symm.toMonoidHom
  rwa [map_center_mulEquiv e.symm] at h1

theorem mem_center_su_of_smul_one {n : ℕ} {g : SU (unitaryInvolution E 3 1) n} {c : E}
    (hg : ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = c • 1) :
    g ∈ Subgroup.center (SU (unitaryInvolution E 3 1) n) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  apply Units.ext
  show ((h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
    ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((h : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  rw [hg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem dgn_left_zero {b : ℕ} (μ : E) : dgn μ 0 b = (-μ) • (1 : Matrix (Fin 0 ⊕ Fin b) _ E) := by
  ext r c
  rcases r with i | i
  · exact i.elim0
  · rcases c with j | j
    · exact j.elim0
    · by_cases hij : i = j <;> simp [dgn, fromBlocks, hij]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem dgn_right_zero {a : ℕ} (μ : E) : dgn μ a 0 = μ • (1 : Matrix (Fin a ⊕ Fin 0) _ E) := by
  ext r c
  rcases r with i | i
  · rcases c with j | j
    · simp [dgn, fromBlocks, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem eq_smul_one_of_mul_eq {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] {g : Matrix ι ι E} {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E}
    {D : Matrix ι' ι' E}
    {d : E} (h1 : Q * Q' = 1) (hgQ : g * Q = Q * D) (hD : D = d • 1) : g = d • 1 := by
  calc g = g * (Q * Q') := by rw [h1, Matrix.mul_one]
    _ = (g * Q) * Q' := by rw [Matrix.mul_assoc]
    _ = d • 1 := by
        rw [hgQ, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

theorem oddCoreIn_centralizer_eq_bot_su (hE : Nat.card E = 9) {n : ℕ} (hn : 3 ≤ n)
    (hZ : IsPGroup 2 (Subgroup.center (SU (unitaryInvolution E 3 1) n)))
    (s : SU (unitaryInvolution E 3 1) n ⧸ Subgroup.center (SU (unitaryInvolution E 3 1) n))
    (hs : orderOf s = 2) :
    oddCoreIn (Subgroup.centralizer
      ({s} : Set (SU (unitaryInvolution E 3 1) n ⧸
        Subgroup.center (SU (unitaryInvolution E 3 1) n)))) = ⊥ := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hs2 : (QuotientGroup.mk g : SU (unitaryInvolution E 3 1) n ⧸
      Subgroup.center (SU (unitaryInvolution E 3 1) n)) ^ 2 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one _
  have hs1 : (QuotientGroup.mk g : SU (unitaryInvolution E 3 1) n ⧸
      Subgroup.center (SU (unitaryInvolution E 3 1) n)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hgc : g ∉ Subgroup.center (SU (unitaryInvolution E 3 1) n) := fun h =>
    hs1 ((QuotientGroup.eq_one_iff g).mpr h)
  have hg2c : g * g ∈ Subgroup.center (SU (unitaryInvolution E 3 1) n) :=
    (QuotientGroup.eq_one_iff (g * g)).mp (by rw [QuotientGroup.mk_mul, ← pow_two]; exact hs2)
  obtain ⟨c, hc⟩ := exists_smul_one_of_mem_center_su hE hn hg2c
  have hgg : ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = c • 1 := by
    rw [← hc]
    rfl
  have hc4 : c ^ 4 = 1 := by
    have hu : cT (unitaryInvolution E 3 1) ((g * g : SU (unitaryInvolution E 3 1) n) :
        GL (Fin n) E).val * antidiag n * ((g * g : SU (unitaryInvolution E 3 1) n) :
          GL (Fin n) E).val = antidiag n := (g * g).2.2
    rw [hc, cT_smul, cT_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul] at hu
    have hn0 : 0 < n := by omega
    have := congrFun (congrFun hu ⟨0, hn0⟩) (Fin.rev ⟨0, hn0⟩)
    simp only [Matrix.smul_apply, antidiag, Matrix.of_apply, ite_true, smul_eq_mul,
      mul_one] at this
    exact pow_four_eq_one_of_norm_eq_one (by rw [mul_comm]; exact this)
  obtain ⟨μ, hμ⟩ := exists_sq_eq_of_pow_four_eq_one hE hc4
  have hμ4 : μ ^ 4 = 1 ∨ μ ^ 4 = -1 := by
    refine mul_self_eq_one_iff.mp ?_
    calc μ ^ 4 * μ ^ 4 = (μ * μ) ^ 4 := by ring
      _ = 1 := by rw [hμ, hc4]
  have hggμ : ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (μ * μ) • 1 := by rw [hgg, hμ]
  have hgU : cT (unitaryInvolution E 3 1) ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      antidiag n * ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = antidiag n := g.2.2
  rcases hμ4 with h4 | h4
  · obtain ⟨a, b, Q, Q', h1, h2', hQ1, hgQ⟩ :=
      exists_normal_form_one hE h4 (cT_antidiag _ n) (isUnit_det_antidiag n) hgU hggμ
    set e' : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) ≃*
        SU (unitaryInvolution E 3 1) n :=
      (conjSUG (unitaryInvolution E 3 1) h1 h2' hQ1).trans
        (MulEquiv.subgroupCongr (SUG_antidiag (unitaryInvolution E 3 1) n)) with he'
    have hcoe : ∀ x, (((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) = Q * umat x * Q' := fun x => rfl
    set g₀ := e'.symm g with hg₀def
    have hg₀ : umat g₀ = dgn μ a b := by
      have h := hcoe g₀
      rw [hg₀def, MulEquiv.apply_symm_apply] at h
      calc umat g₀ = Q' * (Q * umat g₀ * Q') * Q := by
            rw [show Q' * (Q * umat g₀ * Q') * Q = (Q' * Q) * umat g₀ * (Q' * Q) by
              simp only [Matrix.mul_assoc], h2', Matrix.one_mul, Matrix.mul_one]
        _ = Q' * ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * Q := by rw [← h]
        _ = Q' * (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * Q) := by
            rw [Matrix.mul_assoc]
        _ = dgn μ a b := by
            rw [hgQ, ← Matrix.mul_assoc, h2', Matrix.one_mul]
            rfl
    have hab : 1 ≤ a ∧ 1 ≤ b := by
      constructor
      · by_contra h0
        obtain rfl : a = 0 := by omega
        apply hgc
        exact mem_center_su_of_smul_one (c := -μ)
          (eq_smul_one_of_mul_eq h1 hgQ (dgn_left_zero μ))
      · by_contra h0
        obtain rfl : b = 0 := by omega
        apply hgc
        exact mem_center_su_of_smul_one (c := μ)
          (eq_smul_one_of_mul_eq h1 hgQ (dgn_right_zero μ))
    have hZ' := isPGroup_center_of_mulEquiv e' hZ
    exact oddCoreIn_centralizer_eq_bot_of_equiv e'.symm g
      (oddCoreIn_centralizer_dgn_eq_bot hE h4 hab.1 hab.2 hZ' g₀ hg₀)
  · obtain ⟨m, Q, Q', h1, h2', hQJ, hgQ⟩ :=
      exists_normal_form_hyp hE h4 (cT_antidiag _ n) (isUnit_det_antidiag n) hgU hggμ
    set e' : SUG (unitaryInvolution E 3 1) (jh E m) ≃* SU (unitaryInvolution E 3 1) n :=
      (conjSUG (unitaryInvolution E 3 1) h1 h2' hQJ).trans
        (MulEquiv.subgroupCongr (SUG_antidiag (unitaryInvolution E 3 1) n)) with he'
    have hcoe : ∀ x, (((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) :
        Matrix (Fin n) (Fin n) E) = Q * hmat x * Q' := fun x => rfl
    set g₀ := e'.symm g with hg₀def
    have hg₀ : hmat g₀ = dgn μ m m := by
      have h := hcoe g₀
      rw [hg₀def, MulEquiv.apply_symm_apply] at h
      calc hmat g₀ = Q' * (Q * hmat g₀ * Q') * Q := by
            rw [show Q' * (Q * hmat g₀ * Q') * Q = (Q' * Q) * hmat g₀ * (Q' * Q) by
              simp only [Matrix.mul_assoc], h2', Matrix.one_mul, Matrix.mul_one]
        _ = Q' * ((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * Q := by rw [← h]
        _ = Q' * (((g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * Q) := by
            rw [Matrix.mul_assoc]
        _ = dgn μ m m := by
            rw [hgQ, ← Matrix.mul_assoc, h2', Matrix.one_mul]
            rfl
    have hm : 1 ≤ m := by
      have := fintype_card_eq_of_mul_eq_one h1 h2'
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      omega
    have hZ' := isPGroup_center_of_mulEquiv e' hZ
    exact oddCoreIn_centralizer_eq_bot_of_equiv e'.symm g
      (oddCoreIn_centralizer_dgn_hyp_eq_bot hE h4 hm hZ' g₀ hg₀)

end Main

theorem simpleOddCentralizerFreeTag_PSU : SimpleOddCentralizerFreeTag .PSU := by
  intro n hp hadm s hs
  have hn : 3 ≤ n := hadm.2.2.1
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hE : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hZ := (modelFiniteCenterTwoGroup3 .PSU n hp trivial hadm).2
  exact oddCoreIn_centralizer_eq_bot_su hE hn hZ s hs

end CFSG.ClassicalInvolution.Q3
