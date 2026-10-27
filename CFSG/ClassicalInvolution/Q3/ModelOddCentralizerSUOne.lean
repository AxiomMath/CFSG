module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUNormal
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUCommutantGen
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification

section One

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] {a b : ℕ}

theorem cT_fromBlocks_diag (X : Matrix (Fin a) (Fin a) E) (Y : Matrix (Fin b) (Fin b) E) :
    cT (unitaryInvolution E 3 1) (fromBlocks X 0 0 Y) =
      fromBlocks (cT (unitaryInvolution E 3 1) X) 0 0 (cT (unitaryInvolution E 3 1) Y) := by
  rw [cT_fromBlocks]
  have h0 : cT (unitaryInvolution E 3 1) (0 : Matrix (Fin a) (Fin b) E) = 0 := by simp [cT]
  have h0' : cT (unitaryInvolution E 3 1) (0 : Matrix (Fin b) (Fin a) E) = 0 := by simp [cT]
  rw [h0, h0']

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem fromBlocks_diag_mul_self (X : Matrix (Fin a) (Fin a) E) (Y : Matrix (Fin b) (Fin b) E)
    (X' : Matrix (Fin a) (Fin a) E) (Y' : Matrix (Fin b) (Fin b) E) :
    (fromBlocks X 0 0 Y : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) * fromBlocks X' 0 0 Y' =
      fromBlocks (X * X') 0 0 (Y * Y') := by
  rw [fromBlocks_multiply]
  simp

@[expose] def dgn (μ : E) (a b : ℕ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
  fromBlocks (μ • 1) 0 0 ((-μ) • 1)

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem eq_zero_of_neg_smul_eq {μ : E} (hμ : (2 : E) * μ ≠ 0) {n m : ℕ}
    {N : Matrix (Fin n) (Fin m) E} (h : (-μ) • N = μ • N) : N = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  have h' : ((2 : E) * μ) * N i j = 0 := by linear_combination -this
  simpa using (mul_eq_zero.mp h').resolve_left hμ

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem commute_dgn_iff {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {N : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E} :
    N * dgn μ a b = dgn μ a b * N ↔ N = fromBlocks N.toBlocks₁₁ 0 0 N.toBlocks₂₂ := by
  constructor
  · intro h
    conv_lhs at h => rw [← fromBlocks_toBlocks N]
    conv_rhs at h => rw [← fromBlocks_toBlocks N]
    rw [dgn, fromBlocks_multiply, fromBlocks_multiply] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h
    obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.mp h
    have h12' := eq_zero_of_neg_smul_eq hμ h12
    have h21' := eq_zero_of_neg_smul_eq hμ h21.symm
    conv_lhs => rw [← fromBlocks_toBlocks N]
    rw [h12', h21']
  · intro h
    rw [h, dgn, fromBlocks_multiply, fromBlocks_multiply]
    simp [Matrix.mul_smul]

@[expose] def fbL (a b : ℕ) : Matrix (Fin a) (Fin a) E →*
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E where
  toFun X := fromBlocks X 0 0 1
  map_one' := fromBlocks_one
  map_mul' X Y := by
    rw [fromBlocks_diag_mul_self, Matrix.one_mul]

@[expose] def fbR (a b : ℕ) : Matrix (Fin b) (Fin b) E →*
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E where
  toFun Y := fromBlocks 1 0 0 Y
  map_one' := fromBlocks_one
  map_mul' X Y := by
    rw [fromBlocks_diag_mul_self, Matrix.one_mul]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem fbL_injective : Function.Injective (fbL (E := E) a b) := fun X Y h => by
  have := congrArg Matrix.toBlocks₁₁ h
  simpa [fbL] using this

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem fbR_injective : Function.Injective (fbR (E := E) a b) := fun X Y h => by
  have := congrArg Matrix.toBlocks₂₂ h
  simpa [fbR] using this

@[expose] noncomputable def blockHomL (a b : ℕ) :
    SUid (unitaryInvolution E 3 1) a →*
      SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) :=
  ((Units.map (fbL (E := E) a b)).comp (SUid (unitaryInvolution E 3 1) a).subtype).codRestrict
    _ fun A => by
      obtain ⟨hdet, hu⟩ := A.2
      refine ⟨?_, ?_⟩
      · show (fromBlocks (A : GL (Fin a) E).val 0 0 (1 : Matrix (Fin b) (Fin b) E)).det = 1
        rw [det_fromBlocks_zero₂₁, hdet, det_one, mul_one]
      · show cT (unitaryInvolution E 3 1) (fromBlocks (A : GL (Fin a) E).val 0 0
          (1 : Matrix (Fin b) (Fin b) E)) * 1 *
          fromBlocks (A : GL (Fin a) E).val 0 0 (1 : Matrix (Fin b) (Fin b) E) = 1
        rw [cT_fromBlocks_diag, Matrix.mul_one, fromBlocks_diag_mul_self, cT_one]
        have : cT (unitaryInvolution E 3 1) (A : GL (Fin a) E).val * (A : GL (Fin a) E).val = 1 :=
          hu
        rw [this, Matrix.one_mul, fromBlocks_one]

@[expose] noncomputable def blockHomR (a b : ℕ) :
    SUid (unitaryInvolution E 3 1) b →*
      SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) :=
  ((Units.map (fbR (E := E) a b)).comp (SUid (unitaryInvolution E 3 1) b).subtype).codRestrict
    _ fun A => by
      obtain ⟨hdet, hu⟩ := A.2
      refine ⟨?_, ?_⟩
      · show (fromBlocks (1 : Matrix (Fin a) (Fin a) E) 0 0 (A : GL (Fin b) E).val).det = 1
        rw [det_fromBlocks_zero₂₁, hdet, det_one, one_mul]
      · show cT (unitaryInvolution E 3 1) (fromBlocks (1 : Matrix (Fin a) (Fin a) E) 0 0
          (A : GL (Fin b) E).val) * 1 *
          fromBlocks (1 : Matrix (Fin a) (Fin a) E) 0 0 (A : GL (Fin b) E).val = 1
        rw [cT_fromBlocks_diag, Matrix.mul_one, fromBlocks_diag_mul_self, cT_one]
        have : cT (unitaryInvolution E 3 1) (A : GL (Fin b) E).val * (A : GL (Fin b) E).val = 1 :=
          hu
        rw [this, Matrix.one_mul, fromBlocks_one]

theorem coe_blockHomL (A : SUid (unitaryInvolution E 3 1) a) :
    (((blockHomL a b A : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) _ E)) :
      GL (Fin a ⊕ Fin b) E) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) =
      fromBlocks ((A : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) 0 0 1 := rfl

theorem coe_blockHomR (A : SUid (unitaryInvolution E 3 1) b) :
    (((blockHomR a b A : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) _ E)) :
      GL (Fin a ⊕ Fin b) E) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) =
      fromBlocks 1 0 0 ((A : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) := rfl

theorem blockHomL_injective : Function.Injective (blockHomL (E := E) a b) := fun _ _ h =>
  Subtype.ext (Units.ext (fbL_injective (congrArg (fun x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) =>
      ((x : GL (Fin a ⊕ Fin b) E) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) h)))

theorem blockHomR_injective : Function.Injective (blockHomR (E := E) a b) := fun _ _ h =>
  Subtype.ext (Units.ext (fbR_injective (congrArg (fun x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) =>
      ((x : GL (Fin a ⊕ Fin b) E) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) h)))

theorem exists_su_conj_gen (hE : Nat.card E = 9) {n : ℕ} {U : Matrix (Fin n) (Fin n) E}
    (hU : conjTr (unitaryInvolution E 3 1) U * U = 1) (X : SUid (unitaryInvolution E 3 1) n) :
    ∃ X' : SUid (unitaryInvolution E 3 1) n,
      ((X' : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        U * ((X : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
          conjTr (unitaryInvolution E 3 1) U := by
  have hUU : U * conjTr (unitaryInvolution E 3 1) U = 1 := mul_eq_one_comm.mp hU
  obtain ⟨hdet, hu⟩ := X.2
  set Xm : Matrix (Fin n) (Fin n) E := ((X : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hXm
  have hdet' : (U * Xm * conjTr (unitaryInvolution E 3 1) U).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdet, mul_one, ← Matrix.det_mul, hUU, Matrix.det_one]
  have hcc : conjTr (unitaryInvolution E 3 1) (conjTr (unitaryInvolution E 3 1) U) = U :=
    cT_cT _ (unitaryInvolution_involutive (card_sq_of_card_nine hE)) U
  have hu' : conjTr (unitaryInvolution E 3 1) (U * Xm * conjTr (unitaryInvolution E 3 1) U) *
      (U * Xm * conjTr (unitaryInvolution E 3 1) U) = 1 := by
    calc conjTr (unitaryInvolution E 3 1) (U * Xm * conjTr (unitaryInvolution E 3 1) U) *
          (U * Xm * conjTr (unitaryInvolution E 3 1) U)
        = U * (conjTr (unitaryInvolution E 3 1) Xm * (conjTr (unitaryInvolution E 3 1) U * U) *
            Xm) * conjTr (unitaryInvolution E 3 1) U := by
          rw [conjTr_mul, conjTr_mul, hcc]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hu, Matrix.mul_one, hUU]
  exact ⟨SUGen.mkSU _ hdet' hu', rfl⟩

@[expose] def umat (x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E :=
  ((x : GL (Fin a ⊕ Fin b) E) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)

theorem umat_mul (x y : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) : umat (x * y) = umat x * umat y := rfl

theorem umat_injective : Function.Injective (umat (E := E) (a := a) (b := b)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem umat_unitary (x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) :
    cT (unitaryInvolution E 3 1) (umat x) * umat x = 1 := by
  have := x.2.2
  rwa [Matrix.mul_one] at this

theorem umat_inv (x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) :
    umat x⁻¹ = cT (unitaryInvolution E 3 1) (umat x) := by
  have h : umat (x⁻¹ * x) = 1 := by rw [inv_mul_cancel]; rfl
  rw [umat_mul] at h
  calc umat x⁻¹ = umat x⁻¹ * (umat x * cT (unitaryInvolution E 3 1) (umat x)) := by
        rw [mul_eq_one_comm.mp (umat_unitary x), Matrix.mul_one]
    _ = (umat x⁻¹ * umat x) * cT (unitaryInvolution E 3 1) (umat x) := by
        rw [Matrix.mul_assoc]
    _ = cT (unitaryInvolution E 3 1) (umat x) := by rw [h, Matrix.one_mul]

theorem mem_centralizer_dgn {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {g₀ x : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)}
    (hg₀ : umat g₀ = dgn μ a b) (hx : x ∈ Subgroup.centralizer ({g₀} : Set _)) :
    ∃ (x₁ : Matrix (Fin a) (Fin a) E) (x₂ : Matrix (Fin b) (Fin b) E),
      umat x = fromBlocks x₁ 0 0 x₂ ∧ conjTr (unitaryInvolution E 3 1) x₁ * x₁ = 1 ∧
        conjTr (unitaryInvolution E 3 1) x₂ * x₂ = 1 := by
  have hc : umat x * dgn μ a b = dgn μ a b * umat x := by
    have := congrArg umat (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rwa [umat_mul, umat_mul, hg₀] at this
  have hd := (commute_dgn_iff hμ).mp hc
  refine ⟨_, _, hd, ?_⟩
  have hu := umat_unitary x
  rw [hd, cT_fromBlocks_diag, fromBlocks_diag_mul_self] at hu
  have := fromBlocks_inj.mp (hu.trans fromBlocks_one.symm)
  exact ⟨this.1, this.2.2.2⟩

theorem umat_pow (x : SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) (n : ℕ) : umat (x ^ n) = umat x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, umat_mul, ih, pow_succ]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem cT_scalar (σ : E ≃+* E) {n : Type} [Fintype n] [DecidableEq n] (c : E) :
    cT σ (Matrix.scalar n c) = Matrix.scalar n (σ c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT]
  · simp [cT, h, Ne.symm h]

theorem exists_scalar_of_commute_su_block (hE : Nat.card E = 9) {n : ℕ} (hn : 1 ≤ n)
    {ν : Matrix (Fin n) (Fin n) E}
    (h : ∀ X : SUid (unitaryInvolution E 3 1) n,
      ν * ((X : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        ((X : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * ν) :
    ∃ c : E, ν = Matrix.scalar (Fin n) c := by
  by_cases h1 : n = 1
  · subst h1
    refine ⟨ν 0 0, Matrix.ext fun i j => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    simp
  · obtain ⟨ω, hω⟩ := exists_sq_eq_neg_one hE
    exact SUGen.exists_scalar_of_commute_su hω (by omega) h

theorem mem_centralizer_of_blockDiag {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {g₀ x : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)}
    (hg₀ : umat g₀ = dgn μ a b) {X : Matrix (Fin a) (Fin a) E} {Y : Matrix (Fin b) (Fin b) E}
    (hx : umat x = fromBlocks X 0 0 Y) : x ∈ Subgroup.centralizer ({g₀} : Set _) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply umat_injective
  rw [umat_mul, umat_mul, hg₀]
  refine (commute_dgn_iff hμ).mpr ?_
  rw [hx, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

theorem oddCoreIn_centralizer_dgn_eq_bot (hE : Nat.card E = 9) {μ : E} (hμ : μ ^ 4 = 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hZ : IsPGroup 2 (Subgroup.center (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))))
    (g₀ : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))
    (hg₀ : umat g₀ = dgn μ a b) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g₀ : SUG (unitaryInvolution E 3 1)
          (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) ⧸ Subgroup.center _)} :
        Set (SUG (unitaryInvolution E 3 1)
          (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) ⧸ Subgroup.center _))) = ⊥ := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  have h2μ : (2 : E) * μ ≠ 0 := two_mul_ne_zero_of_pow_four h2 (Or.inl hμ)
  set π := QuotientGroup.mk' (Subgroup.center (SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))) with hπ
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ g₀ (ι := Bool)
    (fun i => cond i (blockHomL a b).range (blockHomR a b).range) ?_ ?_ ?_ ?_
  · intro i x hx
    cases i
    · obtain ⟨B, rfl⟩ := hx
      exact mem_centralizer_of_blockDiag h2μ hg₀ (X := 1) (Y := ((B : GL (Fin b) E) : Matrix _ _ E))
        rfl
    · obtain ⟨A, rfl⟩ := hx
      exact mem_centralizer_of_blockDiag h2μ hg₀ (X := ((A : GL (Fin a) E) : Matrix _ _ E)) (Y := 1)
        rfl
  · intro i c hc x hx
    obtain ⟨c₁, c₂, hcd, hc1, hc2⟩ := mem_centralizer_dgn h2μ hg₀ hc
    have hc2' : c₂ * cT (unitaryInvolution E 3 1) c₂ = 1 := mul_eq_one_comm.mp hc2
    have hc1' : c₁ * cT (unitaryInvolution E 3 1) c₁ = 1 := mul_eq_one_comm.mp hc1
    cases i
    · obtain ⟨B, rfl⟩ := hx
      obtain ⟨B', hB'⟩ := exists_su_conj_gen hE hc2 B
      refine ⟨B', ?_⟩
      apply umat_injective
      rw [umat_mul, umat_mul, umat_inv, hcd]
      have e1 : umat (blockHomR a b B') =
          fromBlocks 1 0 0 ((B' : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) := rfl
      have e2 : umat (blockHomR a b B) =
          fromBlocks 1 0 0 ((B : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) := rfl
      rw [e1, e2, cT_fromBlocks_diag, fromBlocks_diag_mul_self, fromBlocks_diag_mul_self, hB',
        Matrix.mul_one, hc1']
      rfl
    · obtain ⟨A, rfl⟩ := hx
      obtain ⟨A', hA'⟩ := exists_su_conj_gen hE hc1 A
      refine ⟨A', ?_⟩
      apply umat_injective
      rw [umat_mul, umat_mul, umat_inv, hcd]
      have e1 : umat (blockHomL a b A') =
          fromBlocks ((A' : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) 0 0 1 := rfl
      have e2 : umat (blockHomL a b A) =
          fromBlocks ((A : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) 0 0 1 := rfl
      rw [e1, e2, cT_fromBlocks_diag, fromBlocks_diag_mul_self, fromBlocks_diag_mul_self, hA',
        Matrix.mul_one, hc2']
      rfl
  · intro i
    cases i
    · show oddCoreIn ((blockHomR a b).range.map π) = ⊥
      rw [← MonoidHom.range_comp]
      refine oddCoreIn_range_eq_bot_of_central_kernel (π.comp (blockHomR a b))
        (componentOddCore_suid_eq_bot hE b) ?_ ?_
      · intro X hX
        have h1 : blockHomR a b X ∈ Subgroup.center _ := (QuotientGroup.eq_one_iff _).mp hX
        rw [Subgroup.mem_center_iff]
        intro Y
        apply blockHomR_injective (a := a)
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.mp h1 (blockHomR a b Y)
      · intro X
        obtain ⟨k, hk⟩ := hZ ⟨blockHomR a b X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
        refine ⟨k, Subtype.ext (blockHomR_injective (a := a) ?_)⟩
        simpa using congrArg Subtype.val hk
    · show oddCoreIn ((blockHomL a b).range.map π) = ⊥
      rw [← MonoidHom.range_comp]
      refine oddCoreIn_range_eq_bot_of_central_kernel (π.comp (blockHomL a b))
        (componentOddCore_suid_eq_bot hE a) ?_ ?_
      · intro X hX
        have h1 : blockHomL a b X ∈ Subgroup.center _ := (QuotientGroup.eq_one_iff _).mp hX
        rw [Subgroup.mem_center_iff]
        intro Y
        apply blockHomL_injective (b := b)
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.mp h1 (blockHomL a b Y)
      · intro X
        obtain ⟨k, hk⟩ := hZ ⟨blockHomL a b X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
        refine ⟨k, Subtype.ext (blockHomL_injective (b := b) ?_)⟩
        simpa using congrArg Subtype.val hk
  · intro ν hν hL
    obtain ⟨ν₁, ν₂, hνd, hν1, hν2⟩ := mem_centralizer_dgn h2μ hg₀ hν
    have hL1 : ∀ A : SUid (unitaryInvolution E 3 1) a,
        ν₁ * ((A : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) =
          ((A : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) * ν₁ := by
      intro A
      have h := congrArg umat (hL true (blockHomL a b A) ⟨A, rfl⟩)
      rw [umat_mul, umat_mul, hνd] at h
      have e : umat (blockHomL a b A) =
          fromBlocks ((A : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) 0 0 1 := rfl
      rw [e, fromBlocks_diag_mul_self, fromBlocks_diag_mul_self] at h
      exact (fromBlocks_inj.mp h).1
    have hL2 : ∀ B : SUid (unitaryInvolution E 3 1) b,
        ν₂ * ((B : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) =
          ((B : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) * ν₂ := by
      intro B
      have h := congrArg umat (hL false (blockHomR a b B) ⟨B, rfl⟩)
      rw [umat_mul, umat_mul, hνd] at h
      have e : umat (blockHomR a b B) =
          fromBlocks 1 0 0 ((B : GL (Fin b) E) : Matrix (Fin b) (Fin b) E) := rfl
      rw [e, fromBlocks_diag_mul_self, fromBlocks_diag_mul_self] at h
      exact (fromBlocks_inj.mp h).2.2.2
    obtain ⟨c₁, hc₁⟩ := exists_scalar_of_commute_su_block hE ha hL1
    obtain ⟨c₂, hc₂⟩ := exists_scalar_of_commute_su_block hE hb hL2
    have hn1 : c₁ ^ 4 = 1 := by
      have h : cT (unitaryInvolution E 3 1) ν₁ * ν₁ = 1 := hν1
      rw [hc₁, cT_scalar, ← map_mul] at h
      have := congrFun (congrFun h ⟨0, ha⟩) ⟨0, ha⟩
      exact pow_four_eq_one_of_norm_eq_one (by simpa [Matrix.scalar_apply] using this)
    have hn2 : c₂ ^ 4 = 1 := by
      have h : cT (unitaryInvolution E 3 1) ν₂ * ν₂ = 1 := hν2
      rw [hc₂, cT_scalar, ← map_mul] at h
      have := congrFun (congrFun h ⟨0, hb⟩) ⟨0, hb⟩
      exact pow_four_eq_one_of_norm_eq_one (by simpa [Matrix.scalar_apply] using this)
    refine ⟨2, ?_⟩
    apply umat_injective
    rw [umat_pow, hνd, hc₁, hc₂]
    have hdiag : (fromBlocks (Matrix.scalar (Fin a) c₁) 0 0 (Matrix.scalar (Fin b) c₂) :
        Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) =
        Matrix.diagonal (Sum.elim (fun _ => c₁) (fun _ => c₂)) := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.fromBlocks_diagonal]
    rw [hdiag, Matrix.diagonal_pow]
    show Matrix.diagonal _ = (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)
    rw [← Matrix.diagonal_one]
    congr 1
    funext r
    rcases r with i | i
    · simpa using hn1
    · simpa using hn2

end One





end CFSG.ClassicalInvolution.Q3
