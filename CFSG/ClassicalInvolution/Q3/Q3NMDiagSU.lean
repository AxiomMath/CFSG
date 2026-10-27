module

public import CFSG.ClassicalInvolution.Q3.Q3NMLie
public import CFSG.ClassicalInvolution.Q3.Q3NMBlocks
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSU

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification CFSG.ClassicalInvolution.Q3

section Gram

variable {E : Type} [Field E] (σ : E ≃+* E) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inv_gram {G : Matrix ι ι E} {D : GL ι E}
    (hD : cT σ (D : Matrix ι ι E) * G * (D : Matrix ι ι E) = G) :
    cT σ ((D⁻¹ : GL ι E) : Matrix ι ι E) * G * ((D⁻¹ : GL ι E) : Matrix ι ι E) = G := by
  have hDi : (D : Matrix ι ι E) * ((D⁻¹ : GL ι E) : Matrix ι ι E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : cT σ ((D⁻¹ : GL ι E) : Matrix ι ι E) *
      (cT σ (D : Matrix ι ι E) * G * (D : Matrix ι ι E)) *
        ((D⁻¹ : GL ι E) : Matrix ι ι E) =
      cT σ ((D : Matrix ι ι E) * ((D⁻¹ : GL ι E) : Matrix ι ι E)) * G *
        ((D : Matrix ι ι E) * ((D⁻¹ : GL ι E) : Matrix ι ι E)) := by
    rw [cT_mul]
    simp only [Matrix.mul_assoc]
  rw [hD, hDi, cT_one, Matrix.one_mul, Matrix.mul_one] at h1
  exact h1

theorem conj_mem_SUG {G : Matrix ι ι E} {D : GL ι E}
    (hD : cT σ (D : Matrix ι ι E) * G * (D : Matrix ι ι E) = G) {x : GL ι E}
    (hx : x ∈ SUG σ G) : D * x * D⁻¹ ∈ SUG σ G := by
  have hDi' := inv_gram σ hD
  obtain ⟨hdet, hu⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    exact hdet
  · rw [Units.val_mul, Units.val_mul, cT_mul, cT_mul]
    calc cT σ ((D⁻¹ : GL ι E) : Matrix ι ι E) *
          (cT σ (x : Matrix ι ι E) * cT σ (D : Matrix ι ι E)) * G *
          ((D : Matrix ι ι E) * (x : Matrix ι ι E) * ((D⁻¹ : GL ι E) : Matrix ι ι E))
        = cT σ ((D⁻¹ : GL ι E) : Matrix ι ι E) * cT σ (x : Matrix ι ι E) *
            (cT σ (D : Matrix ι ι E) * G * (D : Matrix ι ι E)) * (x : Matrix ι ι E) *
              ((D⁻¹ : GL ι E) : Matrix ι ι E) := by simp only [Matrix.mul_assoc]
      _ = cT σ ((D⁻¹ : GL ι E) : Matrix ι ι E) *
            (cT σ (x : Matrix ι ι E) * G * (x : Matrix ι ι E)) *
              ((D⁻¹ : GL ι E) : Matrix ι ι E) := by rw [hD]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hu, hDi']

theorem mem_normalizer_SUG {G : Matrix ι ι E} {D : GL ι E}
    (hD : cT σ (D : Matrix ι ι E) * G * (D : Matrix ι ι E) = G) :
    D ∈ Subgroup.normalizer (SUG σ G : Set (GL ι E)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_SUG σ hD hy, fun hy => ?_⟩
  have := conj_mem_SUG σ (inv_gram σ hD) hy
  simpa [mul_assoc] using this

end Gram


section Blocks

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] {a b : ℕ}

theorem fixed_dgn_block {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {τ : MulAut (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))}
    (hτ : ∀ x, x ∈ fixedSubgroup τ ↔ umat x * dgn μ a b = dgn μ a b * umat x)
    {x : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)}
    (hx : x ∈ fixedSubgroup τ) :
    ∃ (x₁ : Matrix (Fin a) (Fin a) E) (x₂ : Matrix (Fin b) (Fin b) E),
      umat x = fromBlocks x₁ 0 0 x₂ ∧ conjTr (unitaryInvolution E 3 1) x₁ * x₁ = 1 ∧
        conjTr (unitaryInvolution E 3 1) x₂ * x₂ = 1 := by
  have hd := (commute_dgn_iff hμ).mp ((hτ x).mp hx)
  refine ⟨_, _, hd, ?_⟩
  have hu := umat_unitary x
  rw [hd, cT_fromBlocks_diag, fromBlocks_diag_mul_self] at hu
  have := fromBlocks_inj.mp (hu.trans fromBlocks_one.symm)
  exact ⟨this.1, this.2.2.2⟩

theorem mem_fixed_of_blockDiag {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {τ : MulAut (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))}
    (hτ : ∀ x, x ∈ fixedSubgroup τ ↔ umat x * dgn μ a b = dgn μ a b * umat x)
    {x : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)}
    {X : Matrix (Fin a) (Fin a) E} {Y : Matrix (Fin b) (Fin b) E}
    (hx : umat x = fromBlocks X 0 0 Y) : x ∈ fixedSubgroup τ := by
  rw [hτ]
  refine (commute_dgn_iff hμ).mpr ?_
  rw [hx, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

theorem oddCoreIn_fixed_dgn_eq_bot (hE : Nat.card E = 9) {μ : E} (hμ : μ ^ 4 = 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hZ : IsPGroup 2 (Subgroup.center (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))))
    (τ : MulAut (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)))
    (hτ : ∀ x, x ∈ fixedSubgroup τ ↔ umat x * dgn μ a b = dgn μ a b * umat x) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (SUG (unitaryInvolution E 3 1)
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E)) τ)) = ⊥ := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  have h2μ : (2 : E) * μ ≠ 0 := two_mul_ne_zero_of_pow_four h2 (Or.inl hμ)
  set π := QuotientGroup.mk' (Subgroup.center (SUG (unitaryInvolution E 3 1)
    (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E))) with hπ
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ τ (ι := Bool)
    (fun i => cond i (blockHomL a b).range (blockHomR a b).range) ?_ ?_ ?_ ?_
  · intro i x hx
    cases i
    · obtain ⟨B, rfl⟩ := hx
      exact mem_fixed_of_blockDiag h2μ hτ (X := 1) (Y := ((B : GL (Fin b) E) : Matrix _ _ E))
        rfl
    · obtain ⟨A, rfl⟩ := hx
      exact mem_fixed_of_blockDiag h2μ hτ (X := ((A : GL (Fin a) E) : Matrix _ _ E)) (Y := 1)
        rfl
  · intro i c hc x hx
    obtain ⟨c₁, c₂, hcd, hc1, hc2⟩ := fixed_dgn_block h2μ hτ hc
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
    obtain ⟨ν₁, ν₂, hνd, hν1, hν2⟩ := fixed_dgn_block h2μ hτ hν
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

end Blocks





section Main

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem commute_conj_iff {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    {Dm : Matrix ι ι E} {D₀ : Matrix ι' ι' E} {Q : Matrix ι ι' E} {Q' : Matrix ι' ι E}
    (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (hgQ : Dm * Q = Q * D₀) (X : Matrix ι' ι' E) :
    Dm * (Q * X * Q') = (Q * X * Q') * Dm ↔ D₀ * X = X * D₀ := by
  have hQD : Q' * Dm = D₀ * Q' := by
    calc Q' * Dm = Q' * Dm * (Q * Q') := by rw [h1, Matrix.mul_one]
      _ = Q' * (Dm * Q) * Q' := by simp only [Matrix.mul_assoc]
      _ = D₀ * Q' := by rw [hgQ]; simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hDQ : Dm = Q * D₀ * Q' := by
    calc Dm = Dm * (Q * Q') := by rw [h1, Matrix.mul_one]
      _ = (Dm * Q) * Q' := by rw [Matrix.mul_assoc]
      _ = Q * D₀ * Q' := by rw [hgQ]
  constructor
  · intro h
    have h' : Q' * (Dm * (Q * X * Q')) * Q = Q' * ((Q * X * Q') * Dm) * Q := by rw [h]
    have hK : Q' * Dm * Q = D₀ := by rw [hQD, Matrix.mul_assoc, h2, Matrix.mul_one]
    have e1 : Q' * (Dm * (Q * X * Q')) * Q = D₀ * X := by
      calc Q' * (Dm * (Q * X * Q')) * Q = (Q' * Dm * Q) * X * (Q' * Q) := by
            simp only [Matrix.mul_assoc]
        _ = D₀ * X := by rw [hK, h2, Matrix.mul_one]
    have e2 : Q' * ((Q * X * Q') * Dm) * Q = X * D₀ := by
      calc Q' * ((Q * X * Q') * Dm) * Q = (Q' * Q) * X * (Q' * Dm * Q) := by
            simp only [Matrix.mul_assoc]
        _ = X * D₀ := by rw [h2, hK, Matrix.one_mul]
    rw [← e1, ← e2]
    exact h'
  · intro h
    calc Dm * (Q * X * Q') = (Dm * Q) * X * Q' := by simp only [Matrix.mul_assoc]
      _ = Q * (D₀ * X) * Q' := by rw [hgQ]; simp only [Matrix.mul_assoc]
      _ = Q * (X * D₀) * Q' := by rw [h]
      _ = (Q * X * Q') * Dm := by
          rw [show (Q * X * Q') * Dm = Q * X * (Q' * Dm) by simp only [Matrix.mul_assoc], hQD]
          simp only [Matrix.mul_assoc]

theorem mem_normalizer_SU {n : ℕ} {D : GL (Fin n) E}
    (hD : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * antidiag n *
      (D : Matrix (Fin n) (Fin n) E) = antidiag n) :
    D ∈ Subgroup.normalizer (SU (unitaryInvolution E 3 1) n : Set (GL (Fin n) E)) := by
  have := mem_normalizer_SUG (unitaryInvolution E 3 1) hD
  rwa [SUG_antidiag] at this

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem conjAut_eq_one_of_smul_one {n : ℕ} (Y : Subgroup (GL (Fin n) E)) (D : GL (Fin n) E)
    (hN : D ∈ Subgroup.normalizer (Y : Set (GL (Fin n) E))) (c : E)
    (hD : (D : Matrix (Fin n) (Fin n) E) = c • 1) : conjAut Y D hN = 1 := by
  refine MulEquiv.ext fun y => Subtype.ext ?_
  show D * (y : GL (Fin n) E) * D⁻¹ = y
  have hcomm : D * (y : GL (Fin n) E) = y * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem oddCoreIn_fixed_conjSU_eq_bot (hE : Nat.card E = 9) {n : ℕ}
    (hZ : IsPGroup 2 (Subgroup.center (SU (unitaryInvolution E 3 1) n)))
    (D : GL (Fin n) E) (hDD : D * D = 1)
    (hDg : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * antidiag n *
      (D : Matrix (Fin n) (Fin n) E) = antidiag n)
    (hne : conjAut (SU (unitaryInvolution E 3 1) n) D (mem_normalizer_SU hDg) ≠ 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (SU (unitaryInvolution E 3 1) n)
      (conjAut (SU (unitaryInvolution E 3 1) n) D (mem_normalizer_SU hDg)))) = ⊥ := by
  have hDm : (D : Matrix (Fin n) (Fin n) E) * D = 1 := by
    rw [← Units.val_mul, hDD, Units.val_one]
  have hgg : (D : Matrix (Fin n) (Fin n) E) * D = ((1 : E) * 1) • 1 := by
    rw [hDm, one_mul, one_smul]
  obtain ⟨a, b, Q, Q', h1, h2', hQ1, hgQ⟩ := exists_normal_form_one hE (μ := (1 : E))
    (one_pow 4) (cT_antidiag _ n) (isUnit_det_antidiag n) hDg hgg
  have hab : 1 ≤ a ∧ 1 ≤ b := by
    constructor
    · by_contra h0
      obtain rfl : a = 0 := by omega
      exact hne (conjAut_eq_one_of_smul_one _ D _ (-1)
        (eq_smul_one_of_mul_eq h1 hgQ (dgn_left_zero (1 : E))))
    · by_contra h0
      obtain rfl : b = 0 := by omega
      exact hne (conjAut_eq_one_of_smul_one _ D _ 1
        (eq_smul_one_of_mul_eq h1 hgQ (dgn_right_zero (1 : E))))
  set e' : SUG (unitaryInvolution E 3 1) (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) E) ≃*
      SU (unitaryInvolution E 3 1) n :=
    (conjSUG (unitaryInvolution E 3 1) h1 h2' hQ1).trans
      (MulEquiv.subgroupCongr (SUG_antidiag (unitaryInvolution E 3 1) n)) with he'
  have hcoe : ∀ x, (((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = Q * umat x * Q' := fun x => rfl
  have hZ' := isPGroup_center_of_mulEquiv e' hZ
  set τ := conjAut (SU (unitaryInvolution E 3 1) n) D (mem_normalizer_SU hDg) with hτdef
  set τ' := MulAut.congr e'.symm τ with hτ'
  have hτ'fix : ∀ x, x ∈ fixedSubgroup τ' ↔
      umat x * dgn (1 : E) a b = dgn (1 : E) a b * umat x := by
    intro x
    rw [mem_fixedSubgroup_iff]
    have h1' : τ' x = x ↔ τ (e' x) = e' x := by
      show e'.symm (τ (e' x)) = x ↔ _
      rw [MulEquiv.symm_apply_eq]
    have hy : τ (e' x) = e' x ↔ (D : Matrix (Fin n) (Fin n) E) *
        (((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        (((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
          D := by
      constructor
      · intro h
        have h' : D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ =
            ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) := congrArg Subtype.val h
        have : D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) =
            ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D := by
          calc D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E)
              = D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ * D := by
                group
            _ = _ := by rw [h']
        exact congrArg Units.val this
      · intro h
        apply Subtype.ext
        show D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D⁻¹ =
          ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E)
        have : D * ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) =
            ((e' x : SU (unitaryInvolution E 3 1) n) : GL (Fin n) E) * D := Units.ext h
        rw [this]
        group
    rw [h1', hy, hcoe]
    exact (commute_conj_iff h1 h2' hgQ (umat x)).trans eq_comm
  have hres := oddCoreIn_fixed_dgn_eq_bot hE (μ := (1 : E)) (one_pow 4) hab.1 hab.2 hZ' τ' hτ'fix
  have := oddCoreIn_fixed_congr_eq_bot e' τ' hres
  have hcongr : MulAut.congr e' τ' = τ := MulEquiv.ext fun y => by
    show e' (e'.symm (τ (e' (e'.symm y)))) = τ y
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rwa [hcongr] at this

end Main


section Class

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem autOddFreeOn_su_involDiag (hE : Nat.card E = 9) {n : ℕ}
    [Group.IsPerfect (SU (unitaryInvolution E 3 1) n)]
    (hZ : IsPGroup 2 (Subgroup.center (SU (unitaryInvolution E 3 1) n)))
    {X : Type} [Group X] [Finite X] (ψ : SU (unitaryInvolution E 3 1) n →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution E 3 1) n))
    (hodd : ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X)) :
    AutOddFreeOn X (fun τ => ∃ (D : GL (Fin n) E)
      (hDg : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * antidiag n *
        (D : Matrix (Fin n) (Fin n) E) = antidiag n),
      D * D = 1 ∧ ∀ x, τ (ψ x) =
        ψ (conjAut (SU (unitaryInvolution E 3 1) n) D (mem_normalizer_SU hDg) x)) := by
  refine (autOddFreeOn_of_lifts ψ hψ hker
    (fun σ' => ∃ (D : GL (Fin n) E)
      (hDg : cT (unitaryInvolution E 3 1) (D : Matrix (Fin n) (Fin n) E) * antidiag n *
        (D : Matrix (Fin n) (Fin n) E) = antidiag n),
      D * D = 1 ∧ σ' = conjAut (SU (unitaryInvolution E 3 1) n) D (mem_normalizer_SU hDg))
    hodd ?_).mono ?_
  · rintro σ' ⟨D, hDg, hDD, rfl⟩ hne _
    exact oddCoreIn_fixed_conjSU_eq_bot hE hZ D hDD hDg hne
  · rintro τ ⟨D, hDg, hDD, hτ⟩
    exact ⟨_, ⟨D, hDg, hDD, rfl⟩, hτ⟩

end Class
end CFSG.ClassicalInvolution.Q3.Q3NM
