module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUOne

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Balance
  CFSG.ComponentClassification
open scoped MatrixGroups

section Hyp

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] {m : ℕ}

@[expose] def jh (E : Type) [Field E] (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E :=
  fromBlocks 0 1 1 0

@[expose] def hmat (x : SUG (unitaryInvolution E 3 1) (jh E m)) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E :=
  ((x : GL (Fin m ⊕ Fin m) E) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E)

theorem hmat_mul (x y : SUG (unitaryInvolution E 3 1) (jh E m)) :
    hmat (x * y) = hmat x * hmat y := rfl

theorem hmat_injective : Function.Injective (hmat (E := E) (m := m)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem hmat_pow (x : SUG (unitaryInvolution E 3 1) (jh E m)) (n : ℕ) :
    hmat (x ^ n) = hmat x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, hmat_mul, ih, pow_succ]

theorem hmat_unitary (x : SUG (unitaryInvolution E 3 1) (jh E m)) :
    cT (unitaryInvolution E 3 1) (hmat x) * jh E m * hmat x = jh E m := x.2.2

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem cT_diag_mul_jh_mul_diag (σ : E ≃+* E) (A B : Matrix (Fin m) (Fin m) E) :
    cT σ (fromBlocks A 0 0 B) * jh E m * fromBlocks A 0 0 B =
      fromBlocks 0 (cT σ A * B) (cT σ B * A) 0 := by
  have h0 : cT σ (0 : Matrix (Fin m) (Fin m) E) = 0 := by simp [cT]
  rw [jh, cT_fromBlocks, h0]
  simp [fromBlocks_multiply]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem det_cT (σ : E ≃+* E) {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n E) :
    (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose]
  exact (RingHom.map_det (σ : E →+* E) M).symm

theorem mem_centralizer_dgn_hyp {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {g₀ x : SUG (unitaryInvolution E 3 1) (jh E m)} (hg₀ : hmat g₀ = dgn μ m m)
    (hx : x ∈ Subgroup.centralizer ({g₀} : Set _)) :
    ∃ A B : Matrix (Fin m) (Fin m) E, hmat x = fromBlocks A 0 0 B ∧
      cT (unitaryInvolution E 3 1) A * B = 1 ∧ cT (unitaryInvolution E 3 1) B * A = 1 := by
  have hc : hmat x * dgn μ m m = dgn μ m m * hmat x := by
    have := congrArg hmat (Subgroup.mem_centralizer_singleton_iff.mp hx)
    rwa [hmat_mul, hmat_mul, hg₀] at this
  have hd := (commute_dgn_iff hμ).mp hc
  refine ⟨_, _, hd, ?_⟩
  have hu := hmat_unitary x
  rw [hd, cT_diag_mul_jh_mul_diag] at hu
  have := fromBlocks_inj.mp hu
  exact ⟨this.2.1, this.2.2.1⟩

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem sl_mul_inv_coe (S : SL(m, E)) :
    (S : Matrix (Fin m) (Fin m) E) * ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

omit [Finite E] [Fact (Nat.Prime 3)] [CharP E 3] in
theorem sl_inv_mul_coe (S : SL(m, E)) :
    ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) * (S : Matrix (Fin m) (Fin m) E) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

variable (E m) in
@[expose] noncomputable def leviGL (S : SL(m, E)) : GL (Fin m ⊕ Fin m) E :=
  ⟨fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
      (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)),
    fromBlocks ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) 0 0
      (cT (unitaryInvolution E 3 1) (S : Matrix (Fin m) (Fin m) E)), by
      rw [fromBlocks_diag_mul_self, sl_mul_inv_coe, ← cT_mul, sl_mul_inv_coe, cT_one,
        fromBlocks_one], by
      rw [fromBlocks_diag_mul_self, sl_inv_mul_coe, ← cT_mul, sl_inv_mul_coe, cT_one,
        fromBlocks_one]⟩

theorem leviGL_mem (hE : Nat.card E = 9) (S : SL(m, E)) :
    leviGL E m S ∈ SUG (unitaryInvolution E 3 1) (jh E m) := by
  refine ⟨?_, ?_⟩
  · show (fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
        (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E).det = 1
    rw [det_fromBlocks_zero₂₁, S.2, det_cT, (S⁻¹).2, map_one, one_mul]
  · show cT (unitaryInvolution E 3 1) (fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
        (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E))) *
      jh E m * fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
        (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)) = jh E m
    rw [cT_diag_mul_jh_mul_diag, ← cT_mul, sl_inv_mul_coe, cT_one,
      cT_cT _ (unitaryInvolution_involutive (card_sq_of_card_nine hE)), sl_inv_mul_coe]
    rfl

@[expose] noncomputable def leviHom (hE : Nat.card E = 9) (m : ℕ) :
    SL(m, E) →* SUG (unitaryInvolution E 3 1) (jh E m) where
  toFun S := ⟨leviGL E m S, leviGL_mem hE S⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show fromBlocks (((1 : SL(m, E)) : Matrix (Fin m) (Fin m) E)) 0 0
      (cT (unitaryInvolution E 3 1) (((1 : SL(m, E))⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)) =
        1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, cT_one, fromBlocks_one]
  map_mul' S T := by
    apply Subtype.ext
    apply Units.ext
    show fromBlocks (((S * T : SL(m, E))) : Matrix (Fin m) (Fin m) E) 0 0
      (cT (unitaryInvolution E 3 1) ((((S * T)⁻¹ : SL(m, E))) : Matrix (Fin m) (Fin m) E)) =
        fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
          (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)) *
        fromBlocks (T : Matrix (Fin m) (Fin m) E) 0 0
          (cT (unitaryInvolution E 3 1) ((T⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E))
    rw [fromBlocks_diag_mul_self, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, cT_mul]

theorem hmat_leviHom (hE : Nat.card E = 9) (S : SL(m, E)) :
    hmat (leviHom hE m S) = fromBlocks (S : Matrix (Fin m) (Fin m) E) 0 0
      (cT (unitaryInvolution E 3 1) ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E)) := rfl

theorem leviHom_injective (hE : Nat.card E = 9) : Function.Injective (leviHom hE m) :=
  fun S T h => by
    have := congrArg hmat h
    rw [hmat_leviHom, hmat_leviHom] at this
    exact Subtype.ext (fromBlocks_inj.mp this).1

theorem mem_centralizer_of_blockDiag_hyp {μ : E} (hμ : (2 : E) * μ ≠ 0)
    {g₀ x : SUG (unitaryInvolution E 3 1) (jh E m)} (hg₀ : hmat g₀ = dgn μ m m)
    {X Y : Matrix (Fin m) (Fin m) E} (hx : hmat x = fromBlocks X 0 0 Y) :
    x ∈ Subgroup.centralizer ({g₀} : Set _) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply hmat_injective
  rw [hmat_mul, hmat_mul, hg₀]
  refine (commute_dgn_iff hμ).mpr ?_
  rw [hx, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

theorem oddCoreIn_centralizer_dgn_hyp_eq_bot (hE : Nat.card E = 9) {μ : E} (hμ : μ ^ 4 = -1)
    (hm : 1 ≤ m)
    (hZ : IsPGroup 2 (Subgroup.center (SUG (unitaryInvolution E 3 1) (jh E m))))
    (g₀ : SUG (unitaryInvolution E 3 1) (jh E m)) (hg₀ : hmat g₀ = dgn μ m m) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk g₀ : SUG (unitaryInvolution E 3 1) (jh E m) ⧸ Subgroup.center _)} :
        Set (SUG (unitaryInvolution E 3 1) (jh E m) ⧸ Subgroup.center _))) = ⊥ := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_charP_three
  have h2μ : (2 : E) * μ ≠ 0 := two_mul_ne_zero_of_pow_four h2 (Or.inr hμ)
  set π := QuotientGroup.mk' (Subgroup.center (SUG (unitaryInvolution E 3 1) (jh E m))) with hπ
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ g₀ (ι := Unit)
    (fun _ => (leviHom hE m).range) ?_ ?_ ?_ ?_
  · rintro - x ⟨S, rfl⟩
    exact mem_centralizer_of_blockDiag_hyp h2μ hg₀ (hmat_leviHom hE S)
  · rintro - c hc x ⟨S, rfl⟩
    obtain ⟨A, B, hcd, hAB, hBA⟩ := mem_centralizer_dgn_hyp h2μ hg₀ hc
    have hA1 : A * cT (unitaryInvolution E 3 1) B = 1 := mul_eq_one_comm.mp hBA
    have hB1 : B * cT (unitaryInvolution E 3 1) A = 1 := mul_eq_one_comm.mp hAB
    have hcinv : hmat c⁻¹ = fromBlocks (cT (unitaryInvolution E 3 1) B) 0 0
        (cT (unitaryInvolution E 3 1) A) := by
      have h : fromBlocks (cT (unitaryInvolution E 3 1) B) 0 0
          (cT (unitaryInvolution E 3 1) A) * hmat c = 1 := by
        rw [hcd, fromBlocks_diag_mul_self, hBA, hAB, fromBlocks_one]
      show (((c : GL (Fin m ⊕ Fin m) E)⁻¹ : GL (Fin m ⊕ Fin m) E) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E) = _
      exact Units.inv_eq_of_mul_eq_one_left h
    have hdet : (A * (S : Matrix (Fin m) (Fin m) E) * cT (unitaryInvolution E 3 1) B).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, S.2, mul_one, ← Matrix.det_mul, hA1, Matrix.det_one]
    set S' : SL(m, E) := ⟨A * (S : Matrix (Fin m) (Fin m) E) * cT (unitaryInvolution E 3 1) B,
      hdet⟩ with hS'
    have hS'inv : ((S'⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) =
        A * ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) * cT (unitaryInvolution E 3 1) B := by
      refine left_inv_eq_right_inv (sl_inv_mul_coe S') ?_
      calc (S' : Matrix (Fin m) (Fin m) E) * (A * ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) *
            cT (unitaryInvolution E 3 1) B)
          = A * (S : Matrix (Fin m) (Fin m) E) * (cT (unitaryInvolution E 3 1) B * A) *
              ((S⁻¹ : SL(m, E)) : Matrix (Fin m) (Fin m) E) * cT (unitaryInvolution E 3 1) B := by
            simp only [hS', Matrix.mul_assoc]
        _ = 1 := by
            rw [hBA, Matrix.mul_one, Matrix.mul_assoc A, sl_mul_inv_coe, Matrix.mul_one, hA1]
    refine ⟨S', ?_⟩
    apply hmat_injective
    rw [hmat_mul, hmat_mul, hcinv, hcd, hmat_leviHom, hmat_leviHom, fromBlocks_diag_mul_self,
      fromBlocks_diag_mul_self, hS'inv, cT_mul, cT_mul,
      cT_cT _ (unitaryInvolution_involutive (card_sq_of_card_nine hE))]
    simp only [hS', Matrix.mul_assoc]
  · rintro -
    show oddCoreIn ((leviHom hE m).range.map π) = ⊥
    rw [← MonoidHom.range_comp]
    refine oddCoreIn_range_eq_bot_of_central_kernel (π.comp (leviHom hE m))
      (componentOddCore_specialLinear_of_card_nine hE m) ?_ ?_
    · intro X hX
      have h1 : leviHom hE m X ∈ Subgroup.center _ := (QuotientGroup.eq_one_iff _).mp hX
      rw [Subgroup.mem_center_iff]
      intro Y
      apply leviHom_injective hE
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp h1 (leviHom hE m Y)
    · intro X
      obtain ⟨k, hk⟩ := hZ ⟨leviHom hE m X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
      refine ⟨k, Subtype.ext (leviHom_injective hE ?_)⟩
      simpa using congrArg Subtype.val hk
  · intro ν hν hL
    obtain ⟨A, B, hνd, hAB, hBA⟩ := mem_centralizer_dgn_hyp h2μ hg₀ hν
    have hAS : ∀ S : SL(m, E), (S : Matrix (Fin m) (Fin m) E) * A = A * S := by
      intro S
      have h := congrArg hmat (hL () (leviHom hE m S) ⟨S, rfl⟩)
      rw [hmat_mul, hmat_mul, hνd, hmat_leviHom, fromBlocks_diag_mul_self,
        fromBlocks_diag_mul_self] at h
      exact ((fromBlocks_inj.mp h).1).symm
    have hscalar : A ∈ Set.range (Matrix.scalar (Fin m)) :=
      Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => by
        have h := hAS (Matrix.SpecialLinearGroup.transvection t.hij t.c)
        rw [Matrix.SpecialLinearGroup.transvection_coe] at h
        exact h
    obtain ⟨c, hc⟩ := hscalar
    have hAc : A = Matrix.scalar (Fin m) c := hc.symm
    have hAB' : (unitaryInvolution E 3 1 c) • B = 1 := by
      have h := hAB
      rw [hAc, cT_scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h
      exact h
    have hσc : unitaryInvolution E 3 1 c ≠ 0 := by
      intro h0
      have := congrFun (congrFun hAB' ⟨0, hm⟩) ⟨0, hm⟩
      rw [Matrix.smul_apply, h0, zero_smul, Matrix.one_apply_eq] at this
      exact zero_ne_one this
    have hc0 : c ≠ 0 := fun h0 => hσc (by rw [h0, map_zero])
    have hB : B = (unitaryInvolution E 3 1 c)⁻¹ • (1 : Matrix (Fin m) (Fin m) E) := by
      rw [← hAB', smul_smul, inv_mul_cancel₀ hσc, one_smul]
    refine ⟨3, ?_⟩
    apply hmat_injective
    have hdiag : hmat ν = Matrix.diagonal (Sum.elim (fun _ => c)
        (fun _ => (unitaryInvolution E 3 1 c)⁻¹)) := by
      rw [hνd, hAc, hB, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal,
        Matrix.fromBlocks_diagonal]
    rw [hmat_pow, hdiag, Matrix.diagonal_pow]
    show Matrix.diagonal _ = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E)
    rw [← Matrix.diagonal_one]
    congr 1
    funext r
    have h1 : c ^ 8 = 1 := pow_eight_eq_one hE hc0
    have h2' : (unitaryInvolution E 3 1 c) ^ 8 = 1 := pow_eight_eq_one hE hσc
    rcases r with i | i
    · simpa using h1
    · show ((unitaryInvolution E 3 1 c)⁻¹) ^ 2 ^ 3 = 1
      rw [inv_pow, show (2 : ℕ) ^ 3 = 8 from rfl, h2', inv_one]

end Hyp

end CFSG.ClassicalInvolution.Q3
