module

public import CFSG.ClassicalInvolution.Q3.Q3NMBlocks
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLDiag

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3
open scoped MatrixGroups

section Conj

variable {F : Type} [Field F] {n : ℕ}

@[expose] def conjSLAut (D : GL (Fin n) F) : MulAut SL(n, F) where
  toFun x :=
    ⟨(D : Matrix (Fin n) (Fin n) F) * x * ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F),
      by rw [Matrix.det_units_conj]; exact x.2⟩
  invFun x :=
    ⟨((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * x * (D : Matrix (Fin n) (Fin n) F),
      by
        have := Matrix.det_units_conj D⁻¹ (x : Matrix (Fin n) (Fin n) F)
        rw [inv_inv] at this
        rw [this]; exact x.2⟩
  left_inv x := Subtype.ext (by
    simp [Matrix.mul_assoc])
  right_inv x := Subtype.ext (by
    simp [Matrix.mul_assoc])
  map_mul' x y := Subtype.ext (by
    have h : ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (D : Matrix (Fin n) (Fin n) F) = 1 := Units.inv_mul D
    show (D : Matrix (Fin n) (Fin n) F) * ((x : Matrix (Fin n) (Fin n) F) * y) *
        ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((D : Matrix (Fin n) (Fin n) F) * x * ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        ((D : Matrix (Fin n) (Fin n) F) * y * ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    calc (D : Matrix (Fin n) (Fin n) F) * ((x : Matrix (Fin n) (Fin n) F) * y) *
          ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = (D : Matrix (Fin n) (Fin n) F) * x *
            (((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (D : Matrix (Fin n) (Fin n) F)) * y *
              ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

end Conj


section Main

variable {F : Type} [Field F] {n : ℕ}

omit [Field F] in
theorem conjSLAut_coe [Field F] (D : GL (Fin n) F) (x : SL(n, F)) :
    ((conjSLAut D x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (D : Matrix (Fin n) (Fin n) F) * x * ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem mem_fixedSubgroup_conjSLAut (D : GL (Fin n) F) (x : SL(n, F)) :
    x ∈ fixedSubgroup (conjSLAut D) ↔
      (x : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F) =
        (D : Matrix (Fin n) (Fin n) F) * x := by
  have h1 : ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (D : Matrix (Fin n) (Fin n) F) = 1 := Units.inv_mul D
  have h2 : (D : Matrix (Fin n) (Fin n) F) *
      ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := Units.mul_inv D
  rw [mem_fixedSubgroup_iff]
  constructor
  · intro h
    have h' : (D : Matrix (Fin n) (Fin n) F) * x *
        ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = x := by
      have := congrArg (fun y : SL(n, F) => (y : Matrix (Fin n) (Fin n) F)) h
      exact this
    calc (x : Matrix (Fin n) (Fin n) F) * D
        = ((D : Matrix (Fin n) (Fin n) F) * x *
            ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * D := by rw [h']
      _ = (D : Matrix (Fin n) (Fin n) F) * x := by
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro h
    refine Subtype.ext ?_
    show (D : Matrix (Fin n) (Fin n) F) * x *
        ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = x
    rw [← h, Matrix.mul_assoc, h2, Matrix.mul_one]

end Main


section Diag

variable {F : Type} [Field F] [Finite F]

theorem oddCoreIn_fixed_conjDiag_eq_bot (hF : Nat.card F = 3) {n a : ℕ} (ha : 0 < a)
    (han : a < n) (D : GL (Fin n) F)
    (hD : (D : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient SL(n, F) (conjSLAut D))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 :=
    two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  have hn1 : 1 ≤ n := by omega
  set Dm : Matrix (Fin n) (Fin n) F := negBlockK F n 0 a with hDm
  have hDc : negBlockK F n a (n - a) = -Dm := negBlockK_compl han.le
  have hcomm : ∀ x : SL(n, F), x ∈ fixedSubgroup (conjSLAut D) ↔
      (x : Matrix (Fin n) (Fin n) F) * Dm = Dm * x := by
    intro x
    rw [mem_fixedSubgroup_conjSLAut, hD]
  have hneg : ∀ x : SL(n, F), (x : Matrix (Fin n) (Fin n) F) * (-Dm) = (-Dm) * x ↔
      (x : Matrix (Fin n) (Fin n) F) * Dm = Dm * x := by
    intro x
    rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]
  refine oddCoreIn_fixed_eq_bot_of_blocks (isPGroup_center_specialLinear hF hn1) (conjSLAut D)
    (ι := Bool) (fun b => cond b (longRootGroup (negBlockK F n a (n - a)))
      (longRootGroup (negBlockK F n 0 a))) ?_ ?_ ?_ ?_
  · intro b x hx
    cases b
    · exact (hcomm x).mpr hx.1
    · refine (hcomm x).mpr ((hneg x).mp ?_)
      rw [← hDc]
      exact hx.1
  · intro b c hc x hx
    have hc' := (hcomm c).mp hc
    cases b
    · exact conj_mem_longRootGroup_of_commute hc' hx
    · rw [hDc]
      rw [hDc] at hx
      exact conj_mem_longRootGroup_of_commute ((hneg c).mpr hc') hx
  · intro b
    set θ := QuotientGroup.mk' (Subgroup.center SL(n, F)) with hθ
    have hker : θ.ker ≤ Subgroup.center SL(n, F) := (QuotientGroup.ker_mk' _).le
    cases b
    · have hr := range_blockSL_eq_longRootGroupK h2 (n := n) (j := 0) (k := a) (by omega)
      show oddCoreIn ((longRootGroup (negBlockK F n 0 a)).map θ) = ⊥
      rw [← hr, ← MonoidHom.range_comp]
      exact oddCoreIn_range_eq_bot_of_injective _ (comp_blockSL_injective hker _ han)
        (componentOddCore_specialLinear_eq_bot hF a)
    · have hr := range_blockSL_eq_longRootGroupK h2 (n := n) (j := a) (k := n - a) (by omega)
      show oddCoreIn ((longRootGroup (negBlockK F n a (n - a))).map θ) = ⊥
      rw [← hr, ← MonoidHom.range_comp]
      exact oddCoreIn_range_eq_bot_of_injective _ (comp_blockSL_injective hker _ (by omega))
        (componentOddCore_specialLinear_eq_bot hF (n - a))
  · intro ν hν hL
    have hνD := (hcomm ν).mp hν
    refine ⟨1, ?_⟩
    let _ : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
    set e : Fin n → F := fun p => if a ≤ p.val then 1 else -1 with he_def
    have hDe : Dm = Matrix.diagonal e := by
      rw [hDm, negBlockK_eq_diagonal]
      congr 1
      funext p
      by_cases h : p.val < a
      · simp [e, h, not_le.mpr h]
      · simp [e, h, not_lt.mp h]
    have hnegDe : -Dm = Matrix.diagonal (fun p => -e p) := by rw [hDe, Matrix.diagonal_neg]
    have he : ∀ p, e p = 1 ∨ e p = -1 := fun p => by
      by_cases h : a ≤ p.val
      · exact Or.inl (by simp [e, h])
      · exact Or.inr (by simp [e, h])
    have key := mul_self_eq_one_of_commute_single hcard h2 e he ν.2 (by rw [← hDe]; exact hνD) ?_
    · have : ν * ν = 1 := by
        ext i j
        have h' := congrFun (congrFun key i) j
        simpa [Matrix.SpecialLinearGroup.coe_mul] using h'
      simpa [pow_two] using this
    · intro i j hij hee
      rcases he i with h1 | h1
      · have hj1 : e j = 1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n a (n - a)) := by
          rw [hDc, hnegDe]
          exact transvection_mem_longRootGroup_diagonal _ hij (by simp [hee]) (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hL true _ hx)
      · have hj1 : e j = -1 := hee ▸ h1
        have hx : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
            longRootGroup (negBlockK F n 0 a) := by
          rw [← hDm, hDe]
          exact transvection_mem_longRootGroup_diagonal e hij hee (by simp [hj1])
        exact commute_single_of_mul_transvection hij (hL false _ hx)

end Diag


section Hom

variable {F : Type} [Field F] {n : ℕ}

theorem conjSLAut_one : conjSLAut (1 : GL (Fin n) F) = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjSLAut_coe, MulAut.one_apply]
  simp

theorem conjSLAut_mul (D E : GL (Fin n) F) :
    conjSLAut (D * E) = conjSLAut D * conjSLAut E := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjSLAut_coe, MulAut.mul_apply, conjSLAut_coe, conjSLAut_coe]
  simp only [Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

@[expose] def conjSLHom : GL (Fin n) F →* MulAut SL(n, F) where
  toFun := conjSLAut
  map_one' := conjSLAut_one
  map_mul' := conjSLAut_mul

theorem conjSLAut_inv (D : GL (Fin n) F) : conjSLAut D⁻¹ = (conjSLAut D)⁻¹ :=
  map_inv (conjSLHom (F := F) (n := n)) D

end Hom

section Conj

variable {S : Type} [Group S]

theorem fixedSubgroup_conj_aut (α σ : MulAut S) :
    fixedSubgroup (α * σ * α⁻¹) = (fixedSubgroup σ).map (α : S →* S) := by
  ext y
  constructor
  · intro hy
    refine ⟨α⁻¹ y, ?_, by simp⟩
    have h : α (σ (α⁻¹ y)) = y := hy
    show σ (α⁻¹ y) = α⁻¹ y
    have := congrArg (fun z => α⁻¹ z) h
    simpa using this
  · rintro ⟨x, hx, rfl⟩
    have hx' : σ x = x := hx
    show α (σ (α⁻¹ (α x))) = α x
    simp [hx']

theorem oddCoreIn_fixed_conj_eq_bot (α σ : MulAut S) (h : oddCoreIn (fixedSubgroup σ) = ⊥) :
    oddCoreIn (fixedSubgroup (α * σ * α⁻¹)) = ⊥ := by
  rw [fixedSubgroup_conj_aut]
  exact oddCoreIn_map_eq_bot (α : S →* S) α.injective h

end Conj


section Invol

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conjSLAut_eq_one_of_scalar {n : ℕ} (D : GL (Fin n) F) (c : F)
    (hD : (D : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) c) : conjSLAut D = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjSLAut_coe, MulAut.one_apply]
  have hcomm : (D : Matrix (Fin n) (Fin n) F) * x = x * D := by
    rw [hD]
    exact (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq
  rw [hcomm, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem oddCoreIn_fixed_conjInvol_eq_bot (hF : Nat.card F = 3) {n : ℕ} (D : GL (Fin n) F)
    (hD : D * D = 1) (hne : conjSLAut D ≠ 1) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient SL(n, F) (conjSLAut D))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  have hDm : (D : Matrix (Fin n) (Fin n) F) * D = 1 := by
    rw [← Units.val_mul, hD, Units.val_one]
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      apply hne
      have : Subsingleton SL(0, F) := subsingleton_specialLinear_of_le_one (by omega)
      exact MulEquiv.ext fun x => Subsingleton.elim _ _
    · exact hn
  obtain ⟨a, han, P, hP⟩ := exists_sl_conj_diagonal h2 hn hDm
  set M : Matrix (Fin n) (Fin n) F :=
    Matrix.diagonal (fun j : Fin n => if j.val < a then (-1 : F) else 1) with hMdef
  have hPinv : (P : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hDeq : (D : Matrix (Fin n) (Fin n) F) =
      P * M * ((P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
    rw [← hP, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  have hMM : M * M = 1 := by
    rw [hMdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j.val < a <;> simp [h]
  have hscal : ∀ c : F, M = Matrix.scalar (Fin n) c → conjSLAut D = 1 := by
    intro c hc
    refine conjSLAut_eq_one_of_scalar D c ?_
    rw [hDeq, hc, ← (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq, Matrix.mul_assoc,
      hPinv, Matrix.mul_one]
  have ha0 : 0 < a := by
    by_contra h
    have h0 : a = 0 := by omega
    exact hne (hscal 1 (by rw [hMdef, h0]; simp [Matrix.scalar_apply]))
  have han' : a < n := by
    by_contra h
    have hn' : a = n := by omega
    refine hne (hscal (-1) ?_)
    rw [hMdef, Matrix.scalar_apply]
    congr 1
    funext j
    simp [hn', j.isLt]
  let D₀ : GL (Fin n) F := ⟨M, M, hMM, hMM⟩
  have hD₀m : (D₀ : Matrix (Fin n) (Fin n) F) = negBlockK F n 0 a := by
    rw [negBlockK_zero_eq_diagonal]
  let Pg : GL (Fin n) F := Matrix.SpecialLinearGroup.toGL P
  have hDGL : D = Pg * D₀ * Pg⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hDeq
  have hconj : autToCentralQuotient SL(n, F) (conjSLAut D) =
      autToCentralQuotient SL(n, F) (conjSLAut Pg) *
        autToCentralQuotient SL(n, F) (conjSLAut D₀) *
          (autToCentralQuotient SL(n, F) (conjSLAut Pg))⁻¹ := by
    rw [hDGL, conjSLAut_mul, conjSLAut_mul, conjSLAut_inv, map_mul, map_mul, map_inv]
  rw [hconj]
  exact oddCoreIn_fixed_conj_eq_bot _ _ (oddCoreIn_fixed_conjDiag_eq_bot hF ha0 han' D₀ hD₀m)

theorem autOddFreeOn_sl_involDiag (hF : Nat.card F = 3) {n : ℕ} [Group.IsPerfect SL(n, F)]
    {X : Type} [Group X] [Finite X] (ψ : SL(n, F) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(n, F))
    (hodd : ∀ α : MulAut (X ⧸ Subgroup.center X), Odd (orderOf α) →
      α ∈ innSubgroup (X ⧸ Subgroup.center X)) :
    AutOddFreeOn X
      (fun τ => ∃ D : GL (Fin n) F, D * D = 1 ∧ ∀ x, τ (ψ x) = ψ (conjSLAut D x)) := by
  refine (autOddFreeOn_of_lifts ψ hψ hker
    (fun σ => ∃ D : GL (Fin n) F, D * D = 1 ∧ σ = conjSLAut D) hodd ?_).mono ?_
  · rintro σ ⟨D, hD, rfl⟩ hne _
    exact oddCoreIn_fixed_conjInvol_eq_bot hF D hD hne
  · rintro τ ⟨D, hD, hτ⟩
    exact ⟨conjSLAut D, ⟨D, hD, rfl⟩, hτ⟩

end Invol

end CFSG.ClassicalInvolution.Q3.Q3NM
