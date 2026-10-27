module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearTraceZero

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def RowSparse (M : Matrix (Fin 3) (Fin 3) F) (τ : Fin 3 → Fin 3) : Prop :=
  ∀ i j, j ≠ τ i → M i j = 0

theorem RowSparse.mul {M N : Matrix (Fin 3) (Fin 3) F} {τ τ' : Fin 3 → Fin 3}
    (hM : RowSparse M τ) (hN : RowSparse N τ') : RowSparse (M * N) (τ' ∘ τ) := by
  intro i j hj
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · rw [hN (τ i) j hj, mul_zero]
  · intro k _ hk
    rw [hM i k hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem RowSparse.pow {M : Matrix (Fin 3) (Fin 3) F} {τ : Fin 3 → Fin 3}
    (hM : RowSparse M τ) (n : ℕ) : RowSparse (M ^ n) τ^[n] := by
  induction n with
  | zero =>
    intro i j hj
    have hij : i ≠ j := fun h => hj (by simp [h])
    rw [pow_zero, Matrix.one_apply_ne hij]
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ']
    exact ih.mul hM

theorem perm_three_pow_six (σ : Equiv.Perm (Fin 3)) : σ ^ 6 = 1 := by
  revert σ
  decide

theorem pow_ninety_eq_one [Fintype F] (hF : Fintype.card F = 16) {M : Matrix (Fin 3) (Fin 3) F}
    (hdet : M.det ≠ 0) {τ : Fin 3 → Fin 3} (hM : RowSparse M τ) : M ^ 90 = 1 := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 3), ∀ i, τ (σ i) = i := by
    rw [Matrix.det_apply] at hdet
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
    refine ⟨σ, fun i => ?_⟩
    by_contra hne
    apply hσ
    rw [Finset.prod_eq_zero (f := fun k => M (σ k) k) (Finset.mem_univ i)
      (hM (σ i) i (Ne.symm hne)), smul_zero]
  have hτ : τ = ⇑σ⁻¹ := funext fun j => by
    have := hσ (σ⁻¹ j)
    simpa using this
  have h6 := hM.pow 6
  rw [hτ, ← Equiv.Perm.coe_pow, perm_three_pow_six, Equiv.Perm.coe_one] at h6
  set D := M ^ 6 with hD
  have hdiag : D = Matrix.diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, h6 i j (Ne.symm hij)]
  have hdetD : D.det ≠ 0 := by
    rw [hD, Matrix.det_pow]
    exact pow_ne_zero _ hdet
  have hd : ∀ i, D i i ≠ 0 := by
    intro i h
    apply hdetD
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  have h90 : M ^ 90 = D ^ 15 := by rw [hD, ← pow_mul]
  rw [h90, hdiag, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  have := FiniteField.pow_card_sub_one_eq_one (D i i) (hd i)
  rwa [hF] at this

theorem rowSparse_of_mul_diagonal {g : Matrix (Fin 3) (Fin 3) F} {l m : Fin 3 → F}
    (hl : Function.Injective l) (h : g * Matrix.diagonal l = Matrix.diagonal m * g) :
    ∃ τ, RowSparse g τ := by
  classical
  have key : ∀ i j, g i j * l j = m i * g i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  refine ⟨fun i => if hx : ∃ j, g i j ≠ 0 then hx.choose else i, fun i j hj => ?_⟩
  by_contra hne
  have hx : ∃ j, g i j ≠ 0 := ⟨j, hne⟩
  have hj' : j ≠ hx.choose := by simpa [hx] using hj
  have h1 : l j = m i := mul_left_cancel₀ hne (by rw [key, mul_comm])
  have h2 : l hx.choose = m i := mul_left_cancel₀ hx.choose_spec (by rw [key, mul_comm])
  exact hj' (hl (h1.trans h2.symm))

section Sylow

@[expose] def diagSL (a b : Fˣ) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![(a : F), (b : F), ((a * b)⁻¹ : Fˣ)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩

theorem coe_diagSL (a b : Fˣ) : ((diagSL a b : Matrix.SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![(a : F), (b : F), ((a * b)⁻¹ : Fˣ)] := rfl

theorem diagSL_mul (a b c d : Fˣ) : diagSL a b * diagSL c d = diagSL (a * c) (b * d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL, coe_diagSL,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [← Units.val_mul]
    congr 1
    simp only [mul_inv]
    ac_rfl

theorem diagSL_pow (a b : Fˣ) (n : ℕ) : diagSL a b ^ n = diagSL (a ^ n) (b ^ n) := by
  induction n with
  | zero =>
    apply Subtype.ext
    rw [pow_zero, pow_zero, pow_zero, coe_diagSL, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [pow_succ, ih, diagSL_mul, pow_succ, pow_succ]

variable {ω : Fˣ}

theorem injective_eig (hω : orderOf ω = 5) :
    Function.Injective ![(ω : F), ((ω⁻¹ : Fˣ) : F), (((ω * ω⁻¹)⁻¹ : Fˣ) : F)] := by
  have h1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    norm_num at hω
  have h2 : ω ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hω] at this
    norm_num at this
  have hne1 : (ω : F) ≠ ((ω⁻¹ : Fˣ) : F) := by
    intro h
    apply h2
    have := Units.val_injective h
    rw [pow_two]
    calc ω * ω = ω * ω⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel ω
  have hne2 : (ω : F) ≠ (((ω * ω⁻¹)⁻¹ : Fˣ) : F) := by
    rw [mul_inv_cancel, inv_one, Units.val_one]
    exact fun h => h1 (Units.val_eq_one.mp h)
  have hne3 : ((ω⁻¹ : Fˣ) : F) ≠ (((ω * ω⁻¹)⁻¹ : Fˣ) : F) := by
    rw [mul_inv_cancel, inv_one, Units.val_one]
    intro h
    apply h1
    have := Units.val_eq_one.mp h
    rw [inv_eq_one] at this
    exact this
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem diagSL_one_one : diagSL (1 : Fˣ) 1 = 1 := by
  have := diagSL_pow (1 : Fˣ) 1 0
  simp only [pow_zero] at this
  exact this.symm

@[expose] def diagHom : Fˣ × Fˣ →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun p := diagSL p.1 p.2
  map_one' := diagSL_one_one
  map_mul' p q := (diagSL_mul p.1 p.2 q.1 q.2).symm

@[expose] def torusFive (F : Type) [Field F] : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
  ((rootsOfUnity 5 F).prod (rootsOfUnity 5 F)).map diagHom

theorem mem_torusFive {x : Matrix.SpecialLinearGroup (Fin 3) F} :
    x ∈ torusFive F ↔ ∃ a b : Fˣ, a ^ 5 = 1 ∧ b ^ 5 = 1 ∧ diagSL a b = x := by
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, b, (mem_rootsOfUnity 5 a).mp ha, (mem_rootsOfUnity 5 b).mp hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨⟨a, b⟩, ⟨(mem_rootsOfUnity 5 a).mpr ha, (mem_rootsOfUnity 5 b).mpr hb⟩, rfl⟩

theorem pow_five_of_mem_torusFive {x : Matrix.SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ torusFive F) : x ^ 5 = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_torusFive.mp hx
  rw [diagSL_pow, ha, hb, diagSL_one_one]

theorem eq_one_of_mem_torusFive_center {x : Matrix.SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ torusFive F) (hc : x ∈ center (Matrix.SpecialLinearGroup (Fin 3) F)) : x = 1 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := mem_torusFive.mp hx
  obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  have e0 := congrFun (congrFun hra 0) 0
  have e1 := congrFun (congrFun hra 1) 1
  simp only [Matrix.scalar_apply, coe_diagSL, Matrix.diagonal_apply_eq] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  have hr5 : r ^ 5 = 1 := by
    have : ((a : F)) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
    rwa [← e0] at this
  have hr1 : r = 1 := by
    have : r = r ^ 3 * r ^ 3 * (r ^ 5)⁻¹ := by field_simp
    rw [this, hr, hr5]
    simp
  have ha1 : a = 1 := Units.ext (by rw [← e0, hr1, Units.val_one])
  have hb1 : b = 1 := Units.ext (by rw [← e1, hr1, Units.val_one])
  rw [ha1, hb1, diagSL_one_one]

variable (F) in
@[expose] def sylowFive : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
  (torusFive F).map (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F)))

theorem isPGroup_sylowFive : IsPGroup 5 (sylowFive F) := by
  rintro ⟨y, x, hx, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← map_pow, pow_five_of_mem_torusFive hx, map_one]
  rfl

theorem diagSL_pow_mem_torusFive (hω : orderOf ω = 5) (i j : ℕ) :
    diagSL (ω ^ i) (ω ^ j) ∈ torusFive F := by
  have h5 : ω ^ 5 = 1 := by rw [← hω, pow_orderOf_eq_one]
  refine mem_torusFive.mpr ⟨ω ^ i, ω ^ j, ?_, ?_, rfl⟩
  · rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]

theorem le_card_sylowFive [Finite F] (hω : orderOf ω = 5) : 25 ≤ Nat.card (sylowFive F) := by
  classical
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := inferInstance
  let f : Fin 5 × Fin 5 → sylowFive F := fun p =>
    ⟨QuotientGroup.mk (diagSL (ω ^ p.1.val) (ω ^ p.2.val)),
      ⟨_, diagSL_pow_mem_torusFive hω _ _, rfl⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : (QuotientGroup.mk (diagSL (ω ^ i.val) (ω ^ j.val)) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) =
        QuotientGroup.mk (diagSL (ω ^ i'.val) (ω ^ j'.val)) := congrArg Subtype.val h
    rw [QuotientGroup.eq] at h1
    have h2 := eq_one_of_mem_torusFive_center (mul_mem (inv_mem
      (diagSL_pow_mem_torusFive hω _ _)) (diagSL_pow_mem_torusFive hω _ _)) h1
    rw [inv_mul_eq_one] at h2
    have e0 := congrFun (congrFun (congrArg Subtype.val h2) 0) 0
    have e1 := congrFun (congrFun (congrArg Subtype.val h2) 1) 1
    simp only [coe_diagSL, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one] at e0 e1
    have hi := (pow_inj_mod (x := ω)).mp (Units.ext e0)
    have hj := (pow_inj_mod (x := ω)).mp (Units.ext e1)
    rw [hω, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at hi
    rw [hω, Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt j'.2] at hj
    rw [Fin.ext hi, Fin.ext hj]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at this

theorem pow_ninety_of_mem_normalizer_sylowFive [Fintype F] (hF : Fintype.card F = 16)
    (hω : orderOf ω = 5) {y : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F}
    (hy : y ∈ normalizer ((sylowFive F : Subgroup _) : Set _)) : y ^ 90 = 1 := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  set s₁ := diagSL ω ω⁻¹ with hs₁def
  have hs₁ : s₁ ∈ torusFive F := by
    have h5 : ω ^ 5 = 1 := by rw [← hω, pow_orderOf_eq_one]
    exact mem_torusFive.mpr ⟨ω, ω⁻¹, h5, by rw [inv_pow, h5, inv_one], rfl⟩
  have h1 : (QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) *
      QuotientGroup.mk s₁ * (QuotientGroup.mk g)⁻¹ ∈ sylowFive F :=
    (mem_normalizer_iff.mp hy _).mp ⟨s₁, hs₁, rfl⟩
  obtain ⟨x, hx, hxe⟩ := h1
  obtain ⟨a, b, -, -, rfl⟩ := mem_torusFive.mp hx
  have hxe' : (QuotientGroup.mk (g * s₁ * g⁻¹) : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) =
      QuotientGroup.mk (diagSL a b) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hxe.symm
  rw [QuotientGroup.eq] at hxe'
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxe'
  rw [Fintype.card_fin] at hr3
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr3; norm_num at hr3
  have hmat : ((g : Matrix (Fin 3) (Fin 3) F)) * Matrix.diagonal
      ![(ω : F), ((ω⁻¹ : Fˣ) : F), (((ω * ω⁻¹)⁻¹ : Fˣ) : F)] =
      Matrix.diagonal (fun i => r⁻¹ * ![(a : F), (b : F), (((a * b)⁻¹ : Fˣ) : F)] i) *
        (g : Matrix (Fin 3) (Fin 3) F) := by
    have e1 : ((diagSL a b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g * s₁ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          Matrix.scalar (Fin 3) r := by
      rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have e2 : Matrix.diagonal (fun i => r⁻¹ * ![(a : F), (b : F), (((a * b)⁻¹ : Fˣ) : F)] i) =
        ((g * s₁ * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have : Matrix.diagonal (fun i => r⁻¹ * ![(a : F), (b : F), (((a * b)⁻¹ : Fˣ) : F)] i) =
          Matrix.scalar (Fin 3) r⁻¹ *
            ((diagSL a b : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        rw [coe_diagSL, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
      rw [this, e1, ← Matrix.mul_assoc, Matrix.scalar_commute _ (fun _ => Commute.all _ _),
        Matrix.mul_assoc]
      rw [show Matrix.scalar (Fin 3) r⁻¹ * Matrix.scalar (Fin 3) r = 1 by
        rw [← map_mul, inv_mul_cancel₀ hr0, map_one], Matrix.mul_one]
    rw [e2, ← coe_diagSL ω ω⁻¹, ← hs₁def, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  obtain ⟨τ, hτ⟩ := rowSparse_of_mul_diagonal (injective_eig hω) hmat
  have h90 := pow_ninety_eq_one hF (by rw [g.2]; exact one_ne_zero) hτ
  have hg90 : g ^ 90 = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, h90]; rfl)
  rw [← QuotientGroup.mk_pow, hg90, QuotientGroup.mk_one]

end Sylow

theorem not_five_dvd_index {X : Type*} [Group X] [Finite X] (hX : ¬ 125 ∣ Nat.card X)
    {P : Subgroup X} (hP : Nat.card P = 25) : ¬ 5 ∣ P.index := by
  intro h
  apply hX
  rw [← P.card_mul_index, hP]
  exact Nat.mul_dvd_mul_left 25 h

theorem pow_ninety_of_mem_normalizer {X : Type*} [Group X] [Finite X] {F : Type} [Field F]
    [Fintype F] (hF : Fintype.card F = 16)
    (θ : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) (hX : ¬ 125 ∣ Nat.card X)
    {P : Subgroup X} (hP : Nat.card P = 25) {y : X} (hy : y ∈ normalizer (P : Set X)) :
    y ^ 90 = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Fˣ, orderOf ω = 5 := by
    apply exists_prime_orderOf_dvd_card
    rw [Fintype.card_units, hF]
    norm_num
  set X₀ := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F
  have hX₀ : ¬ 125 ∣ Nat.card X₀ := by rwa [← Nat.card_congr θ.toEquiv]
  set P' := P.map θ.toMonoidHom with hP'def
  have hP' : Nat.card P' = 25 := by
    rw [hP'def, Subgroup.card_map_of_injective θ.injective, hP]
  have hP'5 : IsPGroup 5 P' := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  set SP := hP'5.toSylow (not_five_dvd_index hX₀ hP') with hSP
  have hS₀5 := isPGroup_sylowFive (F := F)
  obtain ⟨k, hk⟩ := hS₀5.exists_card_eq
  have hS₀ : Nat.card (sylowFive F) = 25 := by
    have h25 := le_card_sylowFive hω
    have hdvd : 5 ^ k ∣ Nat.card X₀ := hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk2 : k ≤ 2 := by
      by_contra hlt
      apply hX₀
      exact (Nat.pow_dvd_pow 5 (by omega : 3 ≤ k)).trans hdvd
    have hk2' : 2 ≤ k := by
      by_contra hlt
      have : 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hk, show k = 2 by omega]
    norm_num
  set SS := hS₀5.toSylow (not_five_dvd_index hX₀ hS₀) with hSS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X₀ SP SS
  have hy' : θ y ∈ normalizer ((P' : Subgroup X₀) : Set X₀) := by
    rw [mem_normalizer_iff]
    intro z
    obtain ⟨w, rfl⟩ := θ.surjective z
    rw [hP'def, mem_map_equiv, mem_map_equiv, ← map_inv, ← map_mul, ← map_mul,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact (mem_normalizer_iff.mp hy) w
  have hyS : θ y • SP = SP := Sylow.smul_eq_iff_mem_normalizer.mpr hy'
  have hgS : (g * θ y * g⁻¹) • SS = SS := by
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hyS]
  have hn : g * θ y * g⁻¹ ∈ normalizer ((sylowFive F : Subgroup X₀) : Set X₀) := by
    exact Sylow.smul_eq_iff_mem_normalizer.mp hgS
  have h90 := pow_ninety_of_mem_normalizer_sylowFive hF hω hn
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h90
  apply θ.injective
  rw [map_pow, h90, map_one]

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
