module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

namespace FourGroupOddUnitary

open FourGroupOddBilinear

section General

variable {E : Type*} [Field E] {σ : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
  (h : V →ₛₗ[σ] V →ₗ[E] E)

@[expose] def unitaryScalars : Subgroup (sesqSpecialUnitaryGroup h) where
  carrier := {g | ∃ c : Eˣ,
    ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = (c : E) • LinearMap.id}
  one_mem' := ⟨1, by simp; rfl⟩
  mul_mem' := by
    rintro g g' ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_eq_comp, hc, hd]
    ext v
    simp [mul_smul]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have h1 : ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) *
        ((g⁻¹ : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    rw [hc] at h1
    ext v
    have := congrArg (fun f : Module.End E V => ((c⁻¹ : Eˣ) : E) • f v) h1
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Module.End.one_apply, smul_smul, Units.inv_mul, one_smul] at this
    simpa using this

theorem mem_unitaryScalars {g : sesqSpecialUnitaryGroup h} :
    g ∈ unitaryScalars h ↔ ∃ c : Eˣ,
      ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = (c : E) • LinearMap.id :=
  Iff.rfl

instance unitaryScalars_normal : (unitaryScalars h).Normal := ⟨by
  rintro z ⟨c, hc⟩ g
  refine ⟨c, ?_⟩
  have h1 : ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) *
      ((g⁻¹ : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  simp only [Subgroup.coe_mul, Units.val_mul, hc]
  ext v
  have := congrFun (congrArg DFunLike.coe h1) v
  simp only [Module.End.mul_apply, Module.End.one_apply, Subgroup.coe_inv] at this
  simp [Module.End.mul_apply, this]⟩

abbrev unitaryProj : Type _ :=
  sesqSpecialUnitaryGroup h ⧸ unitaryScalars h

@[expose] def unitaryProjMk : sesqSpecialUnitaryGroup h →* unitaryProj h :=
  QuotientGroup.mk' (unitaryScalars h)

@[expose] def unitaryCentralizer (A : LinearMap.GeneralLinearGroup E V) :
    Subgroup (sesqSpecialUnitaryGroup h) :=
  (Subgroup.centralizer {A}).subgroupOf (sesqSpecialUnitaryGroup h)

end General

section Transfer

variable {E : Type*} [Field E] {σ : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
  {h : V →ₛₗ[σ] V →ₗ[E] E} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)

@[expose] def matrixGL (X : Matrix ι ι E) (hX : X.det ≠ 0) : LinearMap.GeneralLinearGroup E V :=
  Units.map (Matrix.toLinAlgEquiv b : Matrix ι ι E →* Module.End E V)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero X hX)

theorem coe_matrixGL (X : Matrix ι ι E) (hX : X.det ≠ 0) :
    (matrixGL b X hX : V →ₗ[E] V) = Matrix.toLin b b X :=
  rfl

theorem sesq_toLin_basis (G : Matrix ι ι E) (hG : ∀ i j, h (b i) (b j) = G i j)
    (X : Matrix ι ι E) (i j : ι) :
    h (Matrix.toLin b b X (b i)) (Matrix.toLin b b X (b j)) =
      ∑ k, ∑ l, σ (X k i) * X l j * G k l := by
  simp only [Matrix.toLin_self, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, hG, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem matrixGL_mem_unitary (G : Matrix ι ι E) (hG : ∀ i j, h (b i) (b j) = G i j)
    {X : Matrix ι ι E} (hX : X.det ≠ 0) (hXσ : ∀ i j, σ (X i j) = X i j)
    (hXG : Xᵀ * G * X = G) : matrixGL b X hX ∈ sesqUnitaryGroup h := by
  intro x y
  have hext : (h.comp (Matrix.toLin b b X)).compl₂ (Matrix.toLin b b X) = h := by
    refine LinearMap.ext_basis b b fun i j => ?_
    rw [LinearMap.compl₂_apply, LinearMap.comp_apply, sesq_toLin_basis b G hG, hG,
      ← congrFun (congrFun hXG i) j]
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, hXσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact LinearMap.congr_fun₂ hext x y

theorem matrixGL_mem_special (G : Matrix ι ι E) (hG : ∀ i j, h (b i) (b j) = G i j)
    {X : Matrix ι ι E} (hX : X.det = 1) (hXσ : ∀ i j, σ (X i j) = X i j)
    (hXG : Xᵀ * G * X = G) :
    matrixGL b X (by rw [hX]; exact one_ne_zero) ∈ sesqSpecialUnitaryGroup h :=
  mem_sesqSpecialUnitaryGroup.2 ⟨matrixGL_mem_unitary b G hG _ hXσ hXG, by
    rw [coe_matrixGL, LinearMap.det_toLin, hX]⟩

theorem toLin_eq_smul_id {X : Matrix ι ι E} {c : E}
    (hX : Matrix.toLin b b X = c • LinearMap.id) : X = c • 1 := by
  apply (Matrix.toLin b b).injective
  rw [hX, map_smul, Matrix.toLin_one]

end Transfer

section Model

variable {E : Type*} [Field E] {σ : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
  {h : V →ₛₗ[σ] V →ₗ[E] E} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_four_of_model (b : Module.Basis ι E V) (A : LinearMap.GeneralLinearGroup E V)
    (D : Matrix ι ι E) (hD : LinearMap.toMatrix b b (A : V →ₗ[E] V) = D)
    (G : Matrix ι ι E) (hG : ∀ i j, h (b i) (b j) = G i j)
    {X Y : Matrix ι ι E} (hXσ : ∀ i j, σ (X i j) = X i j) (hYσ : ∀ i j, σ (Y i j) = Y i j)
    (hXG : Xᵀ * G * X = G) (hYG : Yᵀ * G * Y = G) (hXD : X * D = D * X) (hYD : Y * D = D * Y)
    (hXd : X.det = 1) (hYd : Y.det = 1) (hXX : X * X = 1) (hYY : Y * Y = 1)
    (hXY : X * Y = Y * X ∨ X * Y = -(Y * X)) (hX : ∀ a : E, X ≠ a • 1)
    (hY : ∀ a : E, Y ≠ a • 1) (hXYn : ∀ a : E, X * Y ≠ a • 1) :
    ∃ W : Subgroup (unitaryProj h), W ≤ (unitaryCentralizer h A).map (unitaryProjMk h) ∧
      CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  have hA : (A : V →ₗ[E] V) = Matrix.toLin b b D := by rw [← hD, Matrix.toLin_toMatrix]
  have hcoe : ∀ (M : Matrix ι ι E) (hM : M.det = 1),
      ((matrixGL b M (by rw [hM]; exact one_ne_zero) : LinearMap.GeneralLinearGroup E V) :
        V →ₗ[E] V) = Matrix.toLin b b M := fun M hM => rfl
  let x : sesqSpecialUnitaryGroup h := ⟨_, matrixGL_mem_special b G hG hXd hXσ hXG⟩
  let y : sesqSpecialUnitaryGroup h := ⟨_, matrixGL_mem_special b G hG hYd hYσ hYG⟩
  have hx : ((x : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = Matrix.toLin b b X := rfl
  have hy : ((y : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = Matrix.toLin b b Y := rfl
  have hmul : ∀ g g' : sesqSpecialUnitaryGroup h,
      (((g * g' : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) =
        ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) *
          ((g' : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) := fun g g' => rfl
  have htoLin_mul : ∀ M N : Matrix ι ι E,
      Matrix.toLin b b M * Matrix.toLin b b N = Matrix.toLin b b (M * N) := fun M N => by
    rw [Matrix.toLin_mul b b b]
    rfl
  have hcent : ∀ (M : Matrix ι ι E) (g : sesqSpecialUnitaryGroup h),
      ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = Matrix.toLin b b M → M * D = D * M →
        g ∈ unitaryCentralizer h A := by
    intro M g hg hMD
    change (g : LinearMap.GeneralLinearGroup E V) ∈ Subgroup.centralizer {A}
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hg, hA, htoLin_mul, htoLin_mul, hMD]
  have hscal : ∀ (M : Matrix ι ι E) (g : sesqSpecialUnitaryGroup h),
      ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = Matrix.toLin b b M →
        (∀ a : E, M ≠ a • 1) → g ∉ unitaryScalars h := by
    rintro M g hg hM ⟨c, hc⟩
    rw [hg] at hc
    exact hM _ (toLin_eq_smul_id b hc)
  have hsq : ∀ (M : Matrix ι ι E) (g : sesqSpecialUnitaryGroup h),
      ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = Matrix.toLin b b M → M * M = 1 →
        unitaryProjMk h g * unitaryProjMk h g = 1 := by
    intro M g hg hMM
    have : g * g = 1 := Subtype.ext (Units.ext (by
      rw [hmul, hg, htoLin_mul, hMM, Matrix.toLin_one]
      rfl))
    rw [← map_mul, this, map_one]
  have hpx := hsq X x hx hXX
  have hpy := hsq Y y hy hYY
  have hpxy : unitaryProjMk h x * unitaryProjMk h y = unitaryProjMk h y * unitaryProjMk h x := by
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.2 ?_
    rcases hXY with hc | hc
    · have : x * y = y * x := Subtype.ext (Units.ext (by
        rw [hmul, hmul, hx, hy, htoLin_mul, htoLin_mul, hc]))
      rw [this, inv_mul_cancel]
      exact (unitaryScalars h).one_mem
    · refine ⟨-1, ?_⟩
      have hyx : (((y * x : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) :
          V →ₗ[E] V) = -(((x * y : sesqSpecialUnitaryGroup h) :
            LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) := by
        rw [hmul, hmul, hx, hy, htoLin_mul, htoLin_mul, hc, map_neg, neg_neg]
      rw [hmul, hyx, mul_neg]
      have h1 : ((((x * y)⁻¹ : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) :
          V →ₗ[E] V) * (((x * y : sesqSpecialUnitaryGroup h) : LinearMap.GeneralLinearGroup E V) :
            V →ₗ[E] V) = 1 := by
        rw [← hmul, inv_mul_cancel]
        rfl
      rw [h1]
      ext v
      simp
  have hpx1 : unitaryProjMk h x ≠ 1 := fun h1 =>
    hscal X x hx hX ((QuotientGroup.eq_one_iff x).1 h1)
  have hpy1 : unitaryProjMk h y ≠ 1 := fun h1 =>
    hscal Y y hy hY ((QuotientGroup.eq_one_iff y).1 h1)
  have hpne : unitaryProjMk h x ≠ unitaryProjMk h y := fun h1 => by
    have h2 : unitaryProjMk h (x * y) = 1 := by rw [map_mul, ← h1, hpx]
    exact hscal (X * Y) (x * y) (by rw [hmul, hx, hy, htoLin_mul]) hXYn
      ((QuotientGroup.eq_one_iff _).1 h2)
  obtain ⟨W, -, hWle, hW, hWcard⟩ := FourGroup.exists_kleinFour hpx hpy hpxy hpx1 hpy1 hpne
  exact ⟨W, hWle _ (Subgroup.mem_map_of_mem _ (hcent X x hx hXD))
    (Subgroup.mem_map_of_mem _ (hcent Y y hy hYD)), hW, hWcard⟩

end Model

section Decomposition

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

theorem isCompl_eigen (h2 : (2 : E) ≠ 0) {J : Module.End E V} (hJ : J * J = 1) :
    IsCompl (LinearMap.ker (J - 1)) (LinearMap.ker (J + 1)) := by
  have hJv : ∀ v, J (J v) = v := fun v => by rw [← Module.End.mul_apply, hJ, Module.End.one_apply]
  refine IsCompl.of_eq ?_ ?_
  · refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    obtain ⟨h₁, h₂⟩ := Submodule.mem_inf.1 hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h₁
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, h₁] at h₂
    have : (2 : E) • v = 0 := by rw [two_smul]; exact h₂
    exact (smul_eq_zero.1 this).resolve_left h2
  · refine eq_top_iff.2 fun v _ => Submodule.mem_sup.2
      ⟨(2 : E)⁻¹ • (v + J v), ?_, (2 : E)⁻¹ • (v - J v), ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, map_smul, map_add, hJv, Module.End.one_apply]
      module
    · rw [LinearMap.mem_ker]
      simp only [LinearMap.add_apply, map_smul, map_sub, hJv, Module.End.one_apply]
      module
    · rw [← smul_add, show v + J v + (v - J v) = (2 : E) • v by module, smul_smul,
        inv_mul_cancel₀ h2, one_smul]

@[expose] def sumBasis {p q : Submodule E V} (hpq : IsCompl p q) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ E p) (b₂ : Module.Basis ι₂ E q) : Module.Basis (ι₁ ⊕ ι₂) E V :=
  (b₁.prod b₂).map (Submodule.prodEquivOfIsCompl p q hpq)

theorem sumBasis_inl {p q : Submodule E V} (hpq : IsCompl p q) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ E p) (b₂ : Module.Basis ι₂ E q) (i : ι₁) :
    sumBasis hpq b₁ b₂ (Sum.inl i) = (b₁ i : V) := by
  simp [sumBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem sumBasis_inr {p q : Submodule E V} (hpq : IsCompl p q) {ι₁ ι₂ : Type*}
    (b₁ : Module.Basis ι₁ E p) (b₂ : Module.Basis ι₂ E q) (j : ι₂) :
    sumBasis hpq b₁ b₂ (Sum.inr j) = (b₂ j : V) := by
  simp [sumBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)
    {f : V →ₗ[E] V} {μ : ι → E} (hf : ∀ i, f (b i) = μ i • b i) :
    LinearMap.toMatrix b b f = diagonal μ := by
  ext i j
  rw [LinearMap.toMatrix_apply, hf, map_smul, Module.Basis.repr_self, diagonal_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem toMatrix_sumBasis {p q : Submodule E V} (hpq : IsCompl p q) {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E p)
    (b₂ : Module.Basis ι₂ E q) {f : V →ₗ[E] V} {μ₁ μ₂ : E} (hf₁ : ∀ v ∈ p, f v = μ₁ • v)
    (hf₂ : ∀ v ∈ q, f v = μ₂ • v) :
    LinearMap.toMatrix (sumBasis hpq b₁ b₂) (sumBasis hpq b₁ b₂) f =
      diagonal (Sum.elim (fun _ => μ₁) (fun _ => μ₂)) :=
  toMatrix_eq_diagonal _ fun α => by
    rcases α with i | j
    · rw [sumBasis_inl, hf₁ _ (b₁ i).2]
      rfl
    · rw [sumBasis_inr, hf₂ _ (b₂ j).2]
      rfl

theorem map_signDiag {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : E →+* E) (S : Finset ι)
    (i j : ι) : σ (signDiag S i j) = signDiag S i j := by
  rw [signDiag_apply]
  split_ifs <;> simp

theorem signDiag_supported_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (μ : ι → E) : ∀ i j, diagonal μ i j ≠ 0 → (i ∈ S ↔ j ∈ S) := fun i j hij => by
  rw [diagonal_apply] at hij
  split_ifs at hij with hh
  · rw [hh]
  · exact absurd rfl hij

theorem pair_supported {m : ℕ} (k : Fin m) :
    ∀ α β, (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E) α β ≠ 0 →
      (α ∈ ({Sum.inl k, Sum.inr k} : Finset (Fin m ⊕ Fin m)) ↔
        β ∈ ({Sum.inl k, Sum.inr k} : Finset (Fin m ⊕ Fin m))) := by
  rintro (i | i) (j | j) hne
  · simp at hne
  · rw [fromBlocks_apply₁₂, one_apply] at hne
    split_ifs at hne with hij
    · subst hij; simp
    · exact absurd rfl hne
  · rw [fromBlocks_apply₂₁, one_apply] at hne
    split_ifs at hne with hij
    · subst hij; simp
    · exact absurd rfl hne
  · simp at hne

end Decomposition

section Pairs

variable {E : Type*} [Field E]

@[expose] def pairSign : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) E :=
  fromBlocks !![-1, 0; 0, 1] 0 0 !![-1, 0; 0, 1]

@[expose] def pairSwap : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) E :=
  fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0]

theorem map_pairSign (σ : E →+* E) : ∀ i j, σ ((pairSign : Matrix _ _ E) i j) = pairSign i j := by
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairSign]

theorem map_pairSwap (σ : E →+* E) : ∀ i j, σ ((pairSwap : Matrix _ _ E) i j) = pairSwap i j := by
  rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairSwap]

theorem pairSign_gram :
    (pairSign : Matrix _ _ E)ᵀ * fromBlocks 0 1 1 0 * pairSign = fromBlocks 0 1 1 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairSign, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]

theorem pairSwap_gram :
    (pairSwap : Matrix _ _ E)ᵀ * fromBlocks 0 1 1 0 * pairSwap = fromBlocks 0 1 1 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairSwap, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, one_apply]

theorem pairSign_diagonal (a : E) :
    (pairSign : Matrix _ _ E) * diagonal (Sum.elim (fun _ => a) (fun _ => -a)) =
      diagonal (Sum.elim (fun _ => a) (fun _ => -a)) * pairSign := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairSign, Matrix.mul_apply, diagonal]

theorem pairSwap_diagonal (a : E) :
    (pairSwap : Matrix _ _ E) * diagonal (Sum.elim (fun _ => a) (fun _ => -a)) =
      diagonal (Sum.elim (fun _ => a) (fun _ => -a)) * pairSwap := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairSwap, Matrix.mul_apply, diagonal]

theorem det_pairSign : (pairSign : Matrix _ _ E).det = 1 := by
  simp [pairSign, det_fromBlocks_zero₂₁, det_fin_two_of]

theorem det_pairSwap : (pairSwap : Matrix _ _ E).det = 1 := by
  simp [pairSwap, det_fromBlocks_zero₂₁, det_fin_two_of]

theorem pairSign_mul_self : (pairSign : Matrix _ _ E) * pairSign = 1 := by
  simp [pairSign, fromBlocks_multiply, ← fromBlocks_one, Matrix.one_fin_two]

theorem pairSwap_mul_self : (pairSwap : Matrix _ _ E) * pairSwap = 1 := by
  simp [pairSwap, fromBlocks_multiply, ← fromBlocks_one, Matrix.one_fin_two]

theorem pairSign_mul_pairSwap :
    (pairSign : Matrix _ _ E) * pairSwap = -(pairSwap * pairSign) := by
  simp [pairSign, pairSwap, fromBlocks_multiply, fromBlocks_neg]

theorem pairSign_ne_smul (h2 : (2 : E) ≠ 0) (a : E) : (pairSign : Matrix _ _ E) ≠ a • 1 :=
  fun h => by
    have h0 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    have h1 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
    simp [pairSign] at h0 h1
    exact h2 (by linear_combination h1 - h0)

theorem pairSwap_ne_smul (a : E) : (pairSwap : Matrix _ _ E) ≠ a • 1 := fun h => by
  have h0 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
  simp [pairSwap] at h0

theorem pairSign_mul_pairSwap_ne_smul (a : E) : (pairSign : Matrix _ _ E) * pairSwap ≠ a • 1 :=
  fun h => by
    have h0 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [pairSign, pairSwap, fromBlocks_multiply] at h0

end Pairs

end FourGroupOddUnitary

open FourGroupOddUnitary FourGroupOddBilinear

theorem odd_unitary_scalar_square_centralizer_projective_four_group {p f : ℕ} {E : Type*}
    [Field E] (hE : UnitaryFieldData p f E) (hp : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (hn : 3 ≤ Module.finrank E V)
    {h : V →ₛₗ[hE.bar] V →ₗ[E] E} (hh : h.IsSymm) (hnd : h.SeparatingLeft)
    (A : LinearMap.GeneralLinearGroup E V) (hA : A ∈ sesqUnitaryGroup h) (c : Eˣ)
    (hAc : (A : V →ₗ[E] V) * (A : V →ₗ[E] V) = (c : E) • (1 : Module.End E V)) :
    ∃ W : Subgroup (unitaryProj h), W ≤ (unitaryCentralizer h A).map (unitaryProjMk h) ∧
      CFSG.IsElementaryAbelian 2 W ∧ Nat.card W = 4 := by
  classical
  have := hE.finite
  have := Fintype.ofFinite E
  have hcharP := hE.charP
  have hchar2 : ringChar E ≠ 2 := by rw [ringChar.eq E p]; exact hp
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero hchar2
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by omega)
  have hAx : ∀ x y, h ((A : V →ₗ[E] V) x) ((A : V →ₗ[E] V) y) = h x y := hA
  have hAA : ∀ x, (A : V →ₗ[E] V) ((A : V →ₗ[E] V) x) = (c : E) • x := fun x => by
    have := congrFun (congrArg DFunLike.coe hAc) x
    simpa [Module.End.mul_apply] using this
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨y₀, hy₀⟩ : ∃ y, h x₀ y ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hx₀ (hnd x₀ hall)
  have hNc : hE.bar c * c = 1 := by
    have h1 := hAx ((A : V →ₗ[E] V) x₀) ((A : V →ₗ[E] V) y₀)
    rw [hAA, hAA, hAx] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h1
    have h1' : (hE.bar c * c - 1) * h x₀ y₀ = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1').resolve_right hy₀)
  have hq : Odd (p ^ f) := (hE.prime.odd_of_ne_two hp).pow
  have hcq : (c : E) ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← hE.bar_apply]
    exact hNc
  obtain ⟨a, ha⟩ : IsSquare (c : E) := by
    rw [FiniteField.isSquare_iff hchar2 c.ne_zero]
    have hcard : Fintype.card E = (p ^ f) ^ 2 := by
      rw [Fintype.card_eq_nat_card, hE.card_eq_sq]
    obtain ⟨k, hk⟩ := hq
    have hk2 : (p ^ f) ^ 2 / 2 = (p ^ f + 1) * k := by
      rw [hk, show (2 * k + 1) ^ 2 = 2 * ((2 * k + 1 + 1) * k) + 1 by ring,
        Nat.mul_add_div (by norm_num : 0 < 2)]
      norm_num
    rw [hcard, hk2, pow_mul, hcq, one_pow]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha
    exact c.ne_zero ha
  set J : Module.End E V := a⁻¹ • (A : V →ₗ[E] V) with hJdef
  have hJv : ∀ v, J v = a⁻¹ • (A : V →ₗ[E] V) v := fun v => rfl
  have hJJ : J * J = 1 := by
    ext v
    rw [Module.End.mul_apply, hJv, hJv, map_smul, hAA, smul_smul, smul_smul, Module.End.one_apply,
      ha, show a⁻¹ * a⁻¹ * (a * a) = 1 by field_simp, one_smul]
  have hJform : ∀ x y, h (J x) (J y) = (hE.bar a * a)⁻¹ * h x y := fun x y => by
    rw [hJv, hJv]
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hAx, map_inv₀]
    have : hE.bar a ≠ 0 := fun h0 => ha0 ((hE.bar_eq_zero_iff).1 h0)
    field_simp
  have hNa : hE.bar a * a = 1 ∨ hE.bar a * a = -1 := by
    have : (hE.bar a * a) * (hE.bar a * a) = 1 := by
      rw [← hNc, ha, map_mul]
      ring
    exact mul_self_eq_one_iff.1 this
  set Vp := LinearMap.ker (J - 1) with hVp
  set Vm := LinearMap.ker (J + 1) with hVm
  have hc : IsCompl Vp Vm := isCompl_eigen h2 hJJ
  have hJp : ∀ v ∈ Vp, J v = v := fun v hv => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  have hJm : ∀ v ∈ Vm, J v = -v := fun v hv => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    exact hv
  have hAJ : ∀ v, (A : V →ₗ[E] V) v = a • J v := fun v => by
    rw [hJv, smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hAp : ∀ v ∈ Vp, (A : V →ₗ[E] V) v = a • v := fun v hv => by rw [hAJ, hJp v hv]
  have hAm : ∀ v ∈ Vm, (A : V →ₗ[E] V) v = (-a) • v := fun v hv => by
    rw [hAJ, hJm v hv, smul_neg, neg_smul]
  have hdecomp : ∀ z : V, ∃ z₁ ∈ Vp, ∃ z₂ ∈ Vm, z₁ + z₂ = z := fun z =>
    Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top)
  have hsep : ∀ x : V, (∀ y ∈ Vp, h x y = 0) → (∀ y ∈ Vm, h x y = 0) → x = 0 :=
    fun x h₁ h₂ => hnd x fun z => by
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hdecomp z
      rw [map_add, h₁ z₁ hz₁, h₂ z₂ hz₂, add_zero]
  rcases hNa with hN | hN
  ·
    have hJiso : ∀ x y, h (J x) (J y) = h x y := fun x y => by rw [hJform, hN, inv_one, one_mul]
    have horth : ∀ v ∈ Vp, ∀ w ∈ Vm, h v w = 0 := fun v hv w hw => by
      have h1 := hJiso v w
      rw [hJp v hv, hJm w hw, map_neg] at h1
      have : (2 : E) * h v w = 0 := by linear_combination -h1
      exact (mul_eq_zero.1 this).resolve_left h2
    have horth' : ∀ w ∈ Vm, ∀ v ∈ Vp, h w v = 0 := fun w hw v hv => by
      rw [← hh.eq v w, horth v hv w hw, map_zero]
    obtain ⟨ep, hep⟩ := hE.exists_orthonormal_basis (M := Vp) (B := h.domRestrict₁₂ Vp Vp)
      ⟨fun x y => hh.eq x y⟩ (fun x hx => Subtype.ext (hsep x (fun y hy => hx ⟨y, hy⟩)
        (fun y hy => horth x x.2 y hy)))
    obtain ⟨em, hem⟩ := hE.exists_orthonormal_basis (M := Vm) (B := h.domRestrict₁₂ Vm Vm)
      ⟨fun x y => hh.eq x y⟩ (fun x hx => Subtype.ext (hsep x
        (fun y hy => horth' x x.2 y hy) (fun y hy => hx ⟨y, hy⟩)))
    set b := sumBasis hc ep em with hb
    have hG : ∀ α β, h (b α) (b β) = (1 : Matrix _ _ E) α β := by
      rintro (i | i) (j | j)
      · rw [sumBasis_inl, sumBasis_inl, one_apply]
        have := hep i j
        rw [LinearMap.domRestrict₁₂_apply] at this
        rw [this]
        simp
      · rw [sumBasis_inl, sumBasis_inr, horth _ (ep i).2 _ (em j).2, one_apply]
        simp
      · rw [sumBasis_inr, sumBasis_inl, horth' _ (em i).2 _ (ep j).2, one_apply]
        simp
      · rw [sumBasis_inr, sumBasis_inr, one_apply]
        have := hem i j
        rw [LinearMap.domRestrict₁₂_apply] at this
        rw [this]
        simp
    have hD := toMatrix_sumBasis hc ep em hAp hAm
    have hcard : 3 ≤ Fintype.card (Fin (Module.finrank E Vp) ⊕ Fin (Module.finrank E Vm)) := by
      rw [← Module.finrank_eq_card_basis b]
      exact hn
    let e := (Fintype.equivFin (Fin (Module.finrank E Vp) ⊕ Fin (Module.finrank E Vm))).symm
    let i₀ := e ⟨0, by omega⟩
    let i₁ := e ⟨1, by omega⟩
    let i₂ := e ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := fun h => by simpa [Fin.ext_iff] using e.injective h
    have h02 : i₀ ≠ i₂ := fun h => by simpa [Fin.ext_iff] using e.injective h
    have h12 : i₁ ≠ i₂ := fun h => by simpa [Fin.ext_iff] using e.injective h
    have h1diag : ∀ S : Finset (Fin (Module.finrank E Vp) ⊕ Fin (Module.finrank E Vm)), ∀ i j,
        (1 : Matrix _ _ E) i j ≠ 0 → (i ∈ S ↔ j ∈ S) := fun S i j hij => by
      rw [one_apply] at hij
      split_ifs at hij with hh'
      · rw [hh']
      · exact absurd rfl hij
    refine exists_four_of_model b A _ hD 1 hG (X := signDiag {i₀, i₁}) (Y := signDiag {i₀, i₂})
      (map_signDiag _ _) (map_signDiag _ _) (signDiag_conj (h1diag _)) (signDiag_conj (h1diag _))
      (signDiag_mul_comm (signDiag_supported_diagonal _ _))
      (signDiag_mul_comm (signDiag_supported_diagonal _ _))
      (by rw [det_signDiag, Finset.card_pair h01]; norm_num)
      (by rw [det_signDiag, Finset.card_pair h02]; norm_num) (signDiag_mul_self _)
      (signDiag_mul_self _) (Or.inl (signDiag_comm _ _))
      (signDiag_ne_smul h2 (S := {i₀, i₁}) (i := i₀) (j := i₂) (by simp)
        (by simp [h02.symm, h12.symm]))
      (signDiag_ne_smul h2 (S := {i₀, i₂}) (i := i₀) (j := i₁) (by simp) (by simp [h01.symm, h12]))
      (fun x hx => ?_)
    have h0 := congrFun (congrFun hx i₀) i₀
    have h1 := congrFun (congrFun hx i₁) i₁
    rw [signDiag_mul_signDiag_apply_self, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] at h0 h1
    simp only [Finset.mem_insert, Finset.mem_singleton, h01.symm, h12, h01, true_or,
      or_false, or_true, ↓reduceIte] at h0 h1
    exact h2 (by linear_combination h0 - h1)
  ·
    have hJanti : ∀ x y, h (J x) (J y) = -h x y := fun x y => by
      rw [hJform, hN, inv_neg, inv_one, neg_one_mul]
    have hisop : ∀ v ∈ Vp, ∀ v' ∈ Vp, h v v' = 0 := fun v hv v' hv' => by
      have h1 := hJanti v v'
      rw [hJp v hv, hJp v' hv'] at h1
      have : (2 : E) * h v v' = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_left h2
    have hisom : ∀ w ∈ Vm, ∀ w' ∈ Vm, h w w' = 0 := fun w hw w' hw' => by
      have h1 := hJanti w w'
      rw [hJm w hw, hJm w' hw'] at h1
      simp only [map_neg, LinearMap.neg_apply, neg_neg] at h1
      have : (2 : E) * h w w' = 0 := by linear_combination h1
      exact (mul_eq_zero.1 this).resolve_left h2
    have hnull_m : ∀ w ∈ Vm, (∀ v ∈ Vp, h v w = 0) → w = 0 := fun w hw hvw => by
      have hall : ∀ z : V, h z w = 0 := fun z => by
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hdecomp z
        rw [map_add, LinearMap.add_apply, hvw z₁ hz₁, hisom z₂ hz₂ w hw, add_zero]
      exact hnd w fun z => by rw [← hh.eq z w, hall z, map_zero]
    have hnull_p : ∀ v ∈ Vp, (∀ w ∈ Vm, h w v = 0) → v = 0 := fun v hv hwv => by
      have hall : ∀ z : V, h z v = 0 := fun z => by
        obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hdecomp z
        rw [map_add, LinearMap.add_apply, hisop z₁ hz₁ v hv, hwv z₂ hz₂, add_zero]
      exact hnd v fun z => by rw [← hh.eq z v, hall z, map_zero]
    obtain ⟨m, hm⟩ : ∃ m, Module.finrank E Vp = m := ⟨_, rfl⟩
    obtain ⟨m', hm'⟩ : ∃ m', Module.finrank E Vm = m' := ⟨_, rfl⟩
    let u : Module.Basis (Fin m) E Vp := Module.finBasisOfFinrankEq E Vp hm
    let u' : Module.Basis (Fin m') E Vm := Module.finBasisOfFinrankEq E Vm hm'
    let φ : Vm →ₗ[E] (Fin m → E) := LinearMap.pi fun i => (h (u i : V)).comp Vm.subtype
    let ψ : Vp →ₗ[E] (Fin m' → E) := LinearMap.pi fun j => (h (u' j : V)).comp Vp.subtype
    have hφ : ∀ (w : Vm) i, φ w i = h (u i : V) w := fun w i => rfl
    have hψ : ∀ (v : Vp) j, ψ v j = h (u' j : V) v := fun v j => rfl
    have hφinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hu0 : ∀ i, h (u i : V) (w : V) = 0 := fun i => by rw [← hφ, hw]; rfl
      have hext : (h.flip (w : V)).comp Vp.subtype = 0 :=
        Module.Basis.ext u fun i => by simp [hu0]
      exact Subtype.ext (hnull_m w w.2 fun v hv => by
        simpa using LinearMap.congr_fun hext ⟨v, hv⟩)
    have hψinj : Function.Injective ψ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have hu0 : ∀ j, h (u' j : V) (v : V) = 0 := fun j => by rw [← hψ, hv]; rfl
      have hext : (h.flip (v : V)).comp Vm.subtype = 0 :=
        Module.Basis.ext u' fun j => by simp [hu0]
      exact Subtype.ext (hnull_p v v.2 fun w hw => by
        simpa using LinearMap.congr_fun hext ⟨w, hw⟩)
    have hmm' : m' = m := le_antisymm
      (by have := LinearMap.finrank_le_finrank_of_injective hφinj
          rwa [hm', Module.finrank_fin_fun] at this)
      (by have := LinearMap.finrank_le_finrank_of_injective hψinj
          rwa [hm, Module.finrank_fin_fun] at this)
    let φe : Vm ≃ₗ[E] (Fin m → E) :=
      LinearMap.linearEquivOfInjective φ hφinj (by rw [hm', Module.finrank_fin_fun, hmm'])
    let w : Module.Basis (Fin m) E Vm := (Pi.basisFun E (Fin m)).map φe.symm
    have hw : ∀ i j, h (u i : V) (w j : V) = (1 : Matrix (Fin m) (Fin m) E) i j := fun i j => by
      rw [← hφ, ← LinearMap.linearEquivOfInjective_apply hφinj
        (by rw [hm', Module.finrank_fin_fun, hmm'])]
      change φe (φe.symm (Pi.basisFun E (Fin m) j)) i = _
      rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, one_apply, Pi.single_apply]
    set b := sumBasis hc u w with hb
    have hG : ∀ α β, h (b α) (b β) =
        (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E) α β := by
      rintro (i | i) (j | j)
      · rw [sumBasis_inl, sumBasis_inl, fromBlocks_apply₁₁, Matrix.zero_apply,
          hisop _ (u i).2 _ (u j).2]
      · rw [sumBasis_inl, sumBasis_inr, fromBlocks_apply₁₂, hw]
      · rw [sumBasis_inr, sumBasis_inl, fromBlocks_apply₂₁, ← hh.eq, hw, one_apply, one_apply]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Ne.symm hij]
      · rw [sumBasis_inr, sumBasis_inr, fromBlocks_apply₂₂, Matrix.zero_apply,
          hisom _ (w i).2 _ (w j).2]
    have hD := toMatrix_sumBasis hc u w hAp hAm
    have hm2 : 2 ≤ m := by
      have := Module.finrank_eq_card_basis b
      rw [Fintype.card_sum, Fintype.card_fin] at this
      omega
    by_cases hm3 : 3 ≤ m
    ·
      let p0 : Fin m := ⟨0, by omega⟩
      let p1 : Fin m := ⟨1, by omega⟩
      let p2 : Fin m := ⟨2, by omega⟩
      have h01 : p0 ≠ p1 := by simp [p0, p1, Fin.ext_iff]
      have h02 : p0 ≠ p2 := by simp [p0, p2, Fin.ext_iff]
      have h12 : p1 ≠ p2 := by simp [p1, p2, Fin.ext_iff]
      refine exists_four_of_model b A _ hD _ hG (X := signDiag {Sum.inl p0, Sum.inr p0})
        (Y := signDiag {Sum.inl p1, Sum.inr p1}) (map_signDiag _ _) (map_signDiag _ _)
        (signDiag_conj (pair_supported p0)) (signDiag_conj (pair_supported p1))
        (signDiag_mul_comm (signDiag_supported_diagonal _ _))
        (signDiag_mul_comm (signDiag_supported_diagonal _ _))
        (by rw [det_signDiag, Finset.card_pair (by simp)]; norm_num)
        (by rw [det_signDiag, Finset.card_pair (by simp)]; norm_num) (signDiag_mul_self _)
        (signDiag_mul_self _) (Or.inl (signDiag_comm _ _))
        (signDiag_ne_smul h2 (S := {Sum.inl p0, Sum.inr p0}) (i := Sum.inl p0)
          (j := Sum.inl p1) (by simp) (by simp [h01.symm]))
        (signDiag_ne_smul h2 (S := {Sum.inl p1, Sum.inr p1}) (i := Sum.inl p1)
          (j := Sum.inl p0) (by simp) (by simp [h01]))
        (fun x hx => ?_)
      have h0 := congrFun (congrFun hx (Sum.inl p0)) (Sum.inl p0)
      have h1 := congrFun (congrFun hx (Sum.inl p2)) (Sum.inl p2)
      rw [signDiag_mul_signDiag_apply_self, Matrix.smul_apply, one_apply_eq, smul_eq_mul,
        mul_one] at h0 h1
      simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, h01,
        h02.symm, h12.symm, or_false, ↓reduceIte] at h0 h1
      exact h2 (by linear_combination h1 - h0)
    ·
      have hm2' : m = 2 := by omega
      subst hm2'
      exact exists_four_of_model b A _ hD _ hG (X := pairSign) (Y := pairSwap)
        (map_pairSign _) (map_pairSwap _) pairSign_gram pairSwap_gram (pairSign_diagonal a)
        (pairSwap_diagonal a) det_pairSign det_pairSwap pairSign_mul_self pairSwap_mul_self
        (Or.inr pairSign_mul_pairSwap) (pairSign_ne_smul h2) pairSwap_ne_smul
        pairSign_mul_pairSwap_ne_smul

end CFSG.LocalAnalysis.ComponentInitial
