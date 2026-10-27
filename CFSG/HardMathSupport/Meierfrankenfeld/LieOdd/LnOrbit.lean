module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnDual
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped LinearAlgebra.Projectivization
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {K : Type} [Field K] {m : ℕ}

@[expose] def colV (c : Fin m → K) : Fin (m + 1) → K := Fin.cons 0 c

@[expose] def xMat (c : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  1 + Matrix.vecMulVec (colV c) (Pi.single 0 1)

theorem xMat_det (c : Fin m → K) : (xMat c).det = 1 := by
  rw [xMat, Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [colV]

theorem xMat_add (c d : Fin m → K) : xMat (c + d) = xMat c * xMat d := by
  have h0 : (Pi.single (0 : Fin (m + 1)) (1 : K) : Fin (m + 1) → K) ⬝ᵥ colV d = 0 := by
    simp [colV, single_dotProduct]
  have : xMat c * xMat d = 1 + Matrix.vecMulVec (colV c) (Pi.single 0 1) +
      Matrix.vecMulVec (colV d) (Pi.single 0 1) := by
    simp only [xMat, add_mul, mul_add, one_mul, mul_one, Matrix.vecMulVec_mul_vecMulVec, h0,
      zero_smul, Matrix.vecMulVec_zero]
    abel
  rw [this, xMat]
  have : colV (c + d) = colV c + colV d := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [colV]
  rw [this, Matrix.add_vecMulVec]
  abel

theorem xMat_zero : xMat (0 : Fin m → K) = 1 := by
  have : colV (0 : Fin m → K) = 0 := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [colV]
  simp [xMat, this]

@[expose] def lvMat (A : Matrix (Fin m) (Fin m) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

theorem lvMat_det (A : Matrix (Fin m) (Fin m) K) : (lvMat A).det = A.det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp only [lvMat, Matrix.of_apply, Fin.cases_zero, Fin.val_zero, pow_zero, one_mul]
    rw [Fin.succAbove_zero]
    congr 1
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
    simp [lvMat]
  · simp

theorem lvMat_mul (A B : Matrix (Fin m) (Fin m) K) : lvMat (A * B) = lvMat A * lvMat B := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [lvMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem lvMat_one : lvMat (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [lvMat, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem lvMat_mul_xMat (A : Matrix (Fin m) (Fin m) K) (c : Fin m → K) :
    lvMat A * xMat c = xMat (A *ᵥ c) * lvMat A := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [lvMat, xMat, colV, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMulVec_apply,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, Fin.succ_ne_zero,
      (Fin.succ_ne_zero _).symm]

@[expose] def xSL (c : Fin m → K) : Matrix.SpecialLinearGroup (Fin (m + 1)) K :=
  ⟨xMat c, xMat_det c⟩

theorem coe_xSL (c : Fin m → K) : ((xSL c : Matrix.SpecialLinearGroup (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) = xMat c := rfl

@[expose] def xHom : Multiplicative (Fin m → K) →* Matrix.SpecialLinearGroup (Fin (m + 1)) K where
  toFun c := xSL c.toAdd
  map_one' := Subtype.ext (by rw [coe_xSL, toAdd_one, xMat_zero]; rfl)
  map_mul' a b := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_xSL, coe_xSL, coe_xSL, toAdd_mul, xMat_add])

@[expose] def lvSL (A : Matrix.SpecialLinearGroup (Fin m) K) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) K :=
  ⟨lvMat A, by rw [lvMat_det, A.2]⟩

theorem coe_lvSL (A : Matrix.SpecialLinearGroup (Fin m) K) :
    ((lvSL A : Matrix.SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = lvMat A := rfl

@[expose] def lvHom :
    Matrix.SpecialLinearGroup (Fin m) K →* Matrix.SpecialLinearGroup (Fin (m + 1)) K where
  toFun := lvSL
  map_one' := Subtype.ext (by rw [coe_lvSL, Matrix.SpecialLinearGroup.coe_one, lvMat_one]; rfl)
  map_mul' A B := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_lvSL, coe_lvSL, coe_lvSL,
      Matrix.SpecialLinearGroup.coe_mul, lvMat_mul])

theorem lvSL_mul_xSL (A : Matrix.SpecialLinearGroup (Fin m) K) (c : Fin m → K) :
    lvHom A * xSL c = xSL ((A : Matrix (Fin m) (Fin m) K) *ᵥ c) * lvHom A :=
  Subtype.ext (lvMat_mul_xMat _ _)

@[expose] noncomputable def uHom :
    Multiplicative (Fin m → K) →* LinearFlag.projectiveSL (m + 1) K :=
  (LinearFlag.proj (m + 1) K).comp xHom

@[expose] noncomputable def tHom :
    Matrix.SpecialLinearGroup (Fin m) K →* LinearFlag.projectiveSL (m + 1) K :=
  (LinearFlag.proj (m + 1) K).comp lvHom

theorem tHom_conj_uHom (A : Matrix.SpecialLinearGroup (Fin m) K) (c : Multiplicative (Fin m → K)) :
    tHom A * uHom c * (tHom A)⁻¹ =
      uHom (Multiplicative.ofAdd ((A : Matrix (Fin m) (Fin m) K) *ᵥ c.toAdd)) := by
  rw [mul_inv_eq_iff_eq_mul]
  show LinearFlag.proj (m + 1) K (lvHom A) * LinearFlag.proj (m + 1) K (xSL c.toAdd) =
    LinearFlag.proj (m + 1) K (xSL _) * LinearFlag.proj (m + 1) K (lvHom A)
  rw [← map_mul, ← map_mul, lvSL_mul_xSL, toAdd_ofAdd]

theorem uHom_injective : Function.Injective (uHom (K := K) (m := m)) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h1 : xSL c.toAdd ∈ LinearFlag.scalars (m + 1) K := by
    have : LinearFlag.proj (m + 1) K (xSL c.toAdd) = 1 := hc
    exact LinearFlag.proj_eq_one_iff.1 this
  obtain ⟨r, -, hr⟩ := LinearFlag.mem_scalars.1 h1
  have hx : ∀ i : Fin m, c.toAdd i = 0 := by
    intro i
    have := congrFun (congrFun hr i.succ) 0
    simpa [xSL, xMat, colV, Matrix.vecMulVec_apply, Matrix.scalar_apply, Fin.succ_ne_zero] using this
  apply Multiplicative.toAdd.injective
  funext i
  exact hx i

section Transitivity

theorem diagSL_exists {m : ℕ} (hm : 2 ≤ m) (c : K) (hc : c ≠ 0) :
    ∃ d : Matrix.SpecialLinearGroup (Fin m) K,
      (d : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1) = Pi.single ⟨0, by omega⟩ c := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let f : Fin m → K := fun i => if i = i0 then c else if i = i1 then c⁻¹ else 1
  refine ⟨⟨Matrix.diagonal f, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal, Fintype.prod_eq_mul i0 i1 h01 (fun x hx => by
      simp [f, hx.1, hx.2])]
    simp [f, h01, h01.symm, hc]
  · ext j
    simp only [Matrix.mulVec_diagonal, f, Pi.single_apply]
    by_cases hj : j = i0 <;> simp [hj, i0]

theorem exists_SL_mulVec_eq_single {m : ℕ} (hm : 2 ≤ m)
    {x : Fin m → K} (hx : x ≠ 0) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin m) K) (a : K), a ≠ 0 ∧
      (g : Matrix (Fin m) (Fin m) K) *ᵥ x = Pi.single ⟨0, by omega⟩ a := by
  classical
  have he : (Pi.single (⟨0, by omega⟩ : Fin m) (1 : K) : Fin m → K) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin m) K)
    (Projectivization.mk K x hx) (Projectivization.mk K _ he)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  have hc' : (g : Matrix (Fin m) (Fin m) K) *ᵥ x = (c : K) • Pi.single (⟨0, by omega⟩ : Fin m) (1 : K) := by
    have : (g : Matrix (Fin m) (Fin m) K) *ᵥ x = c • Pi.single (⟨0, by omega⟩ : Fin m) (1 : K) := hc.symm
    rw [this, Units.smul_def]
  refine ⟨g, (c : K), c.ne_zero, ?_⟩
  rw [hc']
  ext j
  by_cases hj : j = ⟨0, by omega⟩ <;> simp [Pi.single_apply, hj]

theorem exists_SL_mulVec_eq {m : ℕ} (hm : 2 ≤ m)
    {x y : Fin m → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin m) K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = y := by
  obtain ⟨g₁, a, ha, h₁⟩ := exists_SL_mulVec_eq_single hm hx
  obtain ⟨g₂, b, hb, h₂⟩ := exists_SL_mulVec_eq_single hm hy
  obtain ⟨d, hd⟩ := diagSL_exists hm (b / a) (div_ne_zero hb ha)
  refine ⟨g₂⁻¹ * d * g₁, ?_⟩
  have hd' : (d : Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ a) =
      Pi.single ⟨0, by omega⟩ b := by
    have : (Pi.single (⟨0, by omega⟩ : Fin m) a : Fin m → K) = a • Pi.single ⟨0, by omega⟩ 1 := by
      ext j; by_cases hj : j = ⟨0, by omega⟩ <;> simp [Pi.single_apply, hj]
    rw [this, Matrix.mulVec_smul, hd]
    ext j
    by_cases hj : j = ⟨0, by omega⟩ <;> simp [Pi.single_apply, hj, ha]
    · field_simp
  have hy' : (g₂ : Matrix (Fin m) (Fin m) K) *ᵥ y = Pi.single ⟨0, by omega⟩ b := h₂
  have e : ((g₂⁻¹ * d * g₁ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x =
      ((g₂⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        ((d : Matrix (Fin m) (Fin m) K) *ᵥ ((g₁ : Matrix (Fin m) (Fin m) K) *ᵥ x)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, h₁, hd', ← hy', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

end Transitivity

section Hyperplanes

variable {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] [Finite K] (τ : K →ₗ[ZMod p] ZMod p)

@[expose] def addOfMulGen {A : Type*} [AddCommGroup A] (D : Subgroup (Multiplicative A)) :
    AddSubgroup A where
  carrier := {x | Multiplicative.ofAdd x ∈ D}
  add_mem' ha hb := D.mul_mem ha hb
  zero_mem' := D.one_mem
  neg_mem' ha := D.inv_mem ha

theorem index_addOfMulGen {A : Type*} [AddCommGroup A] [Finite A]
    (D : Subgroup (Multiplicative A)) : (addOfMulGen D).index = D.index := by
  have h1 : Nat.card (addOfMulGen D) * (addOfMulGen D).index = Nat.card A :=
    AddSubgroup.card_mul_index _
  have h2 : Nat.card D * D.index = Nat.card (Multiplicative A) := Subgroup.card_mul_index D
  have h3 : Nat.card (addOfMulGen D) = Nat.card D := Nat.card_congr (Equiv.refl _)
  have h4 : Nat.card (Multiplicative A) = Nat.card A := Nat.card_congr Multiplicative.toAdd
  have hpos : 0 < Nat.card D := Nat.card_pos
  rw [h3, ← h4, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

@[expose] def kerSub (w : Fin m → K) : Subgroup (Multiplicative (Fin m → K)) where
  carrier := {c | dualForm τ w c.toAdd = 0}
  mul_mem' {a b} ha hb := by
    show dualForm τ w (a * b).toAdd = 0
    rw [toAdd_mul, map_add, ha, hb, add_zero]
  one_mem' := by
    show dualForm τ w (1 : Multiplicative (Fin m → K)).toAdd = 0
    rw [toAdd_one, map_zero]
  inv_mem' {a} ha := by
    show dualForm τ w (a⁻¹).toAdd = 0
    rw [toAdd_inv, map_neg, ha]
    exact neg_zero

@[expose] noncomputable def hypSub (w : Fin m → K) : Subgroup (LinearFlag.projectiveSL (m + 1) K) :=
  (kerSub τ w).map uHom

theorem mem_hypSub {w : Fin m → K} {y : LinearFlag.projectiveSL (m + 1) K} :
    y ∈ hypSub τ w ↔ ∃ c : Multiplicative (Fin m → K), dualForm τ w c.toAdd = 0 ∧ uHom c = y := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem dualForm_vecMul (w : Fin m → K) (M : Matrix (Fin m) (Fin m) K) (d : Fin m → K) :
    dualForm τ (w ᵥ* M) d = dualForm τ w (M *ᵥ d) := by
  rw [dualForm_apply, dualForm_apply, dotProduct_mulVec]

theorem conjSub_tHom_hypSub (A : Matrix.SpecialLinearGroup (Fin m) K) (w : Fin m → K) :
    conjSub (tHom A) (hypSub τ w) =
      hypSub τ (w ᵥ* ((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  ext y
  rw [mem_conjSub, mem_hypSub, mem_hypSub]
  constructor
  · rintro ⟨c, hc, hcy⟩
    refine ⟨Multiplicative.ofAdd ((A : Matrix (Fin m) (Fin m) K) *ᵥ c.toAdd), ?_, ?_⟩
    · rw [toAdd_ofAdd, dualForm_vecMul, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      exact hc
    · rw [← tHom_conj_uHom, hcy]
      group
  · rintro ⟨d, hd, hdy⟩
    refine ⟨Multiplicative.ofAdd (((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) *ᵥ d.toAdd), ?_, ?_⟩
    · rw [toAdd_ofAdd]
      rw [dualForm_vecMul] at hd
      exact hd
    · have := tHom_conj_uHom A⁻¹ d
      rw [map_inv, inv_inv] at this
      rw [← this, hdy]

end Hyperplanes

section Orbit

variable {G : Type*} [Group G] [Finite G]

theorem conjSub_mul (a b : G) (D : Subgroup G) :
    conjSub (a * b) D = conjSub a (conjSub b D) := by
  ext x
  simp only [mem_conjSub]
  rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

theorem conjSub_eq_of_mem_normalizer {g : G} {D : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) : conjSub g D = D := by
  ext x
  rw [mem_conjSub]
  have := Subgroup.mem_set_normalizer_iff.1 hg (g⁻¹ * x * g)
  rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  exact this

theorem card_le_relIndex_of_conj {T D₀ : Subgroup G} {𝓢 : Finset (Subgroup G)}
    (h : ∀ D ∈ 𝓢, ∃ t ∈ T, conjSub t D₀ = D) :
    𝓢.card ≤ (T ⊓ Subgroup.normalizer (D₀ : Set G)).relIndex T := by
  classical
  choose! t ht hD using h
  let H' : Subgroup ↥T := (T ⊓ Subgroup.normalizer (D₀ : Set G)).subgroupOf T
  let F : 𝓢 → (↥T ⧸ H') := fun D => QuotientGroup.mk ⟨t D, ht D D.2⟩
  have hF : Function.Injective F := by
    intro D E hDE
    have h1 := QuotientGroup.eq.1 hDE
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (t D)⁻¹ * t E ∈ Subgroup.normalizer (D₀ : Set G) := (Subgroup.mem_inf.1 h1).2
    have h3 : conjSub (t E) D₀ = conjSub (t D) D₀ := by
      have : t E = t D * ((t D)⁻¹ * t E) := by group
      rw [this, conjSub_mul, conjSub_eq_of_mem_normalizer h2]
    apply Subtype.ext
    rw [← hD D D.2, ← hD E E.2, h3]
  calc 𝓢.card = Nat.card 𝓢 := by simp
    _ ≤ Nat.card (↥T ⧸ H') := Nat.card_le_card_of_injective F hF
    _ = _ := by rw [Subgroup.relIndex, Subgroup.index_eq_card]

end Orbit

section OrbitBound

variable {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] [Finite K] {τ : K →ₗ[ZMod p] ZMod p}

theorem orbit_bound (hm : 2 ≤ m) (hτ : τ ≠ 0)
    {D₀ : Subgroup (LinearFlag.projectiveSL (m + 1) K)}
    (hD₀ : D₀ ≤ (uHom (K := K) (m := m)).range)
    (hrel : D₀.relIndex (uHom (K := K) (m := m)).range = p) :
    (Nat.card K ^ m - 1) / (p - 1) ≤
      ((tHom (K := K) (m := m)).range ⊓ Subgroup.normalizer (D₀ : Set _)).relIndex
        (tHom (K := K) (m := m)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hfinS : Finite (LinearFlag.projectiveSL (m + 1) K) := inferInstance
  obtain ⟨D'', hDD⟩ : ∃ D'' : Subgroup (Multiplicative (Fin m → K)), D''.map uHom = D₀ :=
    ⟨D₀.comap uHom, Subgroup.map_comap_eq_self hD₀⟩
  have hidx : D''.index = p := by
    rw [← Subgroup.relIndex_top_right,
      ← Subgroup.relIndex_map_map_of_injective D'' ⊤ uHom_injective, hDD,
      ← MonoidHom.range_eq_map]
    exact hrel
  have hD'idx : (addOfMulGen D'').index = p := (index_addOfMulGen D'').trans hidx
  obtain ⟨w₀, hw₀, hform⟩ := exists_hyperplane_form hτ (addOfMulGen D'') hD'idx
  have hD'' : D'' = kerSub τ w₀ := by
    ext c
    exact hform c.toAdd
  have hD₀eq : D₀ = hypSub τ w₀ := by rw [← hDD, hD'']; rfl
  let 𝓦 : Finset (Fin m → K) := Finset.univ.filter (· ≠ 0)
  let 𝓢 : Finset (Subgroup (LinearFlag.projectiveSL (m + 1) K)) := 𝓦.image (hypSub τ)
  have hconj : ∀ D ∈ 𝓢, ∃ t ∈ (tHom (K := K) (m := m)).range, conjSub t D₀ = D := by
    intro D hD
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hD
    have hw0 : w ≠ 0 := (Finset.mem_filter.1 hw).2
    obtain ⟨g, hg⟩ := exists_SL_mulVec_eq hm hw₀ hw0
    refine ⟨tHom (g.transpose)⁻¹, ⟨_, rfl⟩, ?_⟩
    rw [hD₀eq, conjSub_tHom_hypSub, inv_inv]
    congr 1
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.vecMul_transpose, hg]
  refine le_trans ?_ (card_le_relIndex_of_conj hconj)
  have hfiber : ∀ a ∈ 𝓦.image (hypSub τ), (𝓦.filter (fun w => hypSub τ w = a)).card ≤ p - 1 := by
    intro a ha
    obtain ⟨w₁, hw₁, rfl⟩ := Finset.mem_image.1 ha
    have hw₁0 : w₁ ≠ 0 := (Finset.mem_filter.1 hw₁).2
    have h1 := card_fiber_le (τ := τ) (m := m) hτ hw₁0
    rw [Nat.card_zmod] at h1
    refine le_trans (Finset.card_le_card ?_) h1
    intro w hw
    obtain ⟨hw𝓦, hweq⟩ := Finset.mem_filter.1 hw
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hw𝓦).2, fun c => ?_⟩
    have hker : kerSub τ w₁ = kerSub τ w :=
      (Subgroup.map_injective (uHom_injective (K := K) (m := m)) hweq).symm
    exact SetLike.ext_iff.1 hker (Multiplicative.ofAdd c)
  have hs := Finset.card_le_mul_card_image 𝓦 (p - 1) hfiber
  have hW : 𝓦.card = Nat.card K ^ m - 1 := by
    have : 𝓦 = Finset.univ.erase 0 := Finset.filter_ne' _ _
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, ← Nat.card_eq_fintype_card]
  exact Nat.div_le_of_le_mul (by rw [← hW]; exact hs)

end OrbitBound

section Radical

theorem uHom_range_comm (a : LinearFlag.projectiveSL (m + 1) K) (ha : a ∈ (uHom (K := K) (m := m)).range)
    (b : LinearFlag.projectiveSL (m + 1) K) (hb : b ∈ (uHom (K := K) (m := m)).range) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem uHom_range_pow {p : ℕ} [CharP K p] (a : LinearFlag.projectiveSL (m + 1) K)
    (ha : a ∈ (uHom (K := K) (m := m)).range) : a ^ p = 1 := by
  obtain ⟨c, rfl⟩ := ha
  rw [← map_pow]
  have : c ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero, zero_smul]
  rw [this, map_one]

theorem uHom_range_ne_bot (hm : 1 ≤ m) : (uHom (K := K) (m := m)).range ≠ ⊥ := by
  intro h
  let c : Multiplicative (Fin m → K) := Multiplicative.ofAdd (Pi.single ⟨0, hm⟩ 1)
  have hc : uHom c ∈ (uHom (K := K) (m := m)).range := ⟨c, rfl⟩
  rw [h, Subgroup.mem_bot, ← map_one uHom] at hc
  have := uHom_injective hc
  have h2 := congrFun (Multiplicative.toAdd.injective (this : c = 1)) ⟨0, hm⟩
  simp [c] at h2

theorem tHom_range_le_normalizer :
    (tHom (K := K) (m := m)).range ≤
      Subgroup.normalizer ((uHom (K := K) (m := m)).range : Set (LinearFlag.projectiveSL (m + 1) K)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (tHom_conj_uHom A c).symm⟩
  · rintro ⟨d, hd⟩
    have h1 := tHom_conj_uHom A⁻¹ d
    rw [map_inv, inv_inv] at h1
    refine ⟨Multiplicative.ofAdd (((A⁻¹ : Matrix.SpecialLinearGroup (Fin m) K) :
      Matrix (Fin m) (Fin m) K) *ᵥ d.toAdd), ?_⟩
    rw [← h1, hd]
    group

end Radical

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
