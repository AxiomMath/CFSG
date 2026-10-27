module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] noncomputable def diagHom (n : ℕ) : (Fin n → Kˣ) →* GL (Fin n) K :=
  (Units.map (diagonalRingHom (Fin n) K).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagHom {n : ℕ} (d : Fin n → Kˣ) :
    ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => (d i : K) :=
  rfl

theorem diagHom_injective (n : ℕ) : Function.Injective (diagHom (K := K) n) := by
  intro d d' h
  funext i
  apply Units.ext
  have := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
    h) i) i
  simpa [coe_diagHom] using this

theorem det_diagHom {n : ℕ} (d : Fin n → Kˣ) :
    ((diagHom n d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ∏ i, (d i : K) := by
  rw [coe_diagHom, det_diagonal]

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def s01Mat : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; -1, 0, 0; 0, 0, -1]

@[expose] def s12Mat : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, 0, -1; 0, -1, 0]

@[expose] def s02Mat : Matrix (Fin 3) (Fin 3) K := !![0, 0, -1; 0, -1, 0; -1, 0, 0]

theorem cycMat_mul_transpose : cycMat (K := K) * cycMatᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycMat_transpose_mul : cycMatᵀ * cycMat (K := K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s01Mat_mul_self : s01Mat (K := K) * s01Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s01Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s12Mat_mul_self : s12Mat (K := K) * s12Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s12Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s02Mat_mul_self : s02Mat (K := K) * s02Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s02Mat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def cycGL : GL (Fin 3) K := ⟨cycMat, cycMatᵀ, cycMat_mul_transpose, cycMat_transpose_mul⟩

@[expose] def s01GL : GL (Fin 3) K := ⟨s01Mat, s01Mat, s01Mat_mul_self, s01Mat_mul_self⟩

@[expose] def s12GL : GL (Fin 3) K := ⟨s12Mat, s12Mat, s12Mat_mul_self, s12Mat_mul_self⟩

@[expose] def s02GL : GL (Fin 3) K := ⟨s02Mat, s02Mat, s02Mat_mul_self, s02Mat_mul_self⟩

theorem coe_cycGL : ((cycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycMat := rfl

theorem coe_cycGL_inv : ((cycGL⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycMatᵀ := rfl

theorem coe_s01GL : ((s01GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s01Mat := rfl

theorem coe_s12GL : ((s12GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s12Mat := rfl

theorem coe_s02GL : ((s02GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = s02Mat := rfl

theorem s01GL_sq : (s01GL : GL (Fin 3) K) ^ 2 = 1 := Units.ext (by
  rw [sq, Units.val_mul, coe_s01GL, s01Mat_mul_self, Units.val_one])

theorem s12GL_sq : (s12GL : GL (Fin 3) K) ^ 2 = 1 := Units.ext (by
  rw [sq, Units.val_mul, coe_s12GL, s12Mat_mul_self, Units.val_one])

theorem s02GL_sq : (s02GL : GL (Fin 3) K) ^ 2 = 1 := Units.ext (by
  rw [sq, Units.val_mul, coe_s02GL, s02Mat_mul_self, Units.val_one])

theorem s01GL_inv : (s01GL : GL (Fin 3) K)⁻¹ = s01GL :=
  inv_eq_of_mul_eq_one_left (by rw [← sq, s01GL_sq])

theorem s12GL_inv : (s12GL : GL (Fin 3) K)⁻¹ = s12GL :=
  inv_eq_of_mul_eq_one_left (by rw [← sq, s12GL_sq])

theorem s02GL_inv : (s02GL : GL (Fin 3) K)⁻¹ = s02GL :=
  inv_eq_of_mul_eq_one_left (by rw [← sq, s02GL_sq])

theorem cycGL_pow_three : (cycGL : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycGL, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [cycMat, pow_succ, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem cycGL_ne_one : (cycGL : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    h) 0) 0
  simp [coe_cycGL, cycMat] at this

theorem orderOf_cycGL : orderOf (cycGL : GL (Fin 3) K) = 3 :=
  orderOf_eq_prime cycGL_pow_three cycGL_ne_one

theorem s01GL_mul_s12GL : (s01GL : GL (Fin 3) K) * s12GL = cycGL := by
  apply Units.ext
  rw [Units.val_mul, coe_s01GL, coe_s12GL, coe_cycGL]
  ext i j; fin_cases i <;> fin_cases j <;> simp [s01Mat, s12Mat, cycMat, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem cycGL_conj_diagHom (d : Fin 3 → Kˣ) :
    cycGL * diagHom 3 d * cycGL⁻¹ = diagHom 3 ![d 2, d 0, d 1] := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_cycGL, coe_cycGL_inv, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, diagonal_apply]

theorem s01GL_conj_diagHom (d : Fin 3 → Kˣ) :
    s01GL * diagHom 3 d * s01GL⁻¹ = diagHom 3 ![d 1, d 0, d 2] := by
  apply Units.ext
  rw [s01GL_inv, Units.val_mul, Units.val_mul, coe_s01GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s01Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, diagonal_apply]

theorem s12GL_conj_diagHom (d : Fin 3 → Kˣ) :
    s12GL * diagHom 3 d * s12GL⁻¹ = diagHom 3 ![d 0, d 2, d 1] := by
  apply Units.ext
  rw [s12GL_inv, Units.val_mul, Units.val_mul, coe_s12GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s12Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, diagonal_apply]

theorem s02GL_conj_diagHom (d : Fin 3 → Kˣ) :
    s02GL * diagHom 3 d * s02GL⁻¹ = diagHom 3 ![d 2, d 1, d 0] := by
  apply Units.ext
  rw [s02GL_inv, Units.val_mul, Units.val_mul, coe_s02GL, coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s02Mat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, diagonal_apply]

structure MonomialData (H : Subgroup (GL (Fin 3) K)) (M : Subgroup Kˣ) : Prop where
  det_eq_one : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1
  diag_mem : ∀ d : Fin 3 → Kˣ, (∀ i, d i ∈ M) → d 0 * d 1 * d 2 = 1 → diagHom 3 d ∈ H
  cyc_mem : cycGL ∈ H
  s01_mem : s01GL ∈ H
  s12_mem : s12GL ∈ H
  s02_mem : s02GL ∈ H

theorem det_of_mem_statedSL {n : ℕ} {x : GL (Fin n) K} (hx : x ∈ StatedSL n K) :
    (x : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hx

theorem det_cycMat : (cycMat (K := K)).det = 1 := by simp [cycMat, det_fin_three]

theorem det_s01Mat : (s01Mat (K := K)).det = 1 := by simp [s01Mat, det_fin_three]

theorem det_s12Mat : (s12Mat (K := K)).det = 1 := by simp [s12Mat, det_fin_three]

theorem det_s02Mat : (s02Mat (K := K)).det = 1 := by simp [s02Mat, det_fin_three]

theorem det_diagHom_three (d : Fin 3 → Kˣ) :
    ((diagHom 3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = d 0 * d 1 * d 2 := by
  rw [det_diagHom, Fin.prod_univ_three]

theorem monomialData_statedSL : MonomialData (StatedSL 3 K) ⊤ where
  det_eq_one _ hx := det_of_mem_statedSL hx
  diag_mem d _ hd := Subgroup.subset_closure (by
    change ((diagHom 3 d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [det_diagHom_three, ← Units.val_mul, ← Units.val_mul, hd, Units.val_one])
  cyc_mem := Subgroup.subset_closure det_cycMat
  s01_mem := Subgroup.subset_closure det_s01Mat
  s12_mem := Subgroup.subset_closure det_s12Mat
  s02_mem := Subgroup.subset_closure det_s02Mat

@[expose] def normOne (K : Type) [Field K] (q : ℕ) : Subgroup Kˣ := (powMonoidHom (q + 1)).ker

theorem mem_normOne {q : ℕ} {c : Kˣ} : c ∈ normOne K q ↔ c ^ (q + 1) = 1 := Iff.rfl

section Unitary

variable {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem map_pow_signed {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) : A.map (· ^ (p ^ f)) = A := by
  ext i j
  have hq : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rcases hA i j with h | h | h <;> simp [Matrix.map_apply, h, zero_pow hq, neg_one_pow_char_pow]

theorem monomialData_statedSU : MonomialData (StatedSU 3 (p ^ f) K) (normOne K (p ^ f)) where
  det_eq_one _ hx := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx
  diag_mem d hdM hd := Subgroup.subset_closure ⟨by
      rw [det_diagHom_three, ← Units.val_mul, ← Units.val_mul, hd, Units.val_one], by
      rw [coe_diagHom, Matrix.diagonal_map (by simp [zero_pow (pow_ne_zero _
        (Fact.out : p.Prime).ne_zero)]), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      have h := mem_normOne.1 (hdM i)
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, h, Units.val_one]⟩
  cyc_mem := Subgroup.subset_closure ⟨det_cycMat, by
    rw [coe_cycGL, map_pow_signed (by intro i j; fin_cases i <;> fin_cases j <;> simp [cycMat]),
      cycMat_transpose_mul]⟩
  s01_mem := Subgroup.subset_closure ⟨det_s01Mat, by
    rw [coe_s01GL, map_pow_signed (by intro i j; fin_cases i <;> fin_cases j <;> simp [s01Mat])]
    have : (s01Mat (K := K))ᵀ = s01Mat := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this, s01Mat_mul_self]⟩
  s12_mem := Subgroup.subset_closure ⟨det_s12Mat, by
    rw [coe_s12GL, map_pow_signed (by intro i j; fin_cases i <;> fin_cases j <;> simp [s12Mat])]
    have : (s12Mat (K := K))ᵀ = s12Mat := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this, s12Mat_mul_self]⟩
  s02_mem := Subgroup.subset_closure ⟨det_s02Mat, by
    rw [coe_s02GL, map_pow_signed (by intro i j; fin_cases i <;> fin_cases j <;> simp [s02Mat])]
    have : (s02Mat (K := K))ᵀ = s02Mat := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [this, s02Mat_mul_self]⟩

end Unitary

section Torus

variable (M : Subgroup Kˣ)

@[expose] noncomputable def torusHom : M × M →* GL (Fin 3) K where
  toFun x := diagHom 3 ![(x.1 : Kˣ), (x.2 : Kˣ), ((x.1 : Kˣ) * x.2)⁻¹]
  map_one' := by
    rw [← map_one (diagHom (K := K) 3)]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem torusHom_apply (x : M × M) :
    torusHom M x = diagHom 3 ![(x.1 : Kˣ), (x.2 : Kˣ), ((x.1 : Kˣ) * x.2)⁻¹] :=
  rfl

theorem torusHom_injective : Function.Injective (torusHom (K := K) M) := by
  intro x y h
  have h' := diagHom_injective 3 h
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)

@[expose] noncomputable def torus3 : Subgroup (GL (Fin 3) K) := (torusHom M).range

theorem mem_torus3 {x : GL (Fin 3) K} :
    x ∈ torus3 M ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ M) ∧ d 0 * d 1 * d 2 = 1 ∧ x = diagHom 3 d := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨![(y.1 : Kˣ), (y.2 : Kˣ), ((y.1 : Kˣ) * y.2)⁻¹], fun i => ?_, by simp, rfl⟩
    fin_cases i
    · exact y.1.2
    · exact y.2.2
    · exact M.inv_mem (M.mul_mem y.1.2 y.2.2)
  · rintro ⟨d, hdM, hd, rfl⟩
    refine ⟨(⟨d 0, hdM 0⟩, ⟨d 1, hdM 1⟩), ?_⟩
    rw [torusHom_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · rfl
    · change ((d 0 * d 1)⁻¹ : Kˣ) = d 2
      rw [inv_eq_iff_mul_eq_one]
      exact hd

theorem card_torus3 [Finite K] : Nat.card (torus3 (K := K) M) = Nat.card M ^ 2 := by
  rw [torus3, ← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective M)).toEquiv,
    Nat.card_prod, sq]

theorem torus3_le {H : Subgroup (GL (Fin 3) K)} (hH : MonomialData H M) : torus3 M ≤ H := by
  intro x hx
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 hx
  exact hH.diag_mem d hdM hd

theorem torus3_comm {x y : GL (Fin 3) K} (hx : x ∈ torus3 M) (hy : y ∈ torus3 M) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem cycGL_conj_mem_torus3 {x : GL (Fin 3) K} (hx : x ∈ torus3 M) :
    cycGL * x * cycGL⁻¹ ∈ torus3 M := by
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 hx
  rw [cycGL_conj_diagHom]
  refine (mem_torus3 M).2 ⟨_, fun i => ?_, ?_, rfl⟩
  · fin_cases i <;> simp [hdM]
  · show d 2 * d 0 * d 1 = 1
    rw [← hd]
    ac_rfl

theorem cycGL_mem_normalizer_torus3 :
    cycGL ∈ Subgroup.normalizer (torus3 (K := K) M : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact cycGL_conj_mem_torus3 M
  · intro hx
    have h := cycGL_conj_mem_torus3 M (cycGL_conj_mem_torus3 M hx)
    rw [show cycGL * (cycGL * (cycGL * x * cycGL⁻¹) * cycGL⁻¹) * cycGL⁻¹ =
        (cycGL * cycGL * cycGL) * x * (cycGL * cycGL * cycGL)⁻¹ by group] at h
    have h3' : (cycGL : GL (Fin 3) K) * cycGL * cycGL = 1 := by
      calc (cycGL : GL (Fin 3) K) * cycGL * cycGL = cycGL ^ 3 := by rw [pow_three, mul_assoc]
        _ = 1 := cycGL_pow_three
    rw [h3', one_mul, inv_one, mul_one] at h
    exact h

theorem zpow_cycGL_mem_torus3 {k : ℤ} (hk : (cycGL : GL (Fin 3) K) ^ k ∈ torus3 M) :
    (cycGL : GL (Fin 3) K) ^ k = 1 := by
  have h3 : (cycGL : GL (Fin 3) K) ^ k = cycGL ^ ((k % 3).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    have h := zpow_mod_orderOf (cycGL : GL (Fin 3) K) k
    rw [orderOf_cycGL] at h
    exact h.symm
  rw [h3] at hk ⊢
  have hlt : (k % 3).toNat < 3 := by omega
  obtain ⟨d, -, -, hd⟩ := (mem_torus3 M).1 hk
  interval_cases h : (k % 3).toNat
  · rw [pow_zero]
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 1) 0
    simp [coe_cycGL, cycMat, coe_diagHom] at this
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 2) 0
    simp [coe_cycGL, cycMat, coe_diagHom, sq, Matrix.mul_apply, Fin.sum_univ_three] at this

end Torus

section Sup

variable {G : Type*} [Group G]

theorem exists_mul_pow_of_mem_sup_zpowers [Finite G] {L : Subgroup G} {δ : G}
    (hδ : δ ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L ⊔ Subgroup.zpowers δ) :
    ∃ l ∈ L, ∃ j < orderOf δ, x = l * δ ^ j := by
  have hnorm : Subgroup.zpowers δ ≤ Subgroup.normalizer (L : Set G) := by
    rwa [Subgroup.zpowers_le]
  have hpos : 0 < orderOf δ := orderOf_pos δ
  have hx' : x ∈ ((L ⊔ Subgroup.zpowers δ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hx'
  obtain ⟨l, hl, _, ⟨k, rfl⟩, hlk⟩ := hx'
  refine ⟨l, hl, (k % (orderOf δ : ℤ)).toNat, ?_, ?_⟩
  · have h1 : k % (orderOf δ : ℤ) < orderOf δ := Int.emod_lt_of_pos k (by exact_mod_cast hpos)
    omega
  · rw [← hlk]
    simp only
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by exact_mod_cast hpos.ne')),
      zpow_mod_orderOf]

theorem card_sup_zpowers_of_normalizer [Finite G] {L : Subgroup G} {δ : G}
    (hδ : δ ∈ Subgroup.normalizer (L : Set G)) (hdisj : ∀ k : ℤ, δ ^ k ∈ L → δ ^ k = 1) :
    Nat.card ↥(L ⊔ Subgroup.zpowers δ) = Nat.card L * orderOf δ := by
  let φ : L × Fin (orderOf δ) → ↥(L ⊔ Subgroup.zpowers δ) := fun x =>
    ⟨x.1 * δ ^ (x.2 : ℕ), Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers _ _))⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h : (x.1 : G) * δ ^ (x.2 : ℕ) = y.1 * δ ^ (y.2 : ℕ) := congrArg Subtype.val hxy
      have h' : δ ^ ((x.2 : ℕ) : ℤ) * (δ ^ ((y.2 : ℕ) : ℤ))⁻¹ = (x.1 : G)⁻¹ * y.1 := by
        rw [zpow_natCast, zpow_natCast]
        calc δ ^ (x.2 : ℕ) * (δ ^ (y.2 : ℕ))⁻¹
            = (x.1 : G)⁻¹ * (x.1 * δ ^ (x.2 : ℕ)) * (δ ^ (y.2 : ℕ))⁻¹ := by group
          _ = (x.1 : G)⁻¹ * y.1 := by rw [h]; group
      rw [← _root_.zpow_sub] at h'
      have h1 : δ ^ (((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ)) = 1 :=
        hdisj _ (by rw [h']; exact mul_mem (inv_mem x.1.2) y.1.2)
      have hdvd := (orderOf_dvd_iff_zpow_eq_one).2 h1
      have h2 : x.2 = y.2 := by
        have hx := x.2.isLt
        have hy := y.2.isLt
        obtain ⟨c, hc⟩ := hdvd
        apply Fin.ext
        have : c = 0 := by
          rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
          · nlinarith
          · exact hc0
          · nlinarith
        rw [this, mul_zero, sub_eq_zero] at hc
        exact_mod_cast hc
      rw [h2, mul_left_inj] at h
      exact Prod.ext (Subtype.ext h) h2
    · obtain ⟨l, hl, j, hj, hz⟩ := exists_mul_pow_of_mem_sup_zpowers hδ z.2
      exact ⟨(⟨l, hl⟩, ⟨j, hj⟩), Subtype.ext hz.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_fin]

end Sup

theorem card_torus3_sup_cyc [Finite K] (M : Subgroup Kˣ) :
    Nat.card ↥(torus3 M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)) = 3 * Nat.card M ^ 2 := by
  rw [card_sup_zpowers_of_normalizer (cycGL_mem_normalizer_torus3 M)
    (fun k hk => zpow_cycGL_mem_torus3 M hk), card_torus3, orderOf_cycGL, mul_comm]

theorem exists_mem_torus3_mul_cyc [Finite K] (M : Subgroup Kˣ) {x : GL (Fin 3) K}
    (hx : x ∈ torus3 M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)) :
    ∃ t ∈ torus3 M, ∃ j < 3, x = t * cycGL ^ j := by
  have := exists_mul_pow_of_mem_sup_zpowers (cycGL_mem_normalizer_torus3 M) hx
  rwa [orderOf_cycGL] at this

theorem card_statedSL_three [Finite K] :
    Nat.card (StatedSL 3 K) =
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) :=
  (CFSG.Open.StatedAPI.card_statedSL_three K).trans (mul_assoc _ _ _).symm

theorem card_statedSU_three [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedSU 3 (p ^ f) K) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [← Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU hK 3).toEquiv,
    CFSG.LieType.Steinberg.card_SU_three hK]

theorem card_units_eq [Finite K] : Nat.card Kˣ = Nat.card K - 1 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]

theorem card_normOne [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card (normOne K q) = q + 1 := by
  rw [normOne, IsCyclic.card_powMonoidHom_ker, card_units_eq, hK]
  have hq : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · have := Finite.one_lt_card (α := K)
      rw [hK, h] at this
      simp at this
    · exact h
  have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq, Nat.one_le_pow 2 q hq]
    ring
  rw [this, Nat.gcd_mul_right_left]

section Arith

theorem factorization_order_eq {q e e' m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hq : q ≠ 0)
    (he : e ≠ 0) (he' : e' ≠ 0) (hm : m ≠ 0) (hrq : ¬ r ∣ q) (hre' : ¬ r ∣ e')
    (hmr : m.factorization r = (3 : ℕ).factorization r) :
    (q ^ 3 * (e * e') * (e * m)).factorization r = (6 * e ^ 2).factorization r := by
  have h2 : (2 : ℕ).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity), Nat.factorization_pow,
    Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_eq_zero_of_not_dvd hrq, Nat.factorization_eq_zero_of_not_dvd hre', hmr,
    h2]
  ring

theorem factorization_sq_add_add_one {q r : ℕ} (hr : r.Prime) (hq : 1 ≤ q) (hrq : r ∣ q - 1) :
    (q ^ 2 + q + 1).factorization r = (3 : ℕ).factorization r := by
  by_cases hr3 : r = 3
  · subst hr3
    rw [Nat.Prime.factorization_self Nat.prime_three]
    have hmod : (q ^ 2 + q + 1) % 9 = 3 := by
      have h3 : q % 3 = 1 := by omega
      have h9 : q % 9 = 1 ∨ q % 9 = 4 ∨ q % 9 = 7 := by omega
      have : (q ^ 2 + q + 1) % 9 = ((q % 9) ^ 2 + q % 9 + 1) % 9 := by
        simp [Nat.add_mod, Nat.pow_mod]
      rcases h9 with h | h | h <;> rw [this, h] <;> norm_num
    have hd : 3 ^ 1 ∣ q ^ 2 + q + 1 := by omega
    have hnd : ¬ 3 ^ 2 ∣ q ^ 2 + q + 1 := by omega
    have hne : q ^ 2 + q + 1 ≠ 0 := by omega
    have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hne).1 hd
    have h2 : ¬ 2 ≤ (q ^ 2 + q + 1).factorization 3 := fun h =>
      hnd ((Nat.prime_three.pow_dvd_iff_le_factorization hne).2 h)
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hr3
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h))]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have hq1 : (q : ZMod r) = 1 := by
      have := (ZMod.natCast_eq_zero_iff (q - 1) r).2 hrq
      rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
      exact this
    have h0 := (ZMod.natCast_eq_zero_iff _ r).2 hdvd
    push_cast at h0
    rw [hq1] at h0
    have h3 : ((3 : ℕ) : ZMod r) = 0 := by rw [← h0]; push_cast; ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3)

theorem factorization_sq_sub_add_one {q r : ℕ} (hr : r.Prime) (hrq : r ∣ q + 1) :
    (q ^ 2 - q + 1).factorization r = (3 : ℕ).factorization r := by
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  by_cases hr3 : r = 3
  · subst hr3
    rw [Nat.Prime.factorization_self Nat.prime_three]
    have hmod : (q ^ 2 - q + 1) % 9 = 3 := by
      have h3 : q % 3 = 2 := by omega
      have h9 : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
      obtain ⟨t, ht⟩ : ∃ t, q = 9 * t + q % 9 := ⟨q / 9, (Nat.div_add_mod q 9).symm⟩
      rcases h9 with h | h | h <;> rw [h] at ht <;> subst ht <;> ring_nf <;> omega
    have hd : 3 ^ 1 ∣ q ^ 2 - q + 1 := by omega
    have hnd : ¬ 3 ^ 2 ∣ q ^ 2 - q + 1 := by omega
    have hne : q ^ 2 - q + 1 ≠ 0 := by omega
    have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hne).1 hd
    have h2 : ¬ 2 ≤ (q ^ 2 - q + 1).factorization 3 := fun h =>
      hnd ((Nat.prime_three.pow_dvd_iff_le_factorization hne).2 h)
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hr3
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h))]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have hq1 : (q : ZMod r) = -1 := by
      have := (ZMod.natCast_eq_zero_iff (q + 1) r).2 hrq
      push_cast at this
      linear_combination this
    have h0 := (ZMod.natCast_eq_zero_iff _ r).2 hdvd
    rw [Nat.cast_add, Nat.cast_sub hqq] at h0
    push_cast at h0
    rw [hq1] at h0
    have h3 : ((3 : ℕ) : ZMod r) = 0 := by rw [← h0]; push_cast; ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3)

end Arith

end CFSG.SectionRank.OddCover
