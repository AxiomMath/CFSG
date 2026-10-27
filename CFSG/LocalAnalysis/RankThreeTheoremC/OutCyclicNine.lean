module

public import CFSG.Assembly.LowTwoRankDefs

open scoped Matrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem exists_isElemAbelian_card_nine_of_commute {H : Type*} [Group H] (x y : H)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : Commute x y)
    (hind : ∀ a b : ℕ, x ^ a * y ^ b = 1 → 3 ∣ a ∧ 3 ∣ b) :
    ∃ A : Subgroup H, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  let f : Multiplicative (ZMod 3 × ZMod 3) → H := fun s =>
    x ^ (Multiplicative.toAdd s).1.val * y ^ (Multiplicative.toAdd s).2.val
  have hf : ∀ s t, f (s * t) = f s * f t := by
    intro s t
    simp only [f, toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, pow_add, pow_add]
    generalize (Multiplicative.toAdd s).1.val = a
    generalize (Multiplicative.toAdd s).2.val = b
    generalize (Multiplicative.toAdd t).1.val = c
    generalize (Multiplicative.toAdd t).2.val = d
    have hcm : x ^ c * y ^ b = y ^ b * x ^ c := (hxy.pow_pow c b).eq
    calc x ^ a * x ^ c * (y ^ b * y ^ d) = x ^ a * (x ^ c * y ^ b) * y ^ d := by
          simp only [mul_assoc]
      _ = x ^ a * (y ^ b * x ^ c) * y ^ d := by rw [hcm]
      _ = x ^ a * y ^ b * (x ^ c * y ^ d) := by simp only [mul_assoc]
  let φ : Multiplicative (ZMod 3 × ZMod 3) →* H := MonoidHom.mk' f hf
  have hφ : ∀ s, φ s = x ^ (Multiplicative.toAdd s).1.val * y ^ (Multiplicative.toAdd s).2.val :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h : x ^ (Multiplicative.toAdd s).1.val * y ^ (Multiplicative.toAdd s).2.val = 1 := by
      rw [← hφ]
      exact hs
    obtain ⟨h1, h2⟩ := hind _ _ h
    have h1' : (Multiplicative.toAdd s).1 = 0 := by
      rw [← ZMod.val_eq_zero]
      have := ZMod.val_lt (Multiplicative.toAdd s).1
      omega
    have h2' : (Multiplicative.toAdd s).2 = 0 := by
      rw [← ZMod.val_eq_zero]
      have := ZMod.val_lt (Multiplicative.toAdd s).2
      omega
    apply Multiplicative.toAdd.injective
    exact Prod.ext h1' h2'
  refine ⟨φ.range, ⟨IsMulCommutative.of_comm ?_, ?_⟩, ?_⟩
  · rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
    apply Subtype.ext
    change φ s * φ t = φ t * φ s
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨s, rfl⟩
    rw [hφ, (hxy.pow_pow _ _).mul_pow, pow_right_comm x _ 3, hx, one_pow,
      pow_right_comm y _ 3, hy, one_pow, one_mul]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3 × ZMod 3) ≃ ZMod 3 × ZMod 3),
      Nat.card_prod, Nat.card_zmod]
    norm_num

theorem exists_isElemAbelian_card_nine_quotient {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal]
    (X Y : G) (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1) (hc : X * Y * X⁻¹ * Y⁻¹ ∈ Z)
    (hind : ∀ a b : ℕ, X ^ a * Y ^ b ∈ Z → 3 ∣ a ∧ 3 ∣ b) :
    ∃ A : Subgroup (G ⧸ Z), CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  refine exists_isElemAbelian_card_nine_of_commute (X : G ⧸ Z) (Y : G ⧸ Z) ?_ ?_ ?_ ?_
  · rw [← QuotientGroup.mk_pow, hX, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, hY, QuotientGroup.mk_one]
  · have h := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
  · intro a b h
    apply hind
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_pow]
    exact h

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)

theorem exists_nine_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (H : Subgroup (GL ι F)) (X Y : GL ι F) (hXH : X ∈ H) (hYH : Y ∈ H) (hX : X ^ 3 = 1)
    (hY : Y ^ 3 = 1) (hc : X * Y * X⁻¹ * Y⁻¹ ∈ StatedScalars ι F)
    (hind : ∀ a b : ℕ, X ^ a * Y ^ b ∈ StatedScalars ι F → 3 ∣ a ∧ 3 ∣ b) :
    ∃ A : Subgroup (StatedProj H), CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  refine exists_isElemAbelian_card_nine_quotient (StatedScalars ι F |>.subgroupOf H)
    (⟨X, hXH⟩ : H) ⟨Y, hYH⟩ (Subtype.ext (by simpa using hX)) (Subtype.ext (by simpa using hY))
    (Subgroup.mem_subgroupOf.mpr (by simpa using hc)) ?_
  intro a b hab
  have := Subgroup.mem_subgroupOf.mp hab
  exact hind a b (by simpa using this)

theorem exists_isElemAbelian_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {m : ℕ}
    (h : ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = m) :
    ∃ A : Subgroup G', CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = m := by
  obtain ⟨A, ⟨hc, hp⟩, hcard⟩ := h
  refine ⟨A.map e.toMonoidHom, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    change e a * e b = e b * e a
    rw [← map_mul, ← map_mul]
    exact congrArg e (congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hp a ha, map_one]
  · rw [← hcard]
    exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

namespace NineSubgroup

variable {F : Type} [Field F]

@[expose] noncomputable def dglHom (n : ℕ) : (Fin n → Fˣ) →* GL (Fin n) F where
  toFun d := ⟨Matrix.diagonal fun i => (d i : F), Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F),
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Matrix.diagonal_one]⟩
  map_one' := by
    refine Units.ext ?_
    simp [Matrix.diagonal_one]
  map_mul' a b := by
    refine Units.ext ?_
    simp [Matrix.diagonal_mul_diagonal]

theorem coe_dglHom (n : ℕ) (d : Fin n → Fˣ) :
    ((dglHom n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (d i : F) := rfl

def d1 (n : ℕ) (ζ : Fˣ) : Fin n → Fˣ := fun i =>
  if i.val = 0 then ζ else if i.val = 1 then ζ⁻¹ else 1

def d2 (n : ℕ) (ζ : Fˣ) : Fin n → Fˣ := fun i =>
  if i.val = 2 then ζ else if i.val = 3 then ζ⁻¹ else 1

theorem d1_pow_three (n : ℕ) {ζ : Fˣ} (h : ζ ^ 3 = 1) : (d1 n ζ) ^ 3 = 1 := by
  funext i
  simp only [d1, Pi.pow_apply, Pi.one_apply]
  split_ifs <;> simp [inv_pow, h]

theorem d2_pow_three (n : ℕ) {ζ : Fˣ} (h : ζ ^ 3 = 1) : (d2 n ζ) ^ 3 = 1 := by
  funext i
  simp only [d2, Pi.pow_apply, Pi.one_apply]
  split_ifs <;> simp [inv_pow, h]

theorem dglHom_mem_scalars_iff {n : ℕ} (d : Fin n → Fˣ) :
    dglHom n d ∈ StatedScalars (Fin n) F ↔ ∃ c : Fˣ, ∀ i, d i = c := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => ?_⟩
    have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i i) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h
    exact Units.ext h.symm
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext ?_⟩
    simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, Matrix.scalar_apply]
    congr 1
    funext i
    rw [hc i]

theorem torus_comm {n : ℕ} (a b : Fin n → Fˣ) :
    (dglHom n a : GL (Fin n) F) * dglHom n b * (dglHom n a)⁻¹ * (dglHom n b)⁻¹ = 1 := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  have : a * b * a⁻¹ * b⁻¹ = 1 := by
    funext i
    simp
  rw [this, map_one]

theorem d1_apply_zero (n : ℕ) (hn : 0 < n) (ζ : Fˣ) : d1 n ζ ⟨0, hn⟩ = ζ := by simp [d1]

theorem d1_apply_two (n : ℕ) (hn : 2 < n) (ζ : Fˣ) : d1 n ζ ⟨2, hn⟩ = 1 := by simp [d1]

theorem d1_apply_four (n : ℕ) (hn : 4 < n) (ζ : Fˣ) : d1 n ζ ⟨4, hn⟩ = 1 := by simp [d1]

theorem d2_apply_zero (n : ℕ) (hn : 0 < n) (ζ : Fˣ) : d2 n ζ ⟨0, hn⟩ = 1 := by simp [d2]

theorem d2_apply_two (n : ℕ) (hn : 2 < n) (ζ : Fˣ) : d2 n ζ ⟨2, hn⟩ = ζ := by simp [d2]

theorem d2_apply_four (n : ℕ) (hn : 4 < n) (ζ : Fˣ) : d2 n ζ ⟨4, hn⟩ = 1 := by simp [d2]

theorem det_dglHom_d1 {n : ℕ} (hn : 5 ≤ n) (ζ : Fˣ) :
    ((dglHom n (d1 n ζ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [coe_dglHom, Matrix.det_diagonal]
  rw [Finset.prod_eq_mul (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ (by simp [Fin.ext_iff])]
  · simp [d1]
  · intro c _ hc
    have h0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
    have h1 : c.val ≠ 1 := fun h => hc.2 (Fin.ext h)
    simp [d1, h0, h1]
  · simp
  · simp

theorem det_dglHom_d2 {n : ℕ} (hn : 5 ≤ n) (ζ : Fˣ) :
    ((dglHom n (d2 n ζ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [coe_dglHom, Matrix.det_diagonal]
  rw [Finset.prod_eq_mul (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩ (by simp [Fin.ext_iff])]
  · simp [d2]
  · intro c _ hc
    have h0 : c.val ≠ 2 := fun h => hc.1 (Fin.ext h)
    have h1 : c.val ≠ 3 := fun h => hc.2 (Fin.ext h)
    simp [d2, h0, h1]
  · simp
  · simp

theorem torus_independent {n : ℕ} (hn : 5 ≤ n) {ζ : Fˣ} (hζ : orderOf ζ = 3) (a b : ℕ)
    (h : (dglHom n (d1 n ζ) : GL (Fin n) F) ^ a * (dglHom n (d2 n ζ)) ^ b ∈
      StatedScalars (Fin n) F) : 3 ∣ a ∧ 3 ∣ b := by
  rw [← map_pow, ← map_pow, ← map_mul, dglHom_mem_scalars_iff] at h
  obtain ⟨c, hc⟩ := h
  have h4 := hc ⟨4, by omega⟩
  have h0 := hc ⟨0, by omega⟩
  have h2 := hc ⟨2, by omega⟩
  simp only [Pi.mul_apply, Pi.pow_apply, d1_apply_four, d2_apply_four, d1_apply_zero,
    d2_apply_zero, d1_apply_two, d2_apply_two, one_pow, mul_one, one_mul] at h4 h0 h2
  rw [← h4] at h0 h2
  have ha := orderOf_dvd_iff_pow_eq_one.mpr h0
  have hb := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hζ] at ha hb
  exact ⟨ha, hb⟩

@[expose] noncomputable def cycGL (F : Type) [Field F] : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_cycGL : ((cycGL F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem cycGL_pow_three : (cycGL F) ^ 3 = 1 := by
  refine Units.ext ?_
  simp only [Units.val_pow_eq_pow_val, Units.val_one, coe_cycGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

def e3 (ζ : Fˣ) : Fin 3 → Fˣ := ![1, ζ, ζ ^ 2]

theorem e3_pow_three {ζ : Fˣ} (h : ζ ^ 3 = 1) : (e3 ζ) ^ 3 = 1 := by
  funext i
  fin_cases i
  · simp [e3]
  · simpa [e3] using h
  · show (ζ ^ 2) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem det_dglHom_e3 {ζ : Fˣ} (h : ζ ^ 3 = 1) :
    ((dglHom 3 (e3 ζ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [coe_dglHom, Matrix.det_diagonal, Fin.prod_univ_three]
  have : (ζ : F) ^ 3 = 1 := by simpa using congrArg Units.val h
  simp [e3]
  calc (ζ : F) * ((ζ : F) ^ 2) = (ζ : F) ^ 3 := by ring
    _ = 1 := this

theorem det_cycGL : ((cycGL F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [coe_cycGL, Matrix.det_fin_three]

theorem e3_mul_cyc {ζ : Fˣ} (h : ζ ^ 3 = 1) :
    (dglHom 3 (e3 ζ) : GL (Fin 3) F) * cycGL F =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (cycGL F * dglHom 3 (e3 ζ)) := by
  have h' : (ζ : F) ^ 3 = 1 := by simpa using congrArg Units.val h
  refine Units.ext ?_
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, coe_cycGL,
    Matrix.scalar_apply]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [e3]
  · calc (1 : F) = (ζ : F) ^ 3 := h'.symm
      _ = ζ * ζ ^ 2 := by ring
  · ring

theorem e3_comm_mem {ζ : Fˣ} (h : ζ ^ 3 = 1) :
    (dglHom 3 (e3 ζ) : GL (Fin 3) F) * cycGL F * (dglHom 3 (e3 ζ))⁻¹ * (cycGL F)⁻¹ ∈
      StatedScalars (Fin 3) F := by
  refine ⟨ζ, ?_⟩
  rw [e3_mul_cyc h]
  simp [mul_assoc]

theorem cycGL_sq_apply_two_zero :
    (((cycGL F) ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 1 := by
  simp [pow_two, coe_cycGL, Matrix.mul_apply, Fin.sum_univ_three]

theorem e3_independent {ζ : Fˣ} (hζ : orderOf ζ = 3) (a b : ℕ)
    (h : (dglHom 3 (e3 ζ) : GL (Fin 3) F) ^ a * (cycGL F) ^ b ∈ StatedScalars (Fin 3) F) :
    3 ∣ a ∧ 3 ∣ b := by
  have hY := cycGL_pow_three (F := F)
  rw [pow_eq_pow_mod b hY] at h
  rw [← map_pow] at h
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases hb with hb | hb | hb
  · rw [hb, pow_zero, mul_one, dglHom_mem_scalars_iff] at h
    obtain ⟨c, hc⟩ := h
    have h0 := hc 0
    have h1 := hc 1
    simp only [Pi.pow_apply, e3, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow] at h0 h1
    rw [← h0] at h1
    have ha := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hζ] at ha
    exact ⟨ha, by omega⟩
  · exfalso
    rw [hb, pow_one] at h
    obtain ⟨c, hc⟩ := h
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 0) hc
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom, coe_cycGL,
      Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply] at this
    simp [e3] at this
    exact pow_ne_zero a ζ.ne_zero this.symm
  · exfalso
    rw [hb] at h
    obtain ⟨c, hc⟩ := h
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 2 0) hc
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_dglHom,
      Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.diagonal_apply] at this
    rw [cycGL_sq_apply_two_zero] at this
    simp [e3] at this
    exact pow_ne_zero a (pow_ne_zero 2 ζ.ne_zero) this.symm

theorem dglHom_unitary {n q : ℕ} (hq : q ≠ 0) (d : Fin n → Fˣ)
    (hd : ∀ i, (d i : F) ^ (q + 1) = 1) :
    (((dglHom n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map (· ^ q))ᵀ *
      ((dglHom n d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  have h0 : (0 : F) ^ q = 0 := zero_pow hq
  rw [coe_dglHom, Matrix.diagonal_map (f := fun x : F => x ^ q) h0, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← pow_succ]
  exact hd i

theorem cycGL_unitary {q : ℕ} (hq : q ≠ 0) :
    (((cycGL F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
      ((cycGL F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [coe_cycGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hq]

theorem pow_eq_one_of_dvd_three {ζ : Fˣ} (h : ζ ^ 3 = 1) {m : ℕ} (hm : 3 ∣ m) : ζ ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_mul, h, one_pow]

end NineSubgroup

open NineSubgroup

theorem exists_nine_of_psl {K : Type} [Group K] {n ℓ f : ℕ}
    (h : StatedClassicalModel K .PSL n ℓ f) (h3n : 3 ∣ n) (h3q : 3 ∣ ℓ ^ f - 1) :
    ∃ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨⟨hℓ, hf, hn2, -⟩, F, instF, instFin, hF, ⟨e⟩⟩ := h
  have hcardU : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; exact h3q
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine exists_isElemAbelian_of_mulEquiv e.symm ?_
  have hn : n = 3 ∨ 5 ≤ n := by omega
  rcases hn with rfl | hn5
  · refine exists_nine_statedProj _ (dglHom 3 (e3 ζ)) (cycGL F)
      (Subgroup.subset_closure (det_dglHom_e3 hζ3)) (Subgroup.subset_closure det_cycGL)
      (by rw [← map_pow, e3_pow_three hζ3, map_one]) cycGL_pow_three (e3_comm_mem hζ3)
      (fun a b hab => e3_independent hζ a b hab)
  · refine exists_nine_statedProj _ (dglHom n (d1 n ζ)) (dglHom n (d2 n ζ))
      (Subgroup.subset_closure (det_dglHom_d1 hn5 ζ))
      (Subgroup.subset_closure (det_dglHom_d2 hn5 ζ))
      (by rw [← map_pow, d1_pow_three n hζ3, map_one])
      (by rw [← map_pow, d2_pow_three n hζ3, map_one]) ?_
      (fun a b hab => torus_independent hn5 hζ a b hab)
    rw [torus_comm]
    exact one_mem _

theorem exists_nine_of_psu {K : Type} [Group K] {n ℓ f : ℕ}
    (h : StatedClassicalModel K .PSU n ℓ f) (h3n : 3 ∣ n) (h3q : 3 ∣ ℓ ^ f + 1) :
    ∃ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨⟨hℓ, hf, hn3, -⟩, F, instF, instFin, hF, ⟨e⟩⟩ := h
  have hq0 : ℓ ^ f ≠ 0 := (pow_pos hℓ.pos f).ne'
  have hcardU : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have := Nat.sq_sub_sq (ℓ ^ f) 1
    rw [one_pow] at this
    rw [this]
    exact Dvd.dvd.mul_right h3q _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζq : ((ζ : F)) ^ (ℓ ^ f + 1) = 1 := by
    have := pow_eq_one_of_dvd_three hζ3 h3q
    simpa using congrArg Units.val this
  refine exists_isElemAbelian_of_mulEquiv e.symm ?_
  have hn : n = 3 ∨ 5 ≤ n := by omega
  rcases hn with rfl | hn5
  · have hX : ∀ i, ((e3 ζ i : Fˣ) : F) ^ (ℓ ^ f + 1) = 1 := by
      intro i
      fin_cases i
      · simp [e3]
      · simpa [e3] using hζq
      · have : ((ζ : F) ^ 2) ^ (ℓ ^ f + 1) = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζq, one_pow]
        simpa [e3] using this
    refine exists_nine_statedProj _ (dglHom 3 (e3 ζ)) (cycGL F)
      (Subgroup.subset_closure ⟨det_dglHom_e3 hζ3, dglHom_unitary hq0 _ hX⟩)
      (Subgroup.subset_closure ⟨det_cycGL, cycGL_unitary hq0⟩)
      (by rw [← map_pow, e3_pow_three hζ3, map_one]) cycGL_pow_three (e3_comm_mem hζ3)
      (fun a b hab => e3_independent hζ a b hab)
  · have hX1 : ∀ i, ((d1 n ζ i : Fˣ) : F) ^ (ℓ ^ f + 1) = 1 := by
      intro i
      simp only [d1]
      split_ifs
      · exact hζq
      · simp [inv_pow, hζq]
      · simp
    have hX2 : ∀ i, ((d2 n ζ i : Fˣ) : F) ^ (ℓ ^ f + 1) = 1 := by
      intro i
      simp only [d2]
      split_ifs
      · exact hζq
      · simp [inv_pow, hζq]
      · simp
    refine exists_nine_statedProj _ (dglHom n (d1 n ζ)) (dglHom n (d2 n ζ))
      (Subgroup.subset_closure ⟨det_dglHom_d1 hn5 ζ, dglHom_unitary hq0 _ hX1⟩)
      (Subgroup.subset_closure ⟨det_dglHom_d2 hn5 ζ, dglHom_unitary hq0 _ hX2⟩)
      (by rw [← map_pow, d1_pow_three n hζ3, map_one])
      (by rw [← map_pow, d2_pow_three n hζ3, map_one]) ?_
      (fun a b hab => torus_independent hn5 hζ a b hab)
    rw [torus_comm]
    exact one_mem _

end CFSG.LocalAnalysis.RankThreeTheoremC
