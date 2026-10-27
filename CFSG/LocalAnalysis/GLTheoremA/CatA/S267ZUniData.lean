module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (blk mem_blk)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

variable (h) in
@[expose] noncomputable def scalarU (c : Kˣ) (hn : h.norm (c : K) = 1) (h3 : c ^ 3 = 1) : ↥(SG h) :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, mem_gramSU.2 ⟨by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, scalar_barTranspose_mul_mul, hn,
      one_smul], by
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val, h3, Units.val_one]⟩⟩

theorem coe_scalarU (c : Kˣ) (hn : h.norm (c : K) = 1) (h3 : c ^ 3 = 1) :
    (((scalarU h c hn h3 : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun _ => (c : K) := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply]

theorem projU_scalarU (c : Kˣ) (hn : h.norm (c : K) = 1) (h3 : c ^ 3 = 1) :
    projU h (scalarU h c hn h3) = 1 :=
  projU_eq_one_iff.2 ⟨c, hn, h3, rfl⟩

variable (h) in
noncomputable abbrev fieldAut (σ : K ≃+* K) : MulAut (PU h) :=
  primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ

theorem fieldAut_projU (σ : K ≃+* K) (g : ↥(SG h)) :
    fieldAut h σ (projU h g) = projU h (primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ g) :=
  primeFormFieldAut_mk h _ σ g

theorem primeFormFieldSU_apply (σ : K ≃+* K) (g : ↥(SG h)) (i j : Fin 3) :
    (((primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ g : ↥(SG h)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) :=
  rfl

theorem fieldAut_projU_diagU (σ : K ≃+* K) {d : Fin 3 → K} {hn : ∀ i, h.bar (d i) * d i = 1}
    {hd : ∏ i, d i = 1} (c : Kˣ) (hcn : h.norm (c : K) = 1) (hc3 : c ^ 3 = 1)
    (hσd : ∀ i, σ (d i) = d i * c) :
    fieldAut h σ (projU h (diagU h d hn hd)) = projU h (diagU h d hn hd) := by
  rw [fieldAut_projU]
  have he : primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ (diagU h d hn hd) =
      diagU h d hn hd * scalarU h c hcn hc3 := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [primeFormFieldSU_apply, Subgroup.coe_mul, Units.val_mul, coe_scalarU, coe_diagU,
      diagonal_mul_diagonal, diagonal_apply, diagonal_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, hσd]
    · rw [if_neg hij, if_neg hij, map_zero]
  rw [he, map_mul, projU_scalarU, mul_one]

theorem norm_apply_ringEquiv (σ : K ≃+* K) (x : K) : h.norm (σ x) = σ (h.norm x) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, UnitaryFieldData.bar_apply,
    UnitaryFieldData.bar_apply, map_mul, map_pow]

theorem diagU_mul_comm {d e : Fin 3 → K} {hn : ∀ i, h.bar (d i) * d i = 1} {hd : ∏ i, d i = 1}
    {hn' : ∀ i, h.bar (e i) * e i = 1} {he : ∏ i, e i = 1} :
    diagU h d hn hd * diagU h e hn' he = diagU h e hn' he * diagU h d hn hd := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_diagU, coe_diagU,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem exists_scalar_of_projU_eq {x y : ↥(SG h)} (hxy : projU h x = projU h y) :
    ∃ c : Kˣ, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal fun _ => (c : K) := by
  have hk : x⁻¹ * y ∈ (projU h).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 (ker_projU (h := h) ▸ hk)
  refine ⟨c, ?_⟩
  have e1 : y = x * (x⁻¹ * y) := by group
  have h1 := congrArg (fun g : ↥(SG h) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) e1
  simp only [Subgroup.coe_mul, Units.val_mul] at h1
  rw [h1, ← Units.val_mul, ← Subgroup.coe_mul, hc, Matrix.GeneralLinearGroup.coe_scalar,
    scalar_apply]

@[expose] noncomputable def dOne (lam : K) : Fin 3 → K := ![(lam ^ 2)⁻¹, lam, lam]

theorem ne_zero_of_norm {x : K} (hx : h.bar x * x = 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

theorem prod_dOne {lam : K} (hlam0 : lam ≠ 0) : ∏ i, dOne lam i = 1 := by
  rw [Fin.prod_univ_three]
  simp only [dOne, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  field_simp

theorem norm_dOne {lam : K} (hlamn : h.bar lam * lam = 1) :
    ∀ i, h.bar (dOne lam i) * dOne lam i = 1 := by
  intro i
  fin_cases i
  · simp only [dOne, Fin.zero_eta, Matrix.cons_val_zero, map_inv₀, map_pow]
    rw [← mul_inv, ← mul_pow, hlamn, one_pow, inv_one]
  · exact hlamn
  · exact hlamn

theorem dOne_one_eq_two (lam : K) : dOne lam 1 = dOne lam 2 := rfl

theorem dOne_zero_ne_one {lam : K} (hlam0 : lam ≠ 0) (hlam3 : lam ^ 3 ≠ 1) :
    dOne lam 0 ≠ dOne lam 1 := by
  simp only [dOne, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  intro he
  apply hlam3
  have : lam * (lam ^ 2)⁻¹ = lam * lam := by rw [he]
  field_simp at he
  linear_combination -he

variable (h) in
@[expose] noncomputable def tOne {lam : K} (hlamn : h.bar lam * lam = 1) : ↥(SG h) :=
  diagU h (dOne lam) (norm_dOne hlamn) (prod_dOne (ne_zero_of_norm hlamn))

variable (h) in
@[expose] noncomputable def tTwo {ζ : K} (hζn : h.bar ζ * ζ = 1) : ↥(SG h) :=
  diagU h ![1, ζ, ζ⁻¹] (norm_diagBlk hζn) (prod_diagBlk (ne_zero_of_norm hζn))

theorem blockU_le_centralizer_tOne {lam : K} (hlamn : h.bar lam * lam = 1) :
    blockU h blk ≤ Subgroup.centralizer ({tOne h hlamn} : Set ↥(SG h)) :=
  blockU_le_centralizer (dOne_one_eq_two lam)

theorem projU_tOne_mem_centralizer {lam : K} (hlamn : h.bar lam * lam = 1) :
    projU h (tOne h hlamn) ∈ Subgroup.centralizer (JU h : Set (PU h)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  have := Subgroup.mem_centralizer_singleton_iff.1 (blockU_le_centralizer_tOne hlamn hg)
  rw [← map_mul, ← map_mul, this]

theorem projU_tTwo_not_mem_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hζn : h.bar ζ * ζ = 1) :
    projU h (tTwo h hζn) ∉ Subgroup.centralizer (JU h : Set (PU h)) := by
  intro hc
  have hw : projU h (swapBlk h) ∈ JU h := ⟨swapBlk h, swapBlk_mem_blockU, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hw
  rw [← map_mul, ← map_mul] at h1
  obtain ⟨c, hc⟩ := exists_scalar_of_projU_eq h1
  have hζ0 : ζ ≠ 0 := ne_zero_of_norm hζn
  simp only [Subgroup.coe_mul, Units.val_mul, tTwo, coe_diagU, coe_swapBlk] at hc
  rw [Matrix.mul_assoc, diagonal_mul_diagonal] at hc
  have h00 := congrFun (congrFun hc 0) 0
  have h12 := congrFun (congrFun hc 1) 2
  rw [diagonal_mul, mul_diagonal] at h00 h12
  simp [swapMat] at h00 h12
  have hc1 : (c : K) = 1 := by linear_combination -h00
  rw [hc1, mul_one] at h12
  have h2 : ζ = ζ⁻¹ := by linear_combination h12
  have h3 : ζ ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h2]
    exact mul_inv_cancel₀ hζ0
  have h4 : p ∣ 2 := hζ.dvd_of_pow_eq_one 2 h3
  have := Nat.le_of_dvd (by norm_num) h4
  have := hp.two_le
  omega

section R

variable {p : ℕ} {lam ζ : K} (hlamn : h.bar lam * lam = 1) (hζn : h.bar ζ * ζ = 1)

variable (h) in
noncomputable abbrev RU : Subgroup (PU h) :=
  Subgroup.zpowers (projU h (tOne h hlamn)) ⊔ Subgroup.zpowers (projU h (tTwo h hζn))

theorem norm_eq_one_of {x : K} (hx : h.bar x * x = 1) : h.norm x = 1 := by
  rw [UnitaryFieldData.norm, mul_comm, hx]

theorem projU_tOne_pow (hlam3p : lam ^ (3 * p) = 1) : projU h (tOne h hlamn) ^ p = 1 := by
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have hlp0 : lam ^ p ≠ 0 := pow_ne_zero p hlam0
  rw [← map_pow, projU_eq_one_iff]
  refine ⟨Units.mk0 (lam ^ p) hlp0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, UnitaryFieldData.norm, map_pow, ← mul_pow, mul_comm, hlamn, one_pow]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm, hlam3p, Units.val_one]
  · apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, tOne, coe_diagU, diagonal_pow,
      Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0]
    congr 1
    funext i
    fin_cases i
    · simp only [dOne, Fin.zero_eta, Pi.pow_apply, Matrix.cons_val_zero, inv_pow, ← pow_mul]
      rw [inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero _ hlam0), ← pow_add,
        show 2 * p + p = 3 * p by ring, hlam3p]
    · rfl
    · rfl

theorem projU_tOne_ne_one (hlam3 : lam ^ 3 ≠ 1) : projU h (tOne h hlamn) ≠ 1 := by
  intro h1
  obtain ⟨c, -, -, hc⟩ := projU_eq_one_iff.1 h1
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [tOne, coe_diagU, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply] at e
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 1
  simp only [diagonal_apply_eq] at e0 e1
  exact dOne_zero_ne_one hlam0 hlam3 (e0.trans e1.symm)

theorem projU_tTwo_pow (hζ : IsPrimitiveRoot ζ p) : projU h (tTwo h hζn) ^ p = 1 := by
  rw [← map_pow]
  have : tTwo h hζn ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, tTwo, coe_diagU, diagonal_pow]
    have hpow : (![1, ζ, ζ⁻¹] : Fin 3 → K) ^ p = 1 := by
      funext k
      fin_cases k <;> simp [hζ.pow_eq_one]
    rw [hpow]
    rfl
  rw [this, map_one]

theorem projU_tOne_comm_tTwo :
    projU h (tOne h hlamn) * projU h (tTwo h hζn) = projU h (tTwo h hζn) * projU h (tOne h hlamn) := by
  rw [← map_mul, ← map_mul, tOne, tTwo, diagU_mul_comm]

variable {hlamn hζn}

theorem projU_tTwo_not_mem_zpowers (hp : p.Prime) (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) :
    projU h (tTwo h hζn) ∉ Subgroup.zpowers (projU h (tOne h hlamn)) := fun hmem =>
  projU_tTwo_not_mem_centralizer hp hp2 hζ hζn
    ((Subgroup.zpowers_le.2 (projU_tOne_mem_centralizer hlamn)) hmem)

theorem isElemAbelian_RU [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hlam3p : lam ^ (3 * p) = 1) (hlam3 : lam ^ 3 ≠ 1) :
    IsElemAbelian p (RU h hlamn hζn) ∧ Nat.card ↥(RU h hlamn hζn) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (PU h) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hord : orderOf (projU h (tOne h hlamn)) = p :=
    orderOf_eq_prime (projU_tOne_pow hlamn hlam3p) (projU_tOne_ne_one hlamn hlam3)
  have hA : IsElemAbelian p (Subgroup.zpowers (projU h (tOne h hlamn))) :=
    ⟨inferInstance, fun y hy => orderOf_dvd_iff_pow_eq_one.1 (hord ▸ orderOf_dvd_of_mem_zpowers hy)⟩
  obtain ⟨hel, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hA
    (projU_tTwo_not_mem_zpowers hp hp2 hζ) (projU_tTwo_pow hζn hζ) (fun a ha => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (projU_tOne_comm_tTwo hlamn hζn) k).eq)
  refine ⟨hel, ?_⟩
  rw [hcard, Nat.card_zpowers, hord, sq]

end R

section Fix

variable {σ : K ≃+* K} {lam ζ : K} {hlamn : h.bar lam * lam = 1} {hζn : h.bar ζ * ζ = 1}

theorem fieldAut_tOne (hlamσ : (σ lam * lam⁻¹) ^ 3 = 1) :
    fieldAut h σ (projU h (tOne h hlamn)) = projU h (tOne h hlamn) := by
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have hσ0 : σ lam ≠ 0 := (map_ne_zero σ).2 hlam0
  set c0 : K := σ lam * lam⁻¹ with hc0
  have hc00 : c0 ≠ 0 := mul_ne_zero hσ0 (inv_ne_zero hlam0)
  have hσl : σ lam = lam * c0 := by rw [hc0]; field_simp
  refine fieldAut_projU_diagU σ (Units.mk0 c0 hc00) ?_ ?_ ?_
  · rw [Units.val_mk0, hc0, norm_mul_eq h, norm_apply_ringEquiv, norm_eq_one_of hlamn, map_one,
      one_mul, UnitaryFieldData.norm, map_inv₀, ← mul_inv, ← UnitaryFieldData.norm,
      norm_eq_one_of hlamn, inv_one]
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hlamσ, Units.val_one])
  · intro i
    rw [Units.val_mk0]
    fin_cases i
    · simp only [dOne, Fin.zero_eta, Matrix.cons_val_zero]
      rw [map_inv₀, map_pow, hσl, mul_pow, mul_inv]
      congr 1
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hlamσ])
    · exact hσl
    · exact hσl

theorem fieldAut_tTwo (hζσ : σ ζ = ζ) :
    fieldAut h σ (projU h (tTwo h hζn)) = projU h (tTwo h hζn) := by
  refine fieldAut_projU_diagU σ 1 (by rw [Units.val_one, UnitaryFieldData.norm, map_one,
    mul_one]) (one_pow 3) fun i => ?_
  rw [Units.val_one, mul_one]
  fin_cases i
  · simp
  · exact hζσ
  · simp [map_inv₀, hζσ]

theorem RU_le_fixSubgroup (hlamσ : (σ lam * lam⁻¹) ^ 3 = 1) (hζσ : σ ζ = ζ) :
    RU h hlamn hζn ≤ fixSubgroup (fieldAut h σ) :=
  sup_le (Subgroup.zpowers_le.2 (mem_fixSubgroup.2 (fieldAut_tOne hlamσ)))
    (Subgroup.zpowers_le.2 (mem_fixSubgroup.2 (fieldAut_tTwo hζσ)))

end Fix

theorem norm_dU : ∀ i, h.bar ((![1, -1, -1] : Fin 3 → K) i) * (![1, -1, -1] : Fin 3 → K) i = 1 := by
  intro i
  fin_cases i <;> simp

theorem prod_dU : ∏ i, (![1, -1, -1] : Fin 3 → K) i = 1 := by
  simp [Fin.prod_univ_three]

variable (h) in
@[expose] noncomputable def uU : ↥(SG h) := diagU h ![1, -1, -1] norm_dU prod_dU

theorem projU_uU_ne_one (h2 : (2 : K) ≠ 0) : projU h (uU h) ≠ 1 := by
  intro h1
  obtain ⟨c, -, -, hc⟩ := projU_eq_one_iff.1 h1
  have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [uU, coe_diagU, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply] at e
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 1
  simp only [diagonal_apply_eq] at e0 e1
  simp at e0 e1
  apply h2
  linear_combination e0 - e1

theorem projU_uU_sq : projU h (uU h) ^ 2 = 1 := by
  rw [← map_pow]
  have : uU h ^ 2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, uU, coe_diagU, diagonal_pow]
    have hpow : (![1, -1, -1] : Fin 3 → K) ^ 2 = 1 := by
      funext k
      fin_cases k <;> simp
    rw [hpow]
    rfl
  rw [this, map_one]

theorem uU_comm_blockU {g : ↥(SG h)} (hg : g ∈ blockU h blk) : g * uU h = uU h * g := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, uU, coe_diagU]
  have hg' := mem_blockU_iff.1 hg
  ext i j
  rw [mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [hg' 0 1 (Or.inl (by simp [mem_blk])), hg' 0 2 (Or.inl (by simp [mem_blk])),
      hg' 1 0 (Or.inr (by simp [mem_blk])), hg' 2 0 (Or.inr (by simp [mem_blk]))]

theorem projU_uU_comm_JU {j : PU h} (hj : j ∈ JU h) : j * projU h (uU h) = projU h (uU h) * j := by
  obtain ⟨g, hg, rfl⟩ := hj
  rw [← map_mul, ← map_mul, uU_comm_blockU hg]

theorem fieldAut_uU (σ : K ≃+* K) : fieldAut h σ (projU h (uU h)) = projU h (uU h) := by
  refine fieldAut_projU_diagU σ 1 (by rw [Units.val_one, UnitaryFieldData.norm, map_one,
    mul_one]) (one_pow 3) fun i => ?_
  rw [Units.val_one, mul_one]
  fin_cases i <;> simp

theorem dvd_of_zpow_apply_eq {σ : K ≃+* K} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p) {a : K}
    (ha : σ a ≠ a) {k : ℤ} (hk : (σ ^ k) a = a) : (p : ℤ) ∣ k := by
  by_contra hnd
  obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hnd
  have hσp : σ ^ (p : ℤ) = 1 := by rw [zpow_natCast, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ = (σ ^ k) ^ v := by
    calc σ = σ ^ (u * (p : ℤ) + v * k) := by rw [huv, zpow_one]
      _ = (σ ^ (p : ℤ)) ^ u * (σ ^ k) ^ v := by
        rw [_root_.zpow_add, mul_comm u, _root_.zpow_mul, mul_comm v, _root_.zpow_mul]
      _ = (σ ^ k) ^ v := by rw [hσp, _root_.one_zpow, one_mul]
  let H : Subgroup (K ≃+* K) :=
    { carrier := {τ | τ a = a}
      mul_mem' := fun {x y} hx hy => by
        change x (y a) = a
        rw [show y a = a from hy, show x a = a from hx]
      one_mem' := rfl
      inv_mem' := fun {x} hx => by
        change x.symm a = a
        rw [RingEquiv.symm_apply_eq]
        exact (show x a = a from hx).symm }
  have hkH : σ ^ k ∈ H := hk
  have hσH : σ ∈ H := hσ1 ▸ H.zpow_mem hkH v
  exact ha hσH

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem centMod_RU (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {lam ζ : K} {hlamn : h.bar lam * lam = 1}
    (hlam3p : lam ^ (3 * p) = 1) (hlam3 : lam ^ 3 ≠ 1) {hζn : h.bar ζ * ζ = 1}
    (hζ : IsPrimitiveRoot ζ p) {a : K} (han : h.bar a * a = 1) (haσ : σ a ≠ a) (k : ℤ) (s : PU h)
    (hs : s ∈ RU h hlamn hζn)
    (hcent : ∀ j ∈ JU h, (fieldAut h σ ^ k * MulAut.conj s) j * j⁻¹ ∈ GLAPPrimeCoreOf p (JU h)) :
    fieldAut h σ ^ k = 1 ∧ s ∈ Subgroup.zpowers (projU h (tOne h hlamn)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (PU h) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hpJ : p ∣ Nat.card ↥(JU h) :=
    (dvd_card_JU hp hp2 hζ hζn).trans (Subgroup.card_quotient_dvd_card _)
  have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp
    (isQuasisimple_JU hK hq) hpJ (fieldAut h σ ^ k * MulAut.conj s).toMonoidHom hcent
  obtain ⟨hRel, hRcard⟩ := isElemAbelian_RU (hlamn := hlamn) (hζn := hζn) hp hp2 hζ hlam3p hlam3
  have ha0 : a ≠ 0 := ne_zero_of_norm han
  set j₁ := projU h (diagU h ![1, a, a⁻¹] (norm_diagBlk han) (prod_diagBlk ha0)) with hj₁
  have hj₁J : j₁ ∈ JU h := ⟨_, diagU_blk_mem_blockU han ha0, rfl⟩
  have hsj : s * j₁ = j₁ * s := by
    have hle : RU h hlamn hζn ≤ Subgroup.centralizer ({j₁} : Set (PU h)) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_) <;>
        rw [Subgroup.mem_centralizer_singleton_iff, hj₁, ← map_mul, ← map_mul] <;>
        exact congrArg _ diagU_mul_comm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hs)
  have hk1 : fieldAut h σ ^ k = 1 := by
    have e := hfix j₁ hj₁J
    have e2 : (fieldAut h σ ^ k * MulAut.conj s) j₁ = (fieldAut h σ ^ k) j₁ := by
      change (fieldAut h σ ^ k) (s * j₁ * s⁻¹) = _
      rw [hsj, mul_assoc, mul_inv_cancel, mul_one]
    change (fieldAut h σ ^ k * MulAut.conj s) j₁ = j₁ at e
    rw [e2, ← map_zpow, hj₁, fieldAut_projU] at e
    obtain ⟨c, hc⟩ := exists_scalar_of_projU_eq e
    have h00 := congrFun (congrFun hc 0) 0
    have h11 := congrFun (congrFun hc 1) 1
    rw [mul_diagonal] at h00 h11
    simp only [coe_diagU, primeFormFieldSU_apply, diagonal_apply_eq] at h00 h11
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_one, one_mul]
      at h00 h11
    rw [← h00, mul_one] at h11
    have hdvd := dvd_of_zpow_apply_eq hp hσ haσ h11.symm
    obtain ⟨m, rfl⟩ := hdvd
    rw [← map_zpow, _root_.zpow_mul, zpow_natCast, ← hσ, pow_orderOf_eq_one, _root_.one_zpow,
      map_one]
  refine ⟨hk1, ?_⟩
  have hsC : s ∈ Subgroup.centralizer (JU h : Set (PU h)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have e := hfix j hj
    change (fieldAut h σ ^ k * MulAut.conj s) j = j at e
    rw [hk1, one_mul, MulAut.conj_apply] at e
    calc j * s = s * j * s⁻¹ * s := by rw [e]
      _ = s * j := by group
  by_contra hsr
  have hsp : s ^ p = 1 := hRel.2 s hs
  have hcomm : ∀ x ∈ Subgroup.zpowers (projU h (tOne h hlamn)), x * s = s * x := by
    intro x hx
    have hxR : x ∈ RU h hlamn hζn := (le_sup_left : Subgroup.zpowers _ ≤ RU h hlamn hζn) hx
    exact congrArg Subtype.val (hRel.1.is_comm.comm ⟨x, hxR⟩ ⟨s, hs⟩)
  have hord : orderOf (projU h (tOne h hlamn)) = p :=
    orderOf_eq_prime (projU_tOne_pow hlamn hlam3p) (projU_tOne_ne_one hlamn hlam3)
  have hA : IsElemAbelian p (Subgroup.zpowers (projU h (tOne h hlamn))) :=
    ⟨inferInstance, fun y hy => orderOf_dvd_iff_pow_eq_one.1 (hord ▸ orderOf_dvd_of_mem_zpowers hy)⟩
  obtain ⟨-, hWcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hA hsr hsp hcomm
  have hWR : Subgroup.zpowers (projU h (tOne h hlamn)) ⊔ Subgroup.zpowers s ≤ RU h hlamn hζn :=
    sup_le le_sup_left (Subgroup.zpowers_le.2 hs)
  have hWeq : Subgroup.zpowers (projU h (tOne h hlamn)) ⊔ Subgroup.zpowers s = RU h hlamn hζn :=
    Subgroup.eq_of_le_of_card_ge hWR (by rw [hRcard, hWcard, Nat.card_zpowers, hord, sq])
  have hWC : Subgroup.zpowers (projU h (tOne h hlamn)) ⊔ Subgroup.zpowers s ≤
      Subgroup.centralizer (JU h : Set (PU h)) :=
    sup_le (Subgroup.zpowers_le.2 (projU_tOne_mem_centralizer hlamn)) (Subgroup.zpowers_le.2 hsC)
  have ht2 : projU h (tTwo h hζn) ∈ RU h hlamn hζn :=
    (le_sup_right : Subgroup.zpowers _ ≤ RU h hlamn hζn) (Subgroup.mem_zpowers _)
  rw [← hWeq] at ht2
  exact projU_tTwo_not_mem_centralizer hp hp2 hζ hζn (hWC ht2)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
