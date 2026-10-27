module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.SP.Local

namespace PGL2Cartan

open Matrix CFSG.GorensteinWalter Subgroup

section

variable {F : Type*} [Field F]

@[expose] def uGL (s : F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, s; 0, 1] (by simp [Matrix.det_fin_two])

@[expose] def dGL (l : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (l : F)] (by simp [Matrix.det_fin_two])

@[simp] lemma uGL_val (s : F) :
    ((uGL s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] := rfl

@[simp] lemma dGL_val (l : Fˣ) :
    ((dGL l : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, (l : F)] := rfl

lemma gl2_mul_apply (A B : GL (Fin 2) F) (i j : Fin 2) :
    ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j
      = (A : Matrix (Fin 2) (Fin 2) F) i 0 * (B : Matrix (Fin 2) (Fin 2) F) 0 j
        + (A : Matrix (Fin 2) (Fin 2) F) i 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma gl2_scalar_apply (c : Fˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j
      = if i = j then (c : F) else 0 := by
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

lemma uGL_add (a b : F) : uGL (a + b) = uGL a * uGL b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2_mul_apply, add_comm]

lemma uGL_zero : (uGL (0 : F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma dGL_mul (a b : Fˣ) : (dGL (a * b) : GL (Fin 2) F) = dGL a * dGL b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2_mul_apply]

lemma dGL_one : (dGL (1 : Fˣ) : GL (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def uHom : Multiplicative F →* GL (Fin 2) F where
  toFun s := uGL (Multiplicative.toAdd s)
  map_one' := uGL_zero
  map_mul' _ _ := uGL_add _ _

def dHom : Fˣ →* GL (Fin 2) F where
  toFun := dGL
  map_one' := dGL_one
  map_mul' := dGL_mul

lemma mk_eq_mk_iff_entries {A B : GL (Fin 2) F} :
    Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B ↔
      ∃ c : Fˣ, ∀ i j, (B : Matrix (Fin 2) (Fin 2) F) i j
        = (A : Matrix (Fin 2) (Fin 2) F) i j * c := by
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i j => ?_⟩
    rw [← hc]
    simp [gl2_mul_apply, gl2_scalar_apply]
    fin_cases j <;> simp
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    ext i j
    rw [hc]
    simp [gl2_mul_apply, gl2_scalar_apply]
    fin_cases j <;> simp

def stdU (F : Type*) [Field F] : Subgroup (PGL2 F) :=
  (Matrix.ProjGenLinGroup.mk.comp (uHom (F := F))).range

def torus0 (F : Type*) [Field F] : Subgroup (PGL2 F) :=
  (Matrix.ProjGenLinGroup.mk.comp (dHom (F := F))).range

lemma mem_stdU {x : PGL2 F} : x ∈ stdU F ↔ ∃ s : F, Matrix.ProjGenLinGroup.mk (uGL s) = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨Multiplicative.ofAdd s, rfl⟩

lemma mem_torus0 {x : PGL2 F} :
    x ∈ torus0 F ↔ ∃ l : Fˣ, Matrix.ProjGenLinGroup.mk (dGL l) = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

lemma mk_uGL_mem_stdU (s : F) : Matrix.ProjGenLinGroup.mk (uGL s) ∈ stdU F :=
  mem_stdU.mpr ⟨s, rfl⟩

lemma mk_dGL_mem_torus0 (l : Fˣ) : Matrix.ProjGenLinGroup.mk (dGL l) ∈ torus0 F :=
  mem_torus0.mpr ⟨l, rfl⟩

lemma mk_uGL_inj {a b : F}
    (h : Matrix.ProjGenLinGroup.mk (uGL a) = Matrix.ProjGenLinGroup.mk (uGL b)) : a = b := by
  obtain ⟨c, hc⟩ := mk_eq_mk_iff_entries.mp h
  have h00 := hc 0 0
  have h01 := hc 0 1
  simp at h00 h01
  rw [← h00] at h01
  simpa using h01.symm

lemma mk_dGL_inj {a b : Fˣ}
    (h : Matrix.ProjGenLinGroup.mk (dGL a) = Matrix.ProjGenLinGroup.mk (dGL b)) : a = b := by
  obtain ⟨c, hc⟩ := mk_eq_mk_iff_entries.mp h
  have h00 := hc 0 0
  have h11 := hc 1 1
  simp at h00 h11
  apply Units.ext
  rw [← h00] at h11
  simpa using h11.symm

lemma card_stdU : Nat.card (stdU F) = Nat.card F := by
  have hinj : Function.Injective (Matrix.ProjGenLinGroup.mk.comp (uHom (F := F))) := fun a b h =>
    Multiplicative.toAdd.injective (mk_uGL_inj h)
  calc Nat.card (stdU F) = Nat.card (Multiplicative F) :=
        (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card F := Nat.card_congr Multiplicative.toAdd

lemma torus0Equiv_aux : Function.Injective (Matrix.ProjGenLinGroup.mk.comp (dHom (F := F))) :=
  fun _ _ h => mk_dGL_inj h

noncomputable def torus0Equiv (F : Type*) [Field F] : Fˣ ≃* torus0 F :=
  MulEquiv.ofBijective (Matrix.ProjGenLinGroup.mk.comp (dHom (F := F))).rangeRestrict
    ⟨fun _ _ h => torus0Equiv_aux (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

lemma isCyclic_torus0 [Finite F] : IsCyclic (torus0 F) :=
  (torus0Equiv F).isCyclic.mp inferInstance

lemma card_torus0 [Finite F] : Nat.card (torus0 F) = Nat.card F - 1 := by
  rw [← Nat.card_congr (torus0Equiv F).toEquiv, Nat.card_units]

lemma dGL_mul_uGL (l : Fˣ) (a : F) : dGL l * uGL a = uGL (a / l) * dGL l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2_mul_apply]

lemma torus0_normalizes {s y : PGL2 F} (hs : s ∈ torus0 F) (hy : y ∈ stdU F) :
    s * y * s⁻¹ ∈ stdU F := by
  obtain ⟨l, rfl⟩ := mem_torus0.mp hs
  obtain ⟨a, rfl⟩ := mem_stdU.mp hy
  rw [← map_inv, ← map_mul, ← map_mul, dGL_mul_uGL, mul_assoc, mul_inv_cancel, mul_one]
  exact mk_uGL_mem_stdU _

lemma uGL_neg (s : F) : (uGL s)⁻¹ = uGL (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← uGL_add, add_neg_cancel, uGL_zero])

lemma gl2_entry10_zero_of_normalizes {A : GL (Fin 2) F}
    (hA : Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk (uGL 1) *
      (Matrix.ProjGenLinGroup.mk A)⁻¹ ∈ stdU F) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨s', hs'⟩ := mem_stdU.mp hA
  have h : Matrix.ProjGenLinGroup.mk (A * uGL 1) = Matrix.ProjGenLinGroup.mk (uGL s' * A) := by
    rw [map_mul, map_mul, hs']
    group
  obtain ⟨c, hc⟩ := mk_eq_mk_iff_entries.mp h
  have e10 := hc 1 0
  have e11 := hc 1 1
  simp [gl2_mul_apply] at e10 e11
  by_contra hc0
  have h1 : (c : F) = 1 := by
    have h2 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 * ((c : F) - 1) = 0 := by
      linear_combination -e10
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hc0
    · exact sub_eq_zero.mp h3
  rw [h1] at e11
  apply hc0
  linear_combination -e11

lemma exists_conj_torus0 {x : PGL2 F} (hx : ∀ y ∈ stdU F, x * y * x⁻¹ ∈ stdU F)
    (hxU : x ∉ stdU F) :
    ∃ s : F, (Matrix.ProjGenLinGroup.mk (uGL s))⁻¹ * x * Matrix.ProjGenLinGroup.mk (uGL s) ∈
      torus0 F := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  have h10 := gl2_entry10_zero_of_normalizes (hx _ (mk_uGL_mem_stdU 1))
  have hdet : Matrix.det (A : Matrix (Fin 2) (Fin 2) F) ≠ 0 := A.det_ne_zero
  rw [Matrix.det_fin_two, h10] at hdet
  simp only [mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have had : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    intro h
    apply hxU
    have hmk : Matrix.ProjGenLinGroup.mk A =
        Matrix.ProjGenLinGroup.mk (uGL ((A : Matrix (Fin 2) (Fin 2) F) 0 1 /
          (A : Matrix (Fin 2) (Fin 2) F) 0 0)) := by
      rw [mk_eq_mk_iff_entries]
      refine ⟨Units.mk0 ((A : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ (inv_ne_zero ha), fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp [h10, ← h] <;> field_simp
    rw [hmk]
    exact mk_uGL_mem_stdU _
  have hsub : (A : Matrix (Fin 2) (Fin 2) F) 1 1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm had)
  refine ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 1 /
    ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0), ?_⟩
  have hε : (A : Matrix (Fin 2) (Fin 2) F) 1 1 / (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
    div_ne_zero hd ha
  have key : uGL (-((A : Matrix (Fin 2) (Fin 2) F) 0 1 /
        ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0))) * A *
      uGL ((A : Matrix (Fin 2) (Fin 2) F) 0 1 /
        ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ ha) *
        dGL (Units.mk0 _ hε) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gl2_mul_apply, gl2_scalar_apply, h10] <;> field_simp
    ring
  rw [← map_inv, uGL_neg, ← map_mul, ← map_mul, key, map_mul, Matrix.ProjGenLinGroup.mk_scalar,
    one_mul]
  exact mk_dGL_mem_torus0 _

lemma isOddPrimePower_of_odd [Finite F] (hodd : Odd (Nat.card F)) :
    IsOddPrimePower (Nat.card F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r, hr, n, hrp, hn⟩ := FiniteField.card' F
  rw [← Nat.card_eq_fintype_card] at hn
  refine ⟨r, n, hrp, ?_, n.pos, hn⟩
  rcases hrp.eq_two_or_odd' with h | h
  · exfalso
    rw [hn, h] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  · exact h

lemma finite_pgl2 [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

attribute [local instance] finite_pgl2

lemma exists_conj_stdU [Finite F] (hodd : Odd (Nat.card F)) {P : Subgroup (PGL2 F)}
    (hP : Nat.card P = Nat.card F) :
    ∃ g : PGL2 F, ∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ stdU F := by
  classical
  obtain ⟨p, n, hp, -, hn, hq⟩ := isOddPrimePower_of_odd hodd
  have : Fact p.Prime := ⟨hp⟩
  have hndvd : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro h
    have h1 : p ∣ Nat.card F ^ 2 := by
      rw [hq, ← pow_mul]
      exact dvd_pow_self p (by omega)
    have h2 : p ∣ 1 := by
      have := Nat.dvd_sub h1 h
      have h3 : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
      rwa [Nat.sub_sub_self (by omega)] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  have hsyl : ∀ Q : Subgroup (PGL2 F), Nat.card Q = Nat.card F →
      ∃ S : Sylow p (PGL2 F), (S : Subgroup (PGL2 F)) = Q := by
    intro Q hQ
    have hQp : IsPGroup p Q := IsPGroup.of_card (n := n) (by rw [hQ, hq])
    have hidx : Q.index = Nat.card F ^ 2 - 1 := by
      have h1 := Q.card_mul_index
      rw [hQ, pgl2_card_formula F] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    exact ⟨hQp.toSylow (by rw [hidx]; exact hndvd), rfl⟩
  obtain ⟨SP, hSP⟩ := hsyl P hP
  obtain ⟨SU, hSU⟩ := hsyl (stdU F) card_stdU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PGL2 F) SP SU
  refine ⟨g, fun x => ?_⟩
  have hcoe : ((g • SP : Sylow p (PGL2 F)) : Subgroup (PGL2 F)) = stdU F := by
    rw [hg, hSU]
  rw [Sylow.coe_subgroup_smul, hSP] at hcoe
  constructor
  · intro hx
    rw [← hcoe, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hcoe, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    have : s = x := by
      simp only [MulAut.smul_def, MulAut.conj_apply] at hsx
      exact mul_left_cancel (mul_right_cancel hsx)
    rwa [← this]

lemma conj_stdU_mem_iff {g u : PGL2 F} (hg : g ∈ stdU F) :
    g⁻¹ * u * g ∈ stdU F ↔ u ∈ stdU F := by
  constructor
  · intro h
    have := mul_mem (mul_mem hg h) (inv_mem hg)
    simpa [mul_assoc] using this
  · intro h
    exact mul_mem (mul_mem (inv_mem hg) h) hg

lemma exists_std_iso {M : Type*} [Group M] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (θ : M ≃* PGL2 F) (Y : Subgroup M) (hY : Nat.card Y = Nat.card F)
    (h : M) (hh : orderOf h = (Nat.card F - 1) / 2) (hhY : ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) :
    ∃ φ : M ≃* PGL2 F, (∀ y, y ∈ Y ↔ φ y ∈ stdU F) ∧ φ h ∈ torus0 F := by
  have hP : Nat.card (Y.map θ.toMonoidHom) = Nat.card F := by
    rw [Subgroup.card_map_of_injective θ.injective, hY]
  obtain ⟨g, hg⟩ := exists_conj_stdU hodd hP
  let φ₁ : M ≃* PGL2 F := θ.trans (MulAut.conj g)
  have hφ₁ : ∀ y, y ∈ Y ↔ φ₁ y ∈ stdU F := by
    intro y
    have h1 := hg (θ y)
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hnorm : ∀ u ∈ stdU F, φ₁ h * u * (φ₁ h)⁻¹ ∈ stdU F := by
    intro u hu
    have h1 : φ₁.symm u ∈ Y := (hφ₁ _).mpr (by simpa using hu)
    have h2 := (hφ₁ _).mp (hhY _ h1)
    simpa using h2
  have hnotin : φ₁ h ∉ stdU F := by
    intro hmem
    have h1 : orderOf (φ₁ h) ∣ Nat.card F := by
      rw [← card_stdU]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    rw [MulEquiv.orderOf_eq, hh] at h1
    obtain ⟨k, hk⟩ := hodd
    have h2 : (Nat.card F - 1) / 2 ∣ Nat.card F - 1 := ⟨2, by omega⟩
    have h3 := Nat.dvd_sub h1 h2
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  obtain ⟨s, hs⟩ := exists_conj_torus0 hnorm hnotin
  refine ⟨φ₁.trans (MulAut.conj (Matrix.ProjGenLinGroup.mk (uGL s))⁻¹), fun y => ?_, ?_⟩
  · simp only [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
    rw [conj_stdU_mem_iff (mk_uGL_mem_stdU s)]
    exact hφ₁ y
  · simpa using hs

lemma dGL_inv (l : Fˣ) : dGL l⁻¹ = (dGL l : GL (Fin 2) F)⁻¹ := map_inv (dHom (F := F)) l

lemma mk_dGL_inv (l : Fˣ) :
    (Matrix.ProjGenLinGroup.mk (dGL l))⁻¹ = Matrix.ProjGenLinGroup.mk (dGL l⁻¹) := by
  rw [dGL_inv, map_inv]

lemma inverts_torus0_or {ε : Fˣ} (hε : ε ≠ 1) {w : PGL2 F}
    (hw : w * Matrix.ProjGenLinGroup.mk (dGL ε) * w⁻¹ = (Matrix.ProjGenLinGroup.mk (dGL ε))⁻¹) :
    (∀ t ∈ torus0 F, w * t * w⁻¹ = t⁻¹) ∨ (ε = -1 ∧ w ∈ torus0 F) := by
  obtain ⟨W, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective w
  rw [mul_inv_eq_iff_eq_mul, mk_dGL_inv, ← map_mul, ← map_mul] at hw
  obtain ⟨u, hu⟩ := mk_eq_mk_iff_entries.mp hw
  have e00 := hu 0 0
  have e01 := hu 0 1
  have e10 := hu 1 0
  have e11 := hu 1 1
  simp [gl2_mul_apply] at e00 e01 e10 e11
  have hdet : Matrix.det (W : Matrix (Fin 2) (Fin 2) F) ≠ 0 := W.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  have hε1 : (ε : F) ≠ 1 := fun h => hε (Units.ext h)
  have hεne : (ε : F) ≠ 0 := ε.ne_zero
  have hεinv1 : (ε : F)⁻¹ ≠ 1 := fun h => hε1 (inv_eq_one.mp h)
  by_cases hu1 : (u : F) = 1
  ·
    right
    rw [hu1] at e01 e10 e11
    have hb : (W : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have h2 : (W : Matrix (Fin 2) (Fin 2) F) 0 1 * ((ε : F) - 1) = 0 := by
        linear_combination -e01
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hε1
    have hc : (W : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have h2 : (W : Matrix (Fin 2) (Fin 2) F) 1 0 * ((ε : F)⁻¹ - 1) = 0 := by
        linear_combination e10
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hεinv1
    rw [hb, hc] at hdet
    simp only [mul_zero, sub_zero] at hdet
    have ha : (W : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hd : (W : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    constructor
    · have hinv : (ε : F)⁻¹ = ε :=
        mul_left_cancel₀ hd (by linear_combination e11)
      have hsq : (ε : F) * ε = 1 := by
        calc (ε : F) * ε = ε * (ε : F)⁻¹ := by rw [hinv]
          _ = 1 := mul_inv_cancel₀ hεne
      have h2 : ((ε : F) - 1) * ((ε : F) + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3) hε1
      · apply Units.ext
        simpa using eq_neg_of_add_eq_zero_left h3
    · rw [mem_torus0]
      refine ⟨Units.mk0 _ (div_ne_zero hd ha), ?_⟩
      rw [mk_eq_mk_iff_entries]
      refine ⟨Units.mk0 ((W : Matrix (Fin 2) (Fin 2) F) 0 0) ha, fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;> simp [hb, hc]
      field_simp
  ·
    left
    have ha : (W : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have h2 : (W : Matrix (Fin 2) (Fin 2) F) 0 0 * (1 - (u : F)) = 0 := by
        linear_combination e00
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3).symm hu1
    rw [ha] at hdet
    simp only [zero_mul, zero_sub, ne_eq, neg_eq_zero] at hdet
    have hb : (W : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := left_ne_zero_of_mul hdet
    have heu : (ε : F) * u = 1 := by
      apply mul_left_cancel₀ hb
      linear_combination -e01
    have hd : (W : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have h2 : (W : Matrix (Fin 2) (Fin 2) F) 1 1 * ((ε : F)⁻¹ - 1) = 0 := by
        linear_combination e11 + (W : Matrix (Fin 2) (Fin 2) F) 1 1 * heu
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hεinv1
    intro t ht
    obtain ⟨l, rfl⟩ := mem_torus0.mp ht
    rw [mul_inv_eq_iff_eq_mul, mk_dGL_inv, ← map_mul, ← map_mul, mk_eq_mk_iff_entries]
    refine ⟨l⁻¹, fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;> simp [ha, hd, gl2_mul_apply]
    field_simp

lemma torus0_sq_eq_one {l : Fˣ}
    (h : Matrix.ProjGenLinGroup.mk (dGL l) * Matrix.ProjGenLinGroup.mk (dGL l) = 1) :
    l = 1 ∨ l = -1 := by
  have h1 : Matrix.ProjGenLinGroup.mk (dGL (l * l)) = Matrix.ProjGenLinGroup.mk (dGL 1) := by
    rw [dGL_mul, map_mul, h, dGL_one, map_one]
  have h2 : l * l = 1 := mk_dGL_inj h1
  have h3 : ((l : F) - 1) * ((l : F) + 1) = 0 := by
    have : (l : F) * l = 1 := by simpa using congrArg Units.val h2
    linear_combination this
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact Or.inl (Units.ext (sub_eq_zero.mp h4))
  · right
    apply Units.ext
    simpa using eq_neg_of_add_eq_zero_left h4

lemma inf_eq_of_relIndex {G : Type*} [Group G] [Finite G] {T H I : Subgroup G}
    (hHT : H ≤ T) (hHI : H ≤ I) (hcard : Nat.card T = 2 * Nat.card H) (hTI : ¬ T ≤ I)
    (hI : I.index = 2) : T ⊓ I = H := by
  have : I.Normal := Subgroup.normal_of_index_eq_two hI
  have h1 : I.relIndex T ∣ 2 := hI ▸ Subgroup.relIndex_dvd_index_of_normal I T
  have h2 : I.relIndex T ≠ 1 := fun h => hTI (Subgroup.relIndex_eq_one.mp h)
  have h3 : I.relIndex T = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd h h2
    · exact h
  have h4 := Subgroup.relIndex_mul_card (H := I) (K := T)
  rw [h3, hcard] at h4
  have h5 : Nat.card (I ⊓ T : Subgroup G) = Nat.card H := by omega
  rw [inf_comm]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hHI hHT) (by omega)).symm

lemma commutator_le_of_index_two' {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2) :
    commutator A ≤ H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto

lemma eq_psl2Range_of_index_two [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {I' : Subgroup (PGL2 F)} (hI' : I'.index = 2) :
    I' = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  have hK := isOddPrimePower_of_odd hodd
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three F hK (by omega)
  have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤ I' := by
    rw [← hcomm]
    exact commutator_le_of_index_two' hI'
  have hidx := pgl2_psl2Range_index_eq_two F hK
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hI', hidx] at h1
  have h2 : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range.relIndex I' =
      1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle

lemma not_torus0_le_psl2Range [Finite F] (hodd : Odd (Nat.card F)) :
    ¬ torus0 F ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  intro hle
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro hchar
    have heven : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two hchar
    have hodd' : Odd (Fintype.card F) := by simpa [Nat.card_eq_fintype_card] using hodd
    exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero heven)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha IsSquare.zero
  have hmem := hle (mk_dGL_mem_torus0 (Units.mk0 a ha0))
  have hsq := (pgl2_mk_mem_psl2_range_iff_det_isSquare (dGL (Units.mk0 a ha0))).mp hmem
  apply ha
  simpa [Matrix.det_fin_two] using hsq

theorem cartan_core [Finite F] {M : Type*} [Group M] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (φ : M ≃* PGL2 F) (I : Subgroup M) (hI : I.index = 2)
    (Y : Subgroup M) (hYU : ∀ y, y ∈ Y ↔ φ y ∈ stdU F)
    (h : M) (hhord : orderOf h = (Nat.card F - 1) / 2) (hhI : h ∈ I)
    (hhT : φ h ∈ torus0 F)
    (w : M) (hw2 : w * w = 1) (hwH : w ∉ Subgroup.zpowers h) (hwinv : w * h * w⁻¹ = h⁻¹) :
    ∃ T : Subgroup M, IsCyclic T ∧ Nat.card T = Nat.card F - 1 ∧ Subgroup.zpowers h ≤ T ∧
      (∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧ (∀ s ∈ T, w * s * w⁻¹ = s⁻¹) ∧
      T ⊓ I = Subgroup.zpowers h := by
  have : Finite M := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨k, hk⟩ := hodd
  let T : Subgroup M := (torus0 F).map φ.symm.toMonoidHom
  have hmemT : ∀ s, s ∈ T ↔ φ s ∈ torus0 F := fun s => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hcyc : IsCyclic T :=
    (MulEquiv.subgroupMap φ.symm (torus0 F)).isCyclic.mp isCyclic_torus0
  have hcardT : Nat.card T = Nat.card F - 1 := by
    rw [← card_torus0 (F := F)]
    exact (Nat.card_congr (MulEquiv.subgroupMap φ.symm (torus0 F)).toEquiv).symm
  have hzT : Subgroup.zpowers h ≤ T := Subgroup.zpowers_le.mpr ((hmemT h).mpr hhT)
  have hnorm : ∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
    intro s hs y hy
    have := torus0_normalizes ((hmemT s).mp hs) ((hYU y).mp hy)
    exact (hYU _).mpr (by simpa using this)
  obtain ⟨ε, hε⟩ := mem_torus0.mp hhT
  have hε1 : ε ≠ 1 := by
    rintro rfl
    rw [dGL_one, map_one] at hε
    have : h = 1 := φ.injective (by rw [← hε, map_one])
    rw [this, orderOf_one] at hhord
    omega
  have hinv : ∀ s ∈ T, w * s * w⁻¹ = s⁻¹ := by
    have hw' : φ w * Matrix.ProjGenLinGroup.mk (dGL ε) * (φ w)⁻¹ =
        (Matrix.ProjGenLinGroup.mk (dGL ε))⁻¹ := by
      rw [hε]
      simpa using congrArg φ hwinv
    rcases inverts_torus0_or hε1 hw' with hB | ⟨hεm, hwT⟩
    · intro s hs
      apply φ.injective
      have := hB (φ s) ((hmemT s).mp hs)
      simpa using this
    · exfalso
      obtain ⟨l, hl⟩ := mem_torus0.mp hwT
      have hsq : Matrix.ProjGenLinGroup.mk (dGL l) * Matrix.ProjGenLinGroup.mk (dGL l) = 1 := by
        rw [hl, ← map_mul, hw2, map_one]
      rcases torus0_sq_eq_one hsq with rfl | rfl
      · apply hwH
        have : w = 1 := φ.injective (by rw [← hl, dGL_one, map_one, map_one])
        rw [this]
        exact one_mem _
      · apply hwH
        have : w = h := φ.injective (by rw [← hl, ← hε, hεm])
        rw [this]
        exact Subgroup.mem_zpowers h
  have hcard2 : Nat.card T = 2 * Nat.card (Subgroup.zpowers h) := by
    rw [hcardT, Nat.card_zpowers, hhord]
    omega
  have hTI : ¬ T ≤ I := by
    intro hTI
    have hI' : (I.map φ.toMonoidHom).index = 2 :=
      (Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective I).trans hI
    have heq := eq_psl2Range_of_index_two ⟨k, hk⟩ h5 hI'
    apply not_torus0_le_psl2Range ⟨k, hk⟩
    intro t ht
    have : φ.symm t ∈ I := hTI ((hmemT _).mpr (by simpa using ht))
    rw [← heq]
    exact ⟨φ.symm t, this, by simp⟩
  exact ⟨T, hcyc, hcardT, hzT, hnorm, hinv,
    inf_eq_of_relIndex hzT (Subgroup.zpowers_le.mpr hhI) hcard2 hTI hI⟩

end

end PGL2Cartan

open CFSG.GorensteinWalter PGL2Cartan

theorem pgl2_cartan {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    {M : Type} [Group M] (θ : M ≃* PGL2 F) (I : Subgroup M) (hI : I.index = 2)
    (Y H : Subgroup M) (hY : Nat.card ↥Y = Nat.card F) (hHI : H ≤ I) (hHc : IsCyclic ↥H)
    (hH : Nat.card ↥H = (Nat.card F - 1) / 2) (hHY : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (w : M) (hw2 : w * w = 1) (hwH : w ∉ H) (hwinv : ∀ h ∈ H, w * h * w⁻¹ = h⁻¹) :
    ∃ T : Subgroup M, IsCyclic ↥T ∧ Nat.card ↥T = Nat.card F - 1 ∧ H ≤ T ∧
      (∀ s ∈ T, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧ (∀ s ∈ T, w * s * w⁻¹ = s⁻¹) ∧ T ⊓ I = H := by
  obtain ⟨h, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHc
  have hhH : h ∈ Subgroup.zpowers h := Subgroup.mem_zpowers h
  have hhord : orderOf h = (Nat.card F - 1) / 2 := by
    rw [← Nat.card_zpowers]
    exact hH
  obtain ⟨φ, hφY, hφh⟩ := exists_std_iso hodd h5 θ Y hY h hhord (hHY h hhH)
  exact cartan_core hodd h5 φ I hI Y hφY h hhord (hHI hhH) hφh w hw2 hwH (hwinv h hhH)

end CFSG.GH74.GLS.SP.Local
