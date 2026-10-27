module

public import CFSG.CharacterTheory.Semidihedral.MatrixCover

public section

namespace CFSG.Semidihedral.MatrixTorus

noncomputable section

open Matrix
open CFSG.Semidihedral.MatrixCoverData

universe u

variable (F : Type u) [Field F] (a : Fˣ)

@[expose] def Torus : Subgroup (SL F) :=
  (Subgroup.centralizer {J F a}).comap SpecialLinearGroup.toGL

@[expose] def torusMatrix (x y : F) : Matrix (Fin 2) (Fin 2) F :=
  !![x, -(a : F) * y; y, x]

theorem torusMatrix_det (x y : F) :
    (torusMatrix F a x y).det = x ^ 2 + (a : F) * y ^ 2 := by
  simp [torusMatrix, Matrix.det_fin_two]
  ring

theorem mem_torus_iff (X : SL F) : X ∈ Torus F a ↔
    (X : Matrix (Fin 2) (Fin 2) F) 0 1 =
      -(a : F) * (X : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
    (X : Matrix (Fin 2) (Fin 2) F) 1 1 =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  change SpecialLinearGroup.toGL X ∈ Subgroup.centralizer {J F a} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm := congrArg (fun V : GL2 F => (V : Matrix (Fin 2) (Fin 2) F)) h
    have h00 := congrArg (fun V : Matrix (Fin 2) (Fin 2) F => V 0 0) hm
    have h10 := congrArg (fun V : Matrix (Fin 2) (Fin 2) F => V 1 0) hm
    simp [J_matrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
    exact ⟨by simpa only [neg_mul] using h00, h10⟩
  · rintro ⟨h01, h11⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J_matrix, Matrix.mul_apply, Fin.sum_univ_two, h01, h11] <;> ring

theorem torus_coordinates (X : SL F) : X ∈ Torus F a ↔
    ∃ x y : F, (X : Matrix (Fin 2) (Fin 2) F) = torusMatrix F a x y ∧
      x ^ 2 + (a : F) * y ^ 2 = 1 := by
  constructor
  · intro hX
    obtain ⟨h01, h11⟩ := (mem_torus_iff F a X).mp hX
    let x := (X : Matrix (Fin 2) (Fin 2) F) 0 0
    let y := (X : Matrix (Fin 2) (Fin 2) F) 1 0
    have hm : (X : Matrix (Fin 2) (Fin 2) F) = torusMatrix F a x y := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [torusMatrix, x, y, h01, h11]
    refine ⟨x, y, hm, ?_⟩
    rw [← torusMatrix_det F a, ← hm]
    exact X.property
  · rintro ⟨x, y, hm, _⟩
    rw [mem_torus_iff, hm]
    simp [torusMatrix]

abbrev Quad := QuadraticAlgebra F (-(a : F)) 0

theorem quadratic_norm (x : Quad F a) : Algebra.norm F x = x.norm := by
  change (DistribSMul.toLinearMap F (Quad F a) x).det = x.norm
  exact QuadraticAlgebra.det_toLinearMap_eq_norm x

theorem quadratic_card [Finite F] : Nat.card (Quad F a) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-(a : F)) 0), Nat.card_prod]
  ring

@[expose] def quadraticMatrix : Quad F a →+*
    Matrix (Fin 2) (Fin 2) F where
  toFun w := torusMatrix F a w.re w.im
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [torusMatrix, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' w v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [torusMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [torusMatrix]
  map_add' w v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusMatrix, mul_add]

theorem quadraticMatrix_injective : Function.Injective (quadraticMatrix F a) := by
  intro w v h
  apply QuadraticAlgebra.ext
  · exact congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 0) h
  · exact congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 1 0) h

theorem quadraticMatrix_det (w : Quad F a) :
    (quadraticMatrix F a w).det = w.norm := by
  rw [show quadraticMatrix F a w = torusMatrix F a w.re w.im from rfl,
    torusMatrix_det, QuadraticAlgebra.norm_def]
  ring

@[expose] def normUnits : (Quad F a)ˣ →* Fˣ :=
  Units.map QuadraticAlgebra.norm

@[expose] def NormOne : Subgroup (Quad F a)ˣ := (normUnits F a).ker

theorem mem_normOne_iff (w : (Quad F a)ˣ) :
    w ∈ NormOne F a ↔ (w : Quad F a).norm = 1 := by
  change normUnits F a w = 1 ↔ _
  rw [Units.ext_iff]
  rfl

@[expose] def normOneToTorus : NormOne F a →* Torus F a where
  toFun w :=
    ⟨(⟨quadraticMatrix F a (w.val : Quad F a), by
      rw [quadraticMatrix_det]
      exact (mem_normOne_iff F a w.val).mp w.property⟩ : SL F), by
      apply (mem_torus_iff F a _).mpr
      simp [quadraticMatrix, torusMatrix]⟩
  map_one' := Subtype.ext (Subtype.ext (quadraticMatrix F a).map_one)
  map_mul' w v := Subtype.ext (Subtype.ext ((quadraticMatrix F a).map_mul _ _))

theorem normOneToTorus_injective : Function.Injective (normOneToTorus F a) := by
  intro w v h
  apply Subtype.ext
  apply Units.ext
  apply quadraticMatrix_injective F a
  exact congrArg (fun X : Torus F a => (X.val : Matrix (Fin 2) (Fin 2) F)) h

theorem normOneToTorus_surjective : Function.Surjective (normOneToTorus F a) := by
  intro X
  obtain ⟨x, y, hm, hn⟩ := (torus_coordinates F a X.val).mp X.property
  let w : Quad F a := ⟨x, y⟩
  have hwn : w.norm = 1 := by
    simp only [QuadraticAlgebra.norm_def, w, zero_mul]
    linear_combination hn
  have hwunit : IsUnit w := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by
    rw [hwn]
    exact isUnit_one)
  refine ⟨⟨hwunit.unit, (mem_normOne_iff F a _).mpr ?_⟩, ?_⟩
  · rw [hwunit.unit_spec]
    exact hwn
  · apply Subtype.ext
    apply Subtype.ext
    change quadraticMatrix F a (hwunit.unit : Quad F a) = _
    rw [hwunit.unit_spec]
    exact hm.symm

@[expose] def normOneEquivTorus : NormOne F a ≃* Torus F a :=
  MulEquiv.ofBijective (normOneToTorus F a)
    ⟨normOneToTorus_injective F a, normOneToTorus_surjective F a⟩

theorem normOneEquivTorus_matrix (w : NormOne F a) :
    ((normOneEquivTorus F a w).val : Matrix (Fin 2) (Fin 2) F) =
      torusMatrix F a (w.val : Quad F a).re (w.val : Quad F a).im := rfl

theorem nonsplit_norm_surjective [Finite F]
    (ha : ¬IsSquare (-(a : F))) : Function.Surjective (normUnits F a) := by
  let : Fact (¬IsSquare (-(a : F))) := ⟨ha⟩
  let : Finite (Quad F a) := Finite.of_equiv (F × F)
    (QuadraticAlgebra.equivProd (-(a : F)) 0).symm
  have hnorm : (QuadraticAlgebra.norm : Quad F a →* F) = Algebra.norm F := by
    ext w
    exact (quadratic_norm F a w).symm
  rw [normUnits, hnorm]
  exact FiniteField.unitsMap_norm_surjective F (Quad F a)

theorem nonsplit_torus_cyclic [Finite F]
    (ha : ¬IsSquare (-(a : F))) : IsCyclic (Torus F a) := by
  let : Fact (¬IsSquare (-(a : F))) := ⟨ha⟩
  let : Finite (Quad F a) := Finite.of_equiv (F × F)
    (QuadraticAlgebra.equivProd (-(a : F)) 0).symm
  exact (normOneEquivTorus F a).isCyclic.mp inferInstance

theorem nonsplit_torus_card [Finite F]
    (ha : ¬IsSquare (-(a : F))) : Nat.card (Torus F a) = Nat.card F + 1 := by
  let : Fact (¬IsSquare (-(a : F))) := ⟨ha⟩
  let : Finite (Quad F a) := Finite.of_equiv (F × F)
    (QuadraticAlgebra.equivProd (-(a : F)) 0).symm
  have h := Subgroup.card_ker_mul_card_of_surjective (nonsplit_norm_surjective F a ha)
  rw [Nat.card_units, Nat.card_units, quadratic_card] at h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hfact : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    have hsub : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel (by omega)
    have hsq : Nat.card F ^ 2 - 1 + 1 = Nat.card F ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  rw [hfact] at h
  have hc : Nat.card (NormOne F a) = Nat.card F + 1 :=
    Nat.eq_of_mul_eq_mul_right (by omega) h
  rw [← Nat.card_congr (normOneEquivTorus F a).toEquiv]
  exact hc

@[expose] def quadraticEval (b : F) (hb : b ^ 2 = -(a : F)) : Quad F a →+* F where
  toFun w := w.re + b * w.im
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' w v := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero]
    linear_combination -w.im * v.im * hb
  map_zero' := by simp
  map_add' w v := by simp; ring

theorem quadratic_norm_split (b : F) (hb : b ^ 2 = -(a : F)) (w : Quad F a) :
    w.norm = (w.re + b * w.im) * (w.re - b * w.im) := by
  rw [QuadraticAlgebra.norm_def]
  linear_combination w.im ^ 2 * hb

@[expose] def splitNormEval (b : F) (hb : b ^ 2 = -(a : F)) : NormOne F a →* Fˣ :=
  (Units.map (quadraticEval F a b hb).toMonoidHom).comp (NormOne F a).subtype

theorem splitNormEval_coe (b : F) (hb : b ^ 2 = -(a : F)) (w : NormOne F a) :
    (splitNormEval F a b hb w : F) =
      (w.val : Quad F a).re + b * (w.val : Quad F a).im := rfl

theorem splitNormEval_injective (h2 : (2 : F) ≠ 0)
    (b : F) (hb : b ^ 2 = -(a : F)) : Function.Injective (splitNormEval F a b hb) := by
  have hb0 : b ≠ 0 := by
    intro hz
    have ha0 := a.ne_zero
    rw [hz, zero_pow (by decide)] at hb
    exact ha0 (neg_eq_zero.mp hb.symm)
  intro w v h
  have hp := congrArg (fun t : Fˣ => (t : F)) h
  rw [splitNormEval_coe, splitNormEval_coe] at hp
  have hwm := (mem_normOne_iff F a w.val).mp w.property
  have hvm := (mem_normOne_iff F a v.val).mp v.property
  rw [quadratic_norm_split F a b hb] at hwm hvm
  have hminus : (w.val : Quad F a).re - b * (w.val : Quad F a).im =
      (v.val : Quad F a).re - b * (v.val : Quad F a).im := by
    have hnonzero : (w.val : Quad F a).re + b * (w.val : Quad F a).im ≠ 0 :=
      (splitNormEval F a b hb w).ne_zero
    apply mul_left_cancel₀ hnonzero
    rw [hwm, hp, hvm]
  apply Subtype.ext
  apply Units.ext
  apply QuadraticAlgebra.ext
  · apply mul_left_cancel₀ h2
    linear_combination hp + hminus
  · apply mul_left_cancel₀ (mul_ne_zero h2 hb0)
    linear_combination hp - hminus

theorem splitNormEval_surjective (h2 : (2 : F) ≠ 0)
    (b : F) (hb : b ^ 2 = -(a : F)) : Function.Surjective (splitNormEval F a b hb) := by
  have hb0 : b ≠ 0 := by
    intro hz
    have ha0 := a.ne_zero
    rw [hz, zero_pow (by decide)] at hb
    exact ha0 (neg_eq_zero.mp hb.symm)
  intro t
  let w : Quad F a := ⟨((t : F) + (t⁻¹ : Fˣ)) / 2,
    ((t : F) - (t⁻¹ : Fˣ)) / (2 * b)⟩
  have hp : w.re + b * w.im = (t : F) := by
    dsimp [w]
    field_simp [h2, hb0]
    ring
  have hm : w.re - b * w.im = (t⁻¹ : Fˣ) := by
    dsimp [w]
    field_simp [h2, hb0]
    ring
  have hn : w.norm = 1 := by
    rw [quadratic_norm_split F a b hb, hp, hm]
    exact t.val_inv
  have hu : IsUnit w := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by
    rw [hn]
    exact isUnit_one)
  refine ⟨⟨hu.unit, (mem_normOne_iff F a _).mpr ?_⟩, ?_⟩
  · rw [hu.unit_spec]
    exact hn
  · apply Units.ext
    rw [splitNormEval_coe, hu.unit_spec]
    exact hp

@[expose] def splitNormEquiv (h2 : (2 : F) ≠ 0)
    (b : F) (hb : b ^ 2 = -(a : F)) : NormOne F a ≃* Fˣ :=
  MulEquiv.ofBijective (splitNormEval F a b hb)
    ⟨splitNormEval_injective F a h2 b hb, splitNormEval_surjective F a h2 b hb⟩

theorem split_torus_cyclic [Finite F] (h2 : (2 : F) ≠ 0)
    (ha : IsSquare (-(a : F))) : IsCyclic (Torus F a) := by
  obtain ⟨b, hb⟩ := ha
  have he := splitNormEquiv F a h2 b (by simpa only [pow_two] using hb.symm)
  have : IsCyclic (NormOne F a) := he.isCyclic.mpr inferInstance
  exact (normOneEquivTorus F a).isCyclic.mp this

theorem split_torus_card [Finite F] (h2 : (2 : F) ≠ 0)
    (ha : IsSquare (-(a : F))) : Nat.card (Torus F a) = Nat.card F - 1 := by
  obtain ⟨b, hb⟩ := ha
  rw [← Nat.card_congr (normOneEquivTorus F a).toEquiv,
    Nat.card_congr (splitNormEquiv F a h2 b
      (by simpa only [pow_two] using hb.symm)).toEquiv, Nat.card_units]

theorem odd_prime_power_card [Finite F] (hodd : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpF, n, hp, hcard⟩ := FiniteField.card' F
  have hcard' : Nat.card F = p ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hpodd : Odd p := by
    apply hp.odd_of_ne_two
    intro he
    have hc : ringChar F = 2 := by
      let : CharP F p := hpF
      simpa only [he] using ringChar.eq F p
    have heven := FiniteField.even_card_of_char_two hc
    have ho := Nat.odd_iff.mp hodd
    rw [Nat.card_eq_fintype_card] at ho
    omega
  exact ⟨p, n, hp, hpodd, n.property, hcard'⟩

theorem neg_coefficient_square_iff [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : IsSquare (-(a : F)) ↔ Nat.card F % 4 = 3 := by
  let : Fintype F := Fintype.ofFinite F
  have hF := odd_prime_power_card F hodd
  constructor
  · intro hs
    by_contra hq
    have hn : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by
      simpa only [Nat.card_eq_fintype_card] using hq)
    have hsq : IsSquare (a : F) := by simpa using hn.mul hs
    exact ha ((SemilinearOuterQuotient.isSquare_unit_iff a).mpr hsq)
  · intro hq
    have hn : ¬IsSquare (-1 : Fˣ) := by
      intro hs
      have hsF := (SemilinearOuterQuotient.isSquare_unit_iff (-1 : Fˣ)).mp hs
      have hh := FiniteField.isSquare_neg_one_iff.mp hsF
      apply hh
      simpa only [Nat.card_eq_fintype_card] using hq
    have hs := ProjectiveNonsquareInvolutions.nonsquare_quotient_square F hF (-1 : Fˣ) a hn ha
    have hsF := (SemilinearOuterQuotient.isSquare_unit_iff (a / (-1 : Fˣ))).mp hs
    simpa only [Units.val_div_eq_div_val, Units.val_neg, Units.val_one,
      div_neg, div_one] using hsF

@[expose] def torusSize (q : ℕ) : ℕ := if q % 4 = 1 then q + 1 else q - 1

theorem torus_cyclic [Finite F] (hodd : Odd (Nat.card F))
    (_ha : ¬IsSquare a) : IsCyclic (Torus F a) := by
  by_cases hs : IsSquare (-(a : F))
  · exact split_torus_cyclic F a (OddFieldSL2.two_ne_zero_of_odd_card F hodd) hs
  · exact nonsplit_torus_cyclic F a hs

theorem torus_card [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : Nat.card (Torus F a) = torusSize (Nat.card F) := by
  have hmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd)
  rcases hmod with hq | hq
  · have hs : ¬IsSquare (-(a : F)) := by
      rw [neg_coefficient_square_iff F a hodd ha]
      omega
    rw [nonsplit_torus_card F a hs, torusSize, ite_eq_left hq]
  · have hs := (neg_coefficient_square_iff F a hodd ha).mpr hq
    rw [split_torus_card F a (OddFieldSL2.two_ne_zero_of_odd_card F hodd) hs,
      torusSize, ite_eq_right (by omega)]

theorem torusSize_mod_four {q : ℕ} (hq : Odd q) : torusSize q % 4 = 2 := by
  have hmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq)
  dsimp [torusSize]
  split_ifs <;> omega

@[expose] def z : Torus F a := ⟨OddFieldSL2.minusIdentity F, by
  rw [mem_torus_iff]
  simp [OddFieldSL2.minusIdentity]⟩

theorem z_orderOf [Finite F] (hodd : Odd (Nat.card F)) : orderOf (z F a) = 2 := by
  rw [Subgroup.orderOf_mk]
  exact OddFieldSL2.minusIdentity_orderOf F (OddFieldSL2.two_ne_zero_of_odd_card F hodd)

theorem torus_unique_involution [Finite F] (hodd : Odd (Nat.card F))
    (X : Torus F a) : orderOf X = 2 ↔ X = z F a := by
  rw [Subgroup.orderOf_mk, OddFieldSL2.orderOf_eq_two_iff F
    (OddFieldSL2.two_ne_zero_of_odd_card F hodd)]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

noncomputable instance torusCommGroup : CommGroup (Torus F a) :=
  (normOneEquivTorus F a).symm.toMonoidHom.commGroupOfInjective
    (normOneEquivTorus F a).symm.injective

@[expose] def W : Subgroup (Torus F a) :=
  (powMonoidHom (torusSize (Nat.card F) / 2)).ker

theorem mem_W_iff (X : Torus F a) :
    X ∈ W F a ↔ X ^ (torusSize (Nat.card F) / 2) = 1 := Iff.rfl

theorem W_characteristic : (W F a).Characteristic := by
  apply Subgroup.characteristic_iff_comap_eq.mpr
  intro phi
  ext X
  change (phi X) ^ (torusSize (Nat.card F) / 2) = 1 ↔
    X ^ (torusSize (Nat.card F) / 2) = 1
  rw [← map_pow]
  constructor
  · intro h
    apply phi.injective
    rw [h, phi.map_one]
  · intro h
    rw [h, phi.map_one]

theorem W_cyclic [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : IsCyclic (W F a) := by
  let : IsCyclic (Torus F a) := torus_cyclic F a hodd ha
  exact inferInstance

theorem torusSize_half_odd {q : ℕ} (hq : Odd q) : Odd (torusSize q / 2) := by
  apply Nat.odd_iff.mpr
  have hm := torusSize_mod_four hq
  omega

theorem torusSize_two_mul_half {q : ℕ} (hq : Odd q) :
    torusSize q = 2 * (torusSize q / 2) := by
  have hm := torusSize_mod_four hq
  omega

theorem W_card [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : Nat.card (W F a) = torusSize (Nat.card F) / 2 := by
  let : IsCyclic (Torus F a) := torus_cyclic F a hodd ha
  rw [W, IsCyclic.card_powMonoidHom_ker, torus_card F a hodd ha]
  exact Nat.gcd_eq_right ⟨2, (torusSize_two_mul_half hodd).trans (Nat.mul_comm _ _)⟩

theorem mem_W_iff_odd_order [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) (X : Torus F a) : X ∈ W F a ↔ Odd (orderOf X) := by
  have hd := torusSize_half_odd hodd
  constructor
  · intro hX
    exact hd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ((mem_W_iff F a X).mp hX))
  · intro hX
    apply (mem_W_iff F a X).mpr
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hc := orderOf_dvd_natCard X
    rw [torus_card F a hodd ha, torusSize_two_mul_half hodd] at hc
    exact hX.coprime_two_right.dvd_of_dvd_mul_left hc

theorem torus_internal_direct [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : (Subgroup.zpowers (z F a)).IsComplement' (W F a) := by
  apply Subgroup.isComplement'_of_coprime
  · rw [Nat.card_zpowers, z_orderOf F a hodd, W_card F a hodd ha,
      torus_card F a hodd ha]
    exact (torusSize_two_mul_half hodd).symm
  · rw [Nat.card_zpowers, z_orderOf F a hodd, W_card F a hodd ha]
    exact (torusSize_half_odd hodd).coprime_two_left

@[expose] def torusDirectEquiv [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) : Subgroup.zpowers (z F a) × W F a ≃* Torus F a :=
  OddFieldLift.internalDirectEquiv _ _ (by
    rw [Subgroup.center_eq_top]
    exact le_top) (torus_internal_direct F a hodd ha)

theorem torusDirectEquiv_apply [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) (x : Subgroup.zpowers (z F a) × W F a) :
    torusDirectEquiv F a hodd ha x = (x.1 : Torus F a) * x.2 := rfl

theorem torus_field_invariant (sigma : F ≃+* F)
    (ha : sigma (a : F) = a) (X : Torus F a) :
    MatrixCover.slFieldEquiv F sigma X.val ∈ Torus F a := by
  obtain ⟨h01, h11⟩ := (mem_torus_iff F a X.val).mp X.property
  apply (mem_torus_iff F a _).mpr
  constructor
  · change sigma ((X.val : Matrix (Fin 2) (Fin 2) F) 0 1) =
      -(a : F) * sigma ((X.val : Matrix (Fin 2) (Fin 2) F) 1 0)
    rw [h01, map_mul, map_neg, ha]
  · exact congrArg sigma h11

@[expose] def torusFieldEquiv (sigma : F ≃+* F)
    (ha : sigma (a : F) = a) : MulAut (Torus F a) where
  toFun X := ⟨MatrixCover.slFieldEquiv F sigma X.val,
    torus_field_invariant F a sigma ha X⟩
  invFun X := ⟨MatrixCover.slFieldEquiv F sigma.symm X.val,
    torus_field_invariant F a sigma.symm (by
      apply sigma.injective
      simpa only [sigma.apply_symm_apply] using ha.symm) X⟩
  left_inv X := Subtype.ext ((MatrixCover.slFieldEquiv F sigma).symm_apply_apply X.val)
  right_inv X := Subtype.ext ((MatrixCover.slFieldEquiv F sigma).apply_symm_apply X.val)
  map_mul' X Y := Subtype.ext ((MatrixCover.slFieldEquiv F sigma).map_mul X.val Y.val)

theorem torusFieldEquiv_matrix (sigma : F ≃+* F)
    (ha : sigma (a : F) = a) (X : Torus F a) :
    ((torusFieldEquiv F a sigma ha X).val : Matrix (Fin 2) (Fin 2) F) =
      sigma.toRingHom.mapMatrix (X.val : Matrix (Fin 2) (Fin 2) F) := rfl

theorem torusFieldEquiv_z (sigma : F ≃+* F) (ha : sigma (a : F) = a) :
    torusFieldEquiv F a sigma ha (z F a) = z F a := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusFieldEquiv, MatrixCover.slFieldEquiv, z, OddFieldSL2.minusIdentity]

theorem W_field_invariant (sigma : F ≃+* F) (ha : sigma (a : F) = a)
    (X : W F a) : torusFieldEquiv F a sigma ha X.val ∈ W F a := by
  have : (W F a).Characteristic := W_characteristic F a
  exact Subgroup.characteristic_iff_le_comap.mp this (torusFieldEquiv F a sigma ha) X.property

theorem beta_fixed_iff (X : SL F) : beta F a X = X ↔ X ∈ Torus F a := by
  change beta F a X = X ↔ SpecialLinearGroup.toGL X ∈ Subgroup.centralizer {J F a}
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm : SpecialLinearGroup.toGL X * J F a = J F a * SpecialLinearGroup.toGL X := by
      have ht := congrArg SpecialLinearGroup.toGL h
      rw [beta, slConjugation_toGL] at ht
      have hv := congrArg (fun g : GL2 F => g * J F a) ht
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hv.symm
    exact hm
  · intro hX
    apply SpecialLinearGroup.toGL_injective
    change SpecialLinearGroup.toGL (slConjugation F (J F a) X) = _
    rw [slConjugation_toGL, ← hX, mul_assoc, mul_inv_cancel, mul_one]

theorem action_torus_trivial (e : C2) (X : Torus F a) :
    MatrixCoverData.action F a e X.val = X.val := by
  have he := exponent_lt_two e
  interval_cases he' : exponent e
  · change ((beta F a) ^ exponent e) X.val = X.val
    simp [he']
  · change ((beta F a) ^ exponent e) X.val = X.val
    simpa only [he', pow_one] using (beta_fixed_iff F a X.val).mpr X.property

theorem matrix_centralizer_u_iff (x : M F a) :
    x ∈ Subgroup.centralizer {u F a} ↔ x.left ∈ Torus F a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hl := congrArg (fun y : M F a => y.left) h
    have hb : beta F a x.left = x.left := by
      simpa only [u_pair, SemidirectProduct.mul_left, map_one, mul_one, one_mul,
        MatrixCoverData.action_one] using hl.symm
    exact (beta_fixed_iff F a x.left).mp hb
  · intro hx
    apply SemidirectProduct.ext
    · simpa only [u_pair, SemidirectProduct.mul_left, map_one, mul_one, one_mul,
        MatrixCoverData.action_one] using ((beta_fixed_iff F a x.left).mpr hx).symm
    · exact mul_comm _ _


section Semilinear

variable (A : Subgroup (F ≃+* F)) (b : (MatrixCover.FixedField F A)ˣ)

@[expose] def slInH : SL F →* MatrixCover.MatrixFieldModel F A b :=
  (SemidirectProduct.inl : M F (MatrixCover.fixedUnit F A b) →*
    MatrixCover.MatrixFieldModel F A b).comp
      (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b))

theorem slInH_pair (X : SL F) :
    slInH F A b X = ⟨⟨X, 1⟩, 1⟩ := rfl

@[expose] def uInH : MatrixCover.MatrixFieldModel F A b :=
  SemidirectProduct.inl (MatrixCoverData.u F (MatrixCover.fixedUnit F A b))

@[expose] def zInH : MatrixCover.MatrixFieldModel F A b :=
  slInH F A b (OddFieldSL2.minusIdentity F)

@[expose] def fieldInH : A →* MatrixCover.MatrixFieldModel F A b :=
  SemidirectProduct.inr

theorem field_fixes_u (sigma : A) :
    MatrixCover.matrixFieldAction F A b sigma
      (MatrixCoverData.u F (MatrixCover.fixedUnit F A b)) =
      MatrixCoverData.u F (MatrixCover.fixedUnit F A b) := by
  apply SemidirectProduct.ext
  · exact map_one _
  · rfl

theorem semilinear_centralizer_u_iff (g : MatrixCover.MatrixFieldModel F A b) :
    g ∈ Subgroup.centralizer {uInH F A b} ↔
      g.left.left ∈ Torus F (MatrixCover.fixedUnit F A b) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hm : g.left ∈ Subgroup.centralizer
        {MatrixCoverData.u F (MatrixCover.fixedUnit F A b)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hl := congrArg (fun x : MatrixCover.MatrixFieldModel F A b => x.left) hg
      change g.left * MatrixCover.matrixFieldAction F A b g.right
        (MatrixCoverData.u F (MatrixCover.fixedUnit F A b)) =
          MatrixCoverData.u F (MatrixCover.fixedUnit F A b) *
            MatrixCover.matrixFieldAction F A b 1 g.left at hl
      simpa only [field_fixes_u, map_one, MulAut.one_apply] using hl
    exact (matrix_centralizer_u_iff F (MatrixCover.fixedUnit F A b) g.left).mp hm
  · intro hg
    have hm := (matrix_centralizer_u_iff F (MatrixCover.fixedUnit F A b) g.left).mpr hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hm
    apply SemidirectProduct.ext
    · change g.left * MatrixCover.matrixFieldAction F A b g.right
        (MatrixCoverData.u F (MatrixCover.fixedUnit F A b)) =
          MatrixCoverData.u F (MatrixCover.fixedUnit F A b) *
            MatrixCover.matrixFieldAction F A b 1 g.left
      simpa only [field_fixes_u, map_one, MulAut.one_apply] using hm
    · simp [uInH]

@[expose] def torusAction : A →* MulAut (Torus F (MatrixCover.fixedUnit F A b)) where
  toFun sigma := torusFieldEquiv F (MatrixCover.fixedUnit F A b) sigma
    ((b : MatrixCover.FixedField F A).property sigma)
  map_one' := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    exact DFunLike.congr_fun (MatrixCover.slFieldEquiv_mul F sigma tau) X.val

@[expose] def WFieldEquiv (sigma : F ≃+* F) (ha : sigma (a : F) = a) :
    MulAut (W F a) where
  toFun X := ⟨torusFieldEquiv F a sigma ha X.val, W_field_invariant F a sigma ha X⟩
  invFun X := ⟨(torusFieldEquiv F a sigma ha).symm X.val, by
    have hchar := W_characteristic F a
    exact Subgroup.characteristic_iff_le_comap.mp hchar
      (torusFieldEquiv F a sigma ha).symm X.property⟩
  left_inv X := Subtype.ext ((torusFieldEquiv F a sigma ha).symm_apply_apply X.val)
  right_inv X := Subtype.ext ((torusFieldEquiv F a sigma ha).apply_symm_apply X.val)
  map_mul' X Y := Subtype.ext ((torusFieldEquiv F a sigma ha).map_mul X.val Y.val)

@[expose] def WAction : A →* MulAut (W F (MatrixCover.fixedUnit F A b)) where
  toFun sigma := WFieldEquiv F (MatrixCover.fixedUnit F A b) sigma
    ((b : MatrixCover.FixedField F A).property sigma)
  map_one' := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    exact DFunLike.congr_fun (torusAction F A b).map_one X.val
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro X
    apply Subtype.ext
    exact DFunLike.congr_fun ((torusAction F A b).map_mul sigma tau) X.val

abbrev WFieldProduct :=
  SemidirectProduct (W F (MatrixCover.fixedUnit F A b)) A (WAction F A b)

@[expose] def WInM : W F a →* M F a :=
  (MatrixCoverData.inclusion F a).comp ((Torus F a).subtype.comp (W F a).subtype)

@[expose] def oddFactor : WFieldProduct F A b →* MatrixCover.MatrixFieldModel F A b :=
  SemidirectProduct.map (WInM F (MatrixCover.fixedUnit F A b)) (MonoidHom.id A) (by
    intro sigma
    apply MonoidHom.ext
    intro X
    apply SemidirectProduct.ext <;> rfl)

theorem oddFactor_pair (x : WFieldProduct F A b) :
    oddFactor F A b x = ⟨⟨x.left.val.val, 1⟩, x.right⟩ := rfl

theorem oddFactor_injective : Function.Injective (oddFactor F A b) := by
  intro x y h
  apply SemidirectProduct.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.left.left) h
  · exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.right) h

theorem oddFactor_mem_centralizer (x : WFieldProduct F A b) :
    oddFactor F A b x ∈ Subgroup.centralizer {uInH F A b} :=
  (semilinear_centralizer_u_iff F A b _).mpr x.left.val.property

@[expose] def torusC2Map : Torus F a × C2 →* M F a where
  toFun x := ⟨x.1.val, x.2⟩
  map_one' := rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · exact (congrArg (fun X : SL F => x.1.val * X)
        (action_torus_trivial F a x.2 y.1)).symm
    · rfl

@[expose] def fourFactor :
    Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2 →*
      MatrixCover.MatrixFieldModel F A b :=
  (SemidirectProduct.inl : M F (MatrixCover.fixedUnit F A b) →*
    MatrixCover.MatrixFieldModel F A b).comp
      ((torusC2Map F (MatrixCover.fixedUnit F A b)).comp
        ((Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b))).subtype.prodMap
          (MonoidHom.id C2)))

theorem fourFactor_pair
    (x : Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2) :
    fourFactor F A b x = ⟨⟨x.1.val.val, x.2⟩, 1⟩ := rfl

theorem fourFactor_injective : Function.Injective (fourFactor F A b) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.left.left) h
  · exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.left.right) h


theorem C2_cases (e : C2) : e = 1 ∨ e = Multiplicative.ofAdd (1 : ZMod 2) := by
  fin_cases e <;> first | exact Or.inl rfl | exact Or.inr rfl

@[expose] def V0 : Subgroup (MatrixCover.MatrixFieldModel F A b) :=
  Subgroup.zpowers (zInH F A b) ⊔ Subgroup.zpowers (uInH F A b)

theorem fourFactor_range : (fourFactor F A b).range = V0 F A b := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.1.property
    have hleft : slInH F A b x.1.val.val ∈ V0 F A b := by
      apply (show Subgroup.zpowers (zInH F A b) ≤ V0 F A b from le_sup_left)
      apply Subgroup.mem_zpowers_iff.mpr
      refine ⟨k, ?_⟩
      have he := congrArg (fun t : Torus F (MatrixCover.fixedUnit F A b) =>
        slInH F A b t.val) hk
      simpa only [Subgroup.coe_zpow, map_zpow, z, zInH] using he
    have hright : (SemidirectProduct.inl
        (SemidirectProduct.inr x.2) : MatrixCover.MatrixFieldModel F A b) ∈ V0 F A b := by
      rcases C2_cases x.2 with h | h
      · simp [h]
      · rw [h]
        exact (show Subgroup.zpowers (uInH F A b) ≤ V0 F A b from le_sup_right)
          (Subgroup.mem_zpowers (uInH F A b))
    have he : fourFactor F A b x = slInH F A b x.1.val.val *
        SemidirectProduct.inl (SemidirectProduct.inr x.2) := by
      apply SemidirectProduct.ext
      · exact (SemidirectProduct.mk_eq_inl_mul_inr x.2 x.1.val.val)
      · change (1 : A) = 1 * 1
        simp
    rw [he]
    exact (V0 F A b).mul_mem hleft hright
  · apply sup_le
    · apply Subgroup.zpowers_le.mpr
      exact ⟨(⟨z F (MatrixCover.fixedUnit F A b), Subgroup.mem_zpowers _⟩, 1), rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨(1, Multiplicative.ofAdd (1 : ZMod 2)), rfl⟩

theorem fourFactor_mem_V0
    (x : Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2) :
    fourFactor F A b x ∈ V0 F A b := by
  rw [← fourFactor_range]
  exact ⟨x, rfl⟩

@[expose] def fourFactorEquiv :
    Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2 ≃* V0 F A b :=
  (MonoidHom.ofInjective (fourFactor_injective F A b)).trans
    (MulEquiv.subgroupCongr (fourFactor_range F A b))

theorem V0_le_centralizer : V0 F A b ≤ Subgroup.centralizer {uInH F A b} := by
  rw [← fourFactor_range]
  rintro g ⟨x, rfl⟩
  exact (semilinear_centralizer_u_iff F A b _).mpr x.1.val.property

theorem field_fixes_z (sigma : A) :
    MatrixCover.matrixFieldAction F A b sigma
      (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b)
        (OddFieldSL2.minusIdentity F)) =
      MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b)
        (OddFieldSL2.minusIdentity F) := by
  apply SemidirectProduct.ext
  · exact congrArg Subtype.val (torusFieldEquiv_z F (MatrixCover.fixedUnit F A b) sigma
      ((b : MatrixCover.FixedField F A).property sigma))
  · rfl

theorem zInH_mem_center : zInH F A b ∈ Subgroup.center (MatrixCover.MatrixFieldModel F A b) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply SemidirectProduct.ext
  · change g.left * MatrixCover.matrixFieldAction F A b g.right
        (MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b)
          (OddFieldSL2.minusIdentity F)) =
      MatrixCoverData.inclusion F (MatrixCover.fixedUnit F A b)
        (OddFieldSL2.minusIdentity F) * MatrixCover.matrixFieldAction F A b 1 g.left
    rw [field_fixes_z, map_one, MulAut.one_apply]
    apply SemidirectProduct.ext
    · change g.left.left * MatrixCoverData.action F (MatrixCover.fixedUnit F A b)
        g.left.right (OddFieldSL2.minusIdentity F) =
      OddFieldSL2.minusIdentity F * MatrixCoverData.action F (MatrixCover.fixedUnit F A b)
        1 g.left.left
      rw [show MatrixCoverData.action F (MatrixCover.fixedUnit F A b) g.left.right
          (OddFieldSL2.minusIdentity F) = OddFieldSL2.minusIdentity F from
            action_torus_trivial F (MatrixCover.fixedUnit F A b) g.left.right (z F _),
        map_one, MulAut.one_apply]
      exact Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F) g.left.left
    · change g.left.right * 1 = 1 * g.left.right
      simp
  · simp [zInH, slInH]

@[expose] def centralizerProductHom :
    (Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2) × WFieldProduct F A b →*
      Subgroup.centralizer {uInH F A b} where
  toFun x := ⟨fourFactor F A b x.1 * oddFactor F A b x.2,
    (Subgroup.centralizer {uInH F A b}).mul_mem
      (V0_le_centralizer F A b (fourFactor_mem_V0 F A b x.1))
      (oddFactor_mem_centralizer F A b x.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change fourFactor F A b (x.1 * y.1) * oddFactor F A b (x.2 * y.2) =
      (fourFactor F A b x.1 * oddFactor F A b x.2) *
        (fourFactor F A b y.1 * oddFactor F A b y.2)
    rw [map_mul, map_mul]
    have hc : Commute (oddFactor F A b x.2) (fourFactor F A b y.1) := by
      have hV : V0 F A b ≤ Subgroup.centralizer {oddFactor F A b x.2} := by
        apply sup_le
        · apply Subgroup.zpowers_le.mpr
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_center_iff.mp (zInH_mem_center F A b) _).symm
        · apply Subgroup.zpowers_le.mpr
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.mp
            (oddFactor_mem_centralizer F A b x.2)).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        (hV (fourFactor_mem_V0 F A b y.1))).symm
    exact (Commute.mul_mul_mul_comm hc _ _).symm

theorem centralizerProductHom_coordinates
    (x : (Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2) ×
      WFieldProduct F A b) :
    (centralizerProductHom F A b x).val =
      ⟨⟨x.1.1.val.val * x.2.left.val.val, x.1.2⟩, x.2.right⟩ := by
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · exact congrArg (fun X : SL F => x.1.1.val.val * X)
        (action_torus_trivial F (MatrixCover.fixedUnit F A b) x.1.2 x.2.left.val)
    · simp [centralizerProductHom, fourFactor_pair, oddFactor_pair]
  · simp [centralizerProductHom, fourFactor_pair, oddFactor_pair]

theorem centralizerProductHom_bijective [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    Function.Bijective (centralizerProductHom F A b) := by
  constructor
  · intro x y h
    have hg := congrArg Subtype.val h
    rw [centralizerProductHom_coordinates, centralizerProductHom_coordinates] at hg
    have he := congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.left.right) hg
    have hs := congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.right) hg
    have ht : x.1.1.val * x.2.left.val = y.1.1.val * y.2.left.val := by
      apply Subtype.ext
      exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g.left.left) hg
    have hpair : (x.1.1, x.2.left) = (y.1.1, y.2.left) :=
      (torus_internal_direct F (MatrixCover.fixedUnit F A b) hodd hb).1
        (show (fun p : Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) ×
          W F (MatrixCover.fixedUnit F A b) => p.1.val * p.2.val) (x.1.1, x.2.left) =
            (fun p : Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) ×
              W F (MatrixCover.fixedUnit F A b) => p.1.val * p.2.val) (y.1.1, y.2.left)
                from ht)
    have hz : x.1.1 = y.1.1 := congrArg (fun p :
      Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × W F (MatrixCover.fixedUnit F A b)
        => p.1) hpair
    have hw : x.2.left = y.2.left := congrArg (fun p :
      Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × W F (MatrixCover.fixedUnit F A b)
        => p.2) hpair
    apply Prod.ext
    · apply Prod.ext
      · exact hz
      · exact he
    · apply SemidirectProduct.ext
      · exact hw
      · exact hs
  · intro g
    let t : Torus F (MatrixCover.fixedUnit F A b) :=
      ⟨g.val.left.left, (semilinear_centralizer_u_iff F A b _).mp g.property⟩
    obtain ⟨x, hx⟩ := (torus_internal_direct F (MatrixCover.fixedUnit F A b) hodd hb).2 t
    refine ⟨((x.1, g.val.left.right), ⟨x.2, g.val.right⟩), ?_⟩
    apply Subtype.ext
    rw [centralizerProductHom_coordinates]
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · exact congrArg Subtype.val hx
      · rfl
    · rfl

@[expose] def centralizerProductEquiv [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    (Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) × C2) ×
      WFieldProduct F A b ≃* Subgroup.centralizer {uInH F A b} :=
  MulEquiv.ofBijective (centralizerProductHom F A b)
    (centralizerProductHom_bijective F A b hodd hb)


@[expose] def V0EquivC2 [Finite F] (hodd : Odd (Nat.card F)) : V0 F A b ≃* C2 × C2 := by
  let z0 : Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) :=
    ⟨z F (MatrixCover.fixedUnit F A b), Subgroup.mem_zpowers _⟩
  let e : C2 ≃* Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b)) :=
    zmodMulEquivOfGenerator (g := z0) (by
      intro t
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp t.property
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩) (by
        rw [Nat.card_zpowers, z_orderOf F _ hodd])
  exact (fourFactorEquiv F A b).symm.trans (e.symm.prodCongr (MulEquiv.refl C2))

theorem V0_card [Finite F] (hodd : Odd (Nat.card F)) : Nat.card (V0 F A b) = 4 := by
  rw [Nat.card_congr (V0EquivC2 F A b hodd).toEquiv, Nat.card_prod]
  norm_num [C2, Nat.card_eq_fintype_card]

@[expose] def centralizerExactEquiv [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    V0 F A b × WFieldProduct F A b ≃* Subgroup.centralizer {uInH F A b} :=
  ((fourFactorEquiv F A b).symm.prodCongr (MulEquiv.refl _)).trans
    (centralizerProductEquiv F A b hodd hb)

theorem centralizerExactEquiv_apply [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) (x : V0 F A b × WFieldProduct F A b) :
    (centralizerExactEquiv F A b hodd hb x).val = x.1.val * oddFactor F A b x.2 := by
  have he := congrArg Subtype.val ((fourFactorEquiv F A b).apply_symm_apply x.1)
  change fourFactor F A b ((fourFactorEquiv F A b).symm x.1) * oddFactor F A b x.2 = _
  exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => g * oddFactor F A b x.2) he

@[expose] def OddSemilinear : Subgroup (MatrixCover.MatrixFieldModel F A b) :=
  (oddFactor F A b).range

theorem OddSemilinear_le_centralizer :
    OddSemilinear F A b ≤ Subgroup.centralizer {uInH F A b} := by
  rintro g ⟨x, rfl⟩
  exact oddFactor_mem_centralizer F A b x

@[expose] def oddFactorEquiv : WFieldProduct F A b ≃* OddSemilinear F A b :=
  MonoidHom.ofInjective (oddFactor_injective F A b)

@[expose] def centralizerInternalEquiv [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ×
      (OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ≃*
        Subgroup.centralizer {uInH F A b} :=
  ((Subgroup.subgroupOfEquivOfLe (V0_le_centralizer F A b)).prodCongr
    ((Subgroup.subgroupOfEquivOfLe (OddSemilinear_le_centralizer F A b)).trans
      (oddFactorEquiv F A b).symm)).trans (centralizerExactEquiv F A b hodd hb)

theorem centralizerInternalEquiv_apply [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b))
    (x : (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ×
      (OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b})) :
    centralizerInternalEquiv F A b hodd hb x = x.1.val * x.2.val := by
  apply Subtype.ext
  change (centralizerExactEquiv F A b hodd hb
    ((Subgroup.subgroupOfEquivOfLe (V0_le_centralizer F A b)) x.1,
      (oddFactorEquiv F A b).symm
        ((Subgroup.subgroupOfEquivOfLe (OddSemilinear_le_centralizer F A b)) x.2))).val = _
  rw [centralizerExactEquiv_apply]
  have he := congrArg Subtype.val ((oddFactorEquiv F A b).apply_symm_apply
    ((Subgroup.subgroupOfEquivOfLe (OddSemilinear_le_centralizer F A b)) x.2))
  exact congrArg (fun g : MatrixCover.MatrixFieldModel F A b => x.1.val.val * g) he

theorem centralizer_internal_complement [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    ((V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b})).IsComplement'
      ((OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b})) := by
  change Function.Bijective (fun x :
    (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ×
      (OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) => x.1.val * x.2.val)
  have he : (fun x :
    (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ×
      (OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) => x.1.val * x.2.val) =
        centralizerInternalEquiv F A b hodd hb :=
    funext (fun x => (centralizerInternalEquiv_apply F A b hodd hb x).symm)
  rw [he]
  exact (centralizerInternalEquiv F A b hodd hb).bijective

theorem V0_central_in_centralizer :
    (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ≤
      Subgroup.center (Subgroup.centralizer {uInH F A b}) := by
  intro v hv
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  have hV : V0 F A b ≤ Subgroup.centralizer {g.val} := by
    apply sup_le
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp (zInH_mem_center F A b) g.val).symm
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp g.property).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hV hv)).symm

theorem centralizer_factorization_iff [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) (g : MatrixCover.MatrixFieldModel F A b) :
    g ∈ Subgroup.centralizer {uInH F A b} ↔
      ∃ w : W F (MatrixCover.fixedUnit F A b), ∃ v : V0 F A b, ∃ sigma : A,
        g = slInH F A b w.val.val * v.val * fieldInH F A b sigma := by
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := (centralizerExactEquiv F A b hodd hb).surjective ⟨g, hg⟩
    refine ⟨x.2.left, x.1, x.2.right, ?_⟩
    have he := congrArg Subtype.val hx
    rw [centralizerExactEquiv_apply] at he
    have hc : Commute x.1.val (slInH F A b x.2.left.val.val) := by
      have hw : slInH F A b x.2.left.val.val ∈ Subgroup.centralizer {uInH F A b} :=
        (semilinear_centralizer_u_iff F A b _).mpr x.2.left.val.property
      have hv := V0_central_in_centralizer F A b
        (show (⟨x.1.val, V0_le_centralizer F A b x.1.property⟩ :
          Subgroup.centralizer {uInH F A b}) ∈
            (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) from x.1.property)
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hv ⟨_, hw⟩)).symm
    have ho : oddFactor F A b x.2 =
        slInH F A b x.2.left.val.val * fieldInH F A b x.2.right := by
      apply SemidirectProduct.ext
      · simp [oddFactor_pair, slInH_pair, fieldInH]
      · simp [oddFactor_pair, slInH_pair, fieldInH]
    rw [ho] at he
    change x.1.val * (slInH F A b x.2.left.val.val * fieldInH F A b x.2.right) = g at he
    rw [← he, ← mul_assoc, hc.eq]
  · rintro ⟨w, v, sigma, rfl⟩
    apply (Subgroup.centralizer {uInH F A b}).mul_mem
    · exact (Subgroup.centralizer {uInH F A b}).mul_mem
        ((semilinear_centralizer_u_iff F A b _).mpr w.val.property)
        (V0_le_centralizer F A b v.property)
    · exact (semilinear_centralizer_u_iff F A b _).mpr (Torus F _).one_mem

theorem semilinear_card [Finite F] :
    Nat.card (MatrixCover.MatrixFieldModel F A b) =
      2 * Nat.card A * Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    Nat.card_congr (SemidirectProduct.equivProd (N := SL F)), Nat.card_prod,
    CFSG.GorensteinWalter.sl2_card_formula]
  have hc : Nat.card C2 = 2 := by norm_num [C2, Nat.card_eq_fintype_card]
  rw [hc]
  ring

theorem semilinear_centralizer_card [Finite F] (hodd : Odd (Nat.card F))
    (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    Nat.card (Subgroup.centralizer {uInH F A b}) =
      2 * Nat.card A * torusSize (Nat.card F) := by
  rw [← Nat.card_congr (centralizerExactEquiv F A b hodd hb).toEquiv, Nat.card_prod,
    V0_card F A b hodd, Nat.card_congr (SemidirectProduct.equivProd
      (N := W F (MatrixCover.fixedUnit F A b))), Nat.card_prod, W_card F _ hodd hb]
  nth_rw 2 [torusSize_two_mul_half hodd]
  ring


theorem nonsquare_matrix_semilinear_involution_centralizer_fixed [Finite F]
    (hodd : Odd (Nat.card F)) (hb : ¬IsSquare (MatrixCover.fixedUnit F A b)) :
    (∀ X : SL F, X ∈ Torus F (MatrixCover.fixedUnit F A b) ↔
      ∃ x y : F, (X : Matrix (Fin 2) (Fin 2) F) =
        torusMatrix F (MatrixCover.fixedUnit F A b) x y ∧
          x ^ 2 + (MatrixCover.fixedUnit F A b : F) * y ^ 2 = 1) ∧
    IsCyclic (Torus F (MatrixCover.fixedUnit F A b)) ∧
    Nat.card (Torus F (MatrixCover.fixedUnit F A b)) = torusSize (Nat.card F) ∧
    (∀ X : Torus F (MatrixCover.fixedUnit F A b), orderOf X = 2 ↔
      X = z F (MatrixCover.fixedUnit F A b)) ∧
    (W F (MatrixCover.fixedUnit F A b)).Characteristic ∧
    IsCyclic (W F (MatrixCover.fixedUnit F A b)) ∧
    Nat.card (W F (MatrixCover.fixedUnit F A b)) = torusSize (Nat.card F) / 2 ∧
    (∀ X : Torus F (MatrixCover.fixedUnit F A b),
      X ∈ W F (MatrixCover.fixedUnit F A b) ↔ Odd (orderOf X)) ∧
    (∀ sigma : A, ∀ X : W F (MatrixCover.fixedUnit F A b),
      torusAction F A b sigma X.val ∈ W F (MatrixCover.fixedUnit F A b)) ∧
    (Subgroup.zpowers (z F (MatrixCover.fixedUnit F A b))).IsComplement'
      (W F (MatrixCover.fixedUnit F A b)) ∧
    (∀ sigma : A, ∀ X : W F (MatrixCover.fixedUnit F A b),
      ((WAction F A b sigma X).val.val : Matrix (Fin 2) (Fin 2) F) =
        (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F)) ∧
    Nonempty (V0 F A b ≃* C2 × C2) ∧
    (V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b}) ≤
      Subgroup.center (Subgroup.centralizer {uInH F A b}) ∧
    ((V0 F A b).subgroupOf (Subgroup.centralizer {uInH F A b})).IsComplement'
      ((OddSemilinear F A b).subgroupOf (Subgroup.centralizer {uInH F A b})) ∧
    (∃ e : V0 F A b × WFieldProduct F A b ≃* Subgroup.centralizer {uInH F A b},
      ∀ x, (e x).val = x.1.val * oddFactor F A b x.2) ∧
    (∀ g : MatrixCover.MatrixFieldModel F A b,
      g ∈ Subgroup.centralizer {uInH F A b} ↔
        ∃ w : W F (MatrixCover.fixedUnit F A b), ∃ v : V0 F A b, ∃ sigma : A,
          g = slInH F A b w.val.val * v.val * fieldInH F A b sigma) ∧
    Nat.card (MatrixCover.MatrixFieldModel F A b) =
      2 * Nat.card A * Nat.card F * (Nat.card F ^ 2 - 1) ∧
    Nat.card (Subgroup.centralizer {uInH F A b}) =
      2 * Nat.card A * torusSize (Nat.card F) := by
  refine ⟨torus_coordinates F _, torus_cyclic F _ hodd hb, torus_card F _ hodd hb,
    torus_unique_involution F _ hodd, W_characteristic F _, W_cyclic F _ hodd hb,
    W_card F _ hodd hb, mem_W_iff_odd_order F _ hodd hb, ?_,
    torus_internal_direct F _ hodd hb, ?_, ⟨V0EquivC2 F A b hodd⟩,
    V0_central_in_centralizer F A b, centralizer_internal_complement F A b hodd hb,
    ⟨centralizerExactEquiv F A b hodd hb, centralizerExactEquiv_apply F A b hodd hb⟩,
    centralizer_factorization_iff F A b hodd hb, semilinear_card F A b,
    semilinear_centralizer_card F A b hodd hb⟩
  · intro sigma X
    exact W_field_invariant F _ sigma ((b : MatrixCover.FixedField F A).property sigma) X
  · intro sigma X
    rfl

end Semilinear


section OriginalCoefficient

variable (A : Subgroup (F ≃+* F)) (hfix : ∀ sigma : A, (sigma : F ≃+* F) (a : F) = a)

@[expose] def originalCoefficient : (MatrixCover.FixedField F A)ˣ :=
  Units.mk0 (⟨(a : F), hfix⟩ : MatrixCover.FixedField F A) (by
    intro h
    exact a.ne_zero (congrArg Subtype.val h))

theorem originalCoefficient_literal :
    MatrixCover.fixedUnit F A (originalCoefficient F a A hfix) = a := Units.ext rfl

@[expose] def originalFieldAction : A →* MulAut (M F a) where
  toFun sigma := MatrixCover.matrixFieldEquiv F sigma a (hfix sigma)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · apply Subtype.ext
      ext i j
      rfl
    · rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro x
    apply SemidirectProduct.ext
    · exact DFunLike.congr_fun (MatrixCover.slFieldEquiv_mul F sigma tau) x.left
    · rfl

abbrev OriginalH := SemidirectProduct (M F a) A (originalFieldAction F a A hfix)

theorem originalFieldAction_pair (sigma : A) (x : M F a) :
    originalFieldAction F a A hfix sigma x =
      ⟨SpecialLinearGroup.map (sigma : F ≃+* F).toRingHom x.left, x.right⟩ := rfl



@[expose] def originalModelEquiv :
    MatrixCover.MatrixFieldModel F A (originalCoefficient F a A hfix) ≃* OriginalH F a A hfix where
  toFun g := ⟨⟨g.left.left, g.left.right⟩, g.right⟩
  invFun g := ⟨⟨g.left.left, g.left.right⟩, g.right⟩
  left_inv g := by apply SemidirectProduct.ext; apply SemidirectProduct.ext <;> rfl; rfl
  right_inv g := by apply SemidirectProduct.ext; apply SemidirectProduct.ext <;> rfl; rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · change g.left.left * MatrixCoverData.action F
          (MatrixCover.fixedUnit F A (originalCoefficient F a A hfix)) g.left.right
            (MatrixCover.slFieldEquiv F (g.right : F ≃+* F) h.left.left) =
          g.left.left * MatrixCoverData.action F a g.left.right
            (MatrixCover.slFieldEquiv F (g.right : F ≃+* F) h.left.left)
        have he : MatrixCoverData.action F
            (MatrixCover.fixedUnit F A (originalCoefficient F a A hfix)) =
              MatrixCoverData.action F a :=
          congrArg (MatrixCoverData.action F) (originalCoefficient_literal F a A hfix)
        exact congrArg (fun phi : C2 →* MulAut (SL F) =>
          g.left.left * phi g.left.right
            (MatrixCover.slFieldEquiv F (g.right : F ≃+* F) h.left.left)) he
      · rfl
    · rfl

theorem originalModelEquiv_coordinates
    (g : MatrixCover.MatrixFieldModel F A (originalCoefficient F a A hfix)) :
    (originalModelEquiv F a A hfix g).left.left = g.left.left ∧
    (originalModelEquiv F a A hfix g).left.right = g.left.right ∧
    (originalModelEquiv F a A hfix g).right = g.right := ⟨rfl, rfl, rfl⟩


@[expose] def originalSlInH : SL F →* OriginalH F a A hfix :=
  (SemidirectProduct.inl : M F a →* OriginalH F a A hfix).comp (MatrixCoverData.inclusion F a)

@[expose] def originalU : OriginalH F a A hfix := SemidirectProduct.inl (MatrixCoverData.u F a)

@[expose] def originalZ : OriginalH F a A hfix := originalSlInH F a A hfix (OddFieldSL2.minusIdentity F)

@[expose] def originalFieldInH : A →* OriginalH F a A hfix := SemidirectProduct.inr

@[expose] def originalV0 : Subgroup (OriginalH F a A hfix) :=
  Subgroup.zpowers (originalZ F a A hfix) ⊔ Subgroup.zpowers (originalU F a A hfix)

theorem originalModelEquiv_u :
    originalModelEquiv F a A hfix (uInH F A (originalCoefficient F a A hfix)) =
      originalU F a A hfix := rfl

theorem originalModelEquiv_z :
    originalModelEquiv F a A hfix (zInH F A (originalCoefficient F a A hfix)) =
      originalZ F a A hfix := rfl

theorem originalModelEquiv_sl (X : SL F) :
    originalModelEquiv F a A hfix (slInH F A (originalCoefficient F a A hfix) X) =
      originalSlInH F a A hfix X := rfl

theorem originalModelEquiv_field (sigma : A) :
    originalModelEquiv F a A hfix (fieldInH F A (originalCoefficient F a A hfix) sigma) =
      originalFieldInH F a A hfix sigma := rfl

theorem originalV0_map :
    (V0 F A (originalCoefficient F a A hfix)).map (originalModelEquiv F a A hfix).toMonoidHom =
      originalV0 F a A hfix := by
  rw [V0, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

@[expose] def originalCentralizerEquiv :
    Subgroup.centralizer {uInH F A (originalCoefficient F a A hfix)} ≃*
      Subgroup.centralizer {originalU F a A hfix} where
  toFun g := ⟨originalModelEquiv F a A hfix g.val, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := congrArg (originalModelEquiv F a A hfix)
      (Subgroup.mem_centralizer_singleton_iff.mp g.property)
    simpa only [map_mul, originalModelEquiv_u] using he⟩
  invFun g := ⟨(originalModelEquiv F a A hfix).symm g.val, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply (originalModelEquiv F a A hfix).injective
    simpa only [map_mul, MulEquiv.apply_symm_apply, originalModelEquiv_u] using
      Subgroup.mem_centralizer_singleton_iff.mp g.property⟩
  left_inv g := Subtype.ext ((originalModelEquiv F a A hfix).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((originalModelEquiv F a A hfix).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((originalModelEquiv F a A hfix).map_mul g.val h.val)

@[expose] def originalFourEquiv : V0 F A (originalCoefficient F a A hfix) ≃* originalV0 F a A hfix :=
  (Subgroup.equivMapOfInjective (V0 F A (originalCoefficient F a A hfix))
    (originalModelEquiv F a A hfix).toMonoidHom (originalModelEquiv F a A hfix).injective).trans
      (MulEquiv.subgroupCongr (originalV0_map F a A hfix))

@[expose] def originalOddSemilinear : Subgroup (OriginalH F a A hfix) :=
  (OddSemilinear F A (originalCoefficient F a A hfix)).map
    (originalModelEquiv F a A hfix).toMonoidHom

@[expose] def originalOddEquiv :
    OddSemilinear F A (originalCoefficient F a A hfix) ≃* originalOddSemilinear F a A hfix :=
  Subgroup.equivMapOfInjective _ (originalModelEquiv F a A hfix).toMonoidHom
    (originalModelEquiv F a A hfix).injective

@[expose] def originalDirectEquiv [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) :
    originalV0 F a A hfix × originalOddSemilinear F a A hfix ≃*
      Subgroup.centralizer {originalU F a A hfix} :=
  ((originalFourEquiv F a A hfix).symm.prodCongr
    ((originalOddEquiv F a A hfix).symm.trans
      (oddFactorEquiv F A (originalCoefficient F a A hfix)).symm)).trans
    ((centralizerExactEquiv F A (originalCoefficient F a A hfix) hodd (by
      rw [originalCoefficient_literal]
      exact ha)).trans (originalCentralizerEquiv F a A hfix))

theorem originalDirectEquiv_apply [Finite F] (hodd : Odd (Nat.card F))
    (ha : ¬IsSquare a) (x : originalV0 F a A hfix × originalOddSemilinear F a A hfix) :
    (originalDirectEquiv F a A hfix hodd ha x).val = x.1.val * x.2.val := by
  let v := (originalFourEquiv F a A hfix).symm x.1
  let w := (originalOddEquiv F a A hfix).symm x.2
  change originalModelEquiv F a A hfix
    (centralizerExactEquiv F A (originalCoefficient F a A hfix) hodd _
      (v, (oddFactorEquiv F A (originalCoefficient F a A hfix)).symm w)).val = _
  rw [centralizerExactEquiv_apply, map_mul]
  have hv := congrArg Subtype.val ((originalFourEquiv F a A hfix).apply_symm_apply x.1)
  have hw := congrArg Subtype.val ((originalOddEquiv F a A hfix).apply_symm_apply x.2)
  have he := congrArg Subtype.val ((oddFactorEquiv F A (originalCoefficient F a A hfix)).apply_symm_apply w)
  change originalModelEquiv F a A hfix v.val = x.1.val at hv
  change originalModelEquiv F a A hfix w.val = x.2.val at hw
  change oddFactor F A (originalCoefficient F a A hfix)
    ((oddFactorEquiv F A (originalCoefficient F a A hfix)).symm w) = w.val at he
  rw [he, hv, hw]


theorem nonsquare_matrix_semilinear_involution_centralizer [Finite F]
    (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    (∀ X : SL F, X ∈ Torus F a ↔ ∃ x y : F,
      (X : Matrix (Fin 2) (Fin 2) F) = torusMatrix F a x y ∧ x ^ 2 + (a : F) * y ^ 2 = 1) ∧
    IsCyclic (Torus F a) ∧ Nat.card (Torus F a) = torusSize (Nat.card F) ∧
    (∀ X : Torus F a, orderOf X = 2 ↔ X = z F a) ∧
    (W F a).Characteristic ∧ IsCyclic (W F a) ∧
    Nat.card (W F a) = torusSize (Nat.card F) / 2 ∧
    (∀ X : Torus F a, X ∈ W F a ↔ Odd (orderOf X)) ∧
    (∀ sigma : A, ∀ X : W F a, torusFieldEquiv F a sigma (hfix sigma) X.val ∈ W F a) ∧
    (Subgroup.zpowers (z F a)).IsComplement' (W F a) ∧
    (∀ sigma : A, ∀ X : W F a,
      ((WFieldEquiv F a sigma (hfix sigma) X).val.val : Matrix (Fin 2) (Fin 2) F) =
        (sigma : F ≃+* F).toRingHom.mapMatrix (X.val.val : Matrix (Fin 2) (Fin 2) F)) ∧
    Nonempty (originalV0 F a A hfix ≃* C2 × C2) ∧
    (∃ e : originalV0 F a A hfix × originalOddSemilinear F a A hfix ≃*
      Subgroup.centralizer {originalU F a A hfix}, ∀ x, (e x).val = x.1.val * x.2.val) ∧
    Nonempty (originalOddSemilinear F a A hfix ≃*
      SemidirectProduct (W F a) A
        ({ toFun := fun sigma => WFieldEquiv F a sigma (hfix sigma)
           map_one' := by
             apply MulEquiv.ext
             intro X
             apply Subtype.ext
             apply Subtype.ext
             apply Subtype.ext
             ext i j
             rfl
           map_mul' := by
             intro sigma tau
             apply MulEquiv.ext
             intro X
             apply Subtype.ext
             apply Subtype.ext
             exact DFunLike.congr_fun (MatrixCover.slFieldEquiv_mul F sigma tau) X.val.val } :
           A →* MulAut (W F a))) ∧
    Nat.card (OriginalH F a A hfix) =
      2 * Nat.card A * Nat.card F * (Nat.card F ^ 2 - 1) ∧
    Nat.card (Subgroup.centralizer {originalU F a A hfix}) =
      2 * Nat.card A * torusSize (Nat.card F) := by
  have hb : ¬IsSquare (MatrixCover.fixedUnit F A (originalCoefficient F a A hfix)) := by
    rw [originalCoefficient_literal]
    exact ha
  refine ⟨torus_coordinates F a, torus_cyclic F a hodd ha, torus_card F a hodd ha,
    torus_unique_involution F a hodd, W_characteristic F a, W_cyclic F a hodd ha,
    W_card F a hodd ha, mem_W_iff_odd_order F a hodd ha,
    (fun sigma X => W_field_invariant F a sigma (hfix sigma) X),
    torus_internal_direct F a hodd ha, (fun _ _ => rfl),
    ⟨(originalFourEquiv F a A hfix).symm.trans
      (V0EquivC2 F A (originalCoefficient F a A hfix) hodd)⟩,
    ⟨originalDirectEquiv F a A hfix hodd ha, originalDirectEquiv_apply F a A hfix hodd ha⟩,
    ?_, ?_, ?_⟩
  · have h := originalCoefficient_literal F a A hfix
    let e := (originalOddEquiv F a A hfix).symm.trans
      (oddFactorEquiv F A (originalCoefficient F a A hfix)).symm
    exact ⟨e.trans (SemidirectProduct.congr
      (by rw [h]; exact MulEquiv.refl _) (MulEquiv.refl A) (by
        intro sigma
        apply MulEquiv.ext
        intro X
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        rfl))⟩
  · rw [← Nat.card_congr (originalModelEquiv F a A hfix).toEquiv]
    exact semilinear_card F A (originalCoefficient F a A hfix)
  · rw [← Nat.card_congr (originalCentralizerEquiv F a A hfix).toEquiv]
    exact semilinear_centralizer_card F A (originalCoefficient F a A hfix) hodd hb

end OriginalCoefficient

end

end CFSG.Semidihedral.MatrixTorus
