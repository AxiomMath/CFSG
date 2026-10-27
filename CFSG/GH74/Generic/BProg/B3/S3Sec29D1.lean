module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wDefs
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.GH74.GLS.Bg.Iii2.L41Comp
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Layer
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def Kg31e (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B : Subgroup G) (b : G) (D J : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
    Obs52 B b D J → HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd → ¬ B ≤ normalizer (J : Set G)

@[expose] def Kg21d : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
    ∀ V : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)), (∀ v ∈ V, v * v = 1) → 4 ≤ Nat.card ↥V →
      ∃ v ∈ V, v ≠ 1 ∧ ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, v = MulAut.conj s

structure SL2Data (X : Type*) [Group X] (z : X) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_comm : ∀ a : X, a * z = z * a
  center_eq : ∀ a : X, (∀ b : X, a * b = b * a) → a = 1 ∨ a = z
  invol_eq : ∀ a : X, a * a = 1 → a = 1 ∨ a = z
  exists_sq : ∃ t : X, t * t = z
  invert : ∀ t : X, t * t = z → ∃ s : X, s * s = z ∧ s * t * s⁻¹ = t⁻¹

namespace S3Sec29D1

theorem SL2Data.of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {z : Y} (h : SL2Data Y z) :
    SL2Data X (e.symm z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, h.z_sq, map_one]
  · intro h1
    exact h.z_ne (by simpa using congrArg e h1)
  · intro a
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h.z_comm (e a)
  · intro a ha
    rcases h.center_eq (e a) (fun b => by
      obtain ⟨b', rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, ha b']) with h1 | h1
    · left; exact e.injective (by simpa using h1)
    · right; rw [← h1]; simp
  · intro a ha
    rcases h.invol_eq (e a) (by rw [← map_mul, ha, map_one]) with h1 | h1
    · left; exact e.injective (by simpa using h1)
    · right; rw [← h1]; simp
  · obtain ⟨t, ht⟩ := h.exists_sq
    exact ⟨e.symm t, by rw [← map_mul, ht]⟩
  · intro t ht
    have ht' : e t * e t = z := by rw [← map_mul, ht]; simp
    obtain ⟨s, hss, hs⟩ := h.invert (e t) ht'
    refine ⟨e.symm s, by rw [← map_mul, hss], e.injective ?_⟩
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hs

section SL2

variable {F : Type} [Field F]

theorem sl2_invol (h2 : (2 : F) ≠ 0) (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : A * A = 1) :
    A = 1 ∨ A = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, ((A * A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j; rw [hA]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases hs : a + d = 0
  · exfalso
    have hd : d = -a := by linear_combination hs
    apply h2
    rw [hd] at hdet
    linear_combination -(e00 + hdet)
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have ha2 : a * a = 1 := by rw [hb] at e00; linear_combination e00
    have had : a * d = 1 := by rw [hb, hc] at hdet; linear_combination hdet
    have hda : d = a := by linear_combination a * had - d * ha2
    have ha : a = 1 ∨ a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination ha2
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases ha with ha | ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, hda, ha] at *
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, hda, ha] at *

theorem sl2_center (A : Matrix.SpecialLinearGroup (Fin 2) F) (hA : ∀ B, A * B = B * A) :
    A = 1 ∨ A = -1 := by
  have hmem : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.mpr fun B => (hA B).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  simp only [Fintype.card_fin] at hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.mp hr' with h | h
  · left
    apply Subtype.ext
    rw [← hrA, show r = 1 by linear_combination h]
    simp
  · right
    apply Subtype.ext
    rw [← hrA, show r = -1 by linear_combination h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sl2_neg_one_ne (h2 : (2 : F) ≠ 0) : (-1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq] at h00
  exact h2 (by linear_combination (-1 : F) * h00)

theorem exists_sq_add_sq_eq_neg_one [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ α β : F, α ^ 2 + β ^ 2 = -1 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hR : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd
  have hf : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by simp
  have hg : (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> simp
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hR
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

theorem sl2_conj_of_anticomm (t : Matrix.SpecialLinearGroup (Fin 2) F) (ht : t * t = -1)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) (htr : M 0 0 + M 1 1 = 0)
    (hanti : M * (t : Matrix (Fin 2) (Fin 2) F) = -(t : Matrix (Fin 2) (Fin 2) F) * M) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, s * s = -1 ∧ s * t * s⁻¹ = t⁻¹ := by
  let s : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hM⟩
  have hs : s * t = -t * s := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg]
    exact hanti)
  have htinv : t⁻¹ = -t := by rw [inv_eq_iff_mul_eq_one, mul_neg, ht, neg_neg]
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hM
  have hss : s * s = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    show M * M = -1
    have hd : M 1 1 = -M 0 0 := by linear_combination htr
    rw [hd] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd] <;>
      first | ring1 | linear_combination -hdet
  exact ⟨s, hss, by rw [htinv, hs, mul_inv_cancel_right]⟩

theorem sl2_invert [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    (t : Matrix.SpecialLinearGroup (Fin 2) F) (ht : t * t = -1) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) F, s * s = -1 ∧ s * t * s⁻¹ = t⁻¹ := by
  have hdet : (t : Matrix (Fin 2) (Fin 2) F).det = 1 := t.2
  rw [Matrix.det_fin_two] at hdet
  have e : ∀ i j, ((t * t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
      ((-1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j; rw [ht]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), neg_zero] at e00 e01 e10 e11
  set a := (t : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
  set b := (t : Matrix (Fin 2) (Fin 2) F) 0 1 with hb_def
  set c := (t : Matrix (Fin 2) (Fin 2) F) 1 0 with hc_def
  set d := (t : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
  have hd : d = -a := by
    by_contra hne
    have hs : a + d ≠ 0 := fun h => hne (by linear_combination h)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    rw [hb] at e00
    rw [hb, hc] at hdet
    exact hs (by linear_combination (-a) * hdet + d * e00)
  by_cases hc : c = 0
  · have ha2 : a * a = -1 := by rw [hc] at e00; linear_combination e00
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha2; exact h2 (by linear_combination (2 : F) * ha2)
    by_cases hb : b = 0
    · refine sl2_conj_of_anticomm t ht !![0, 1; -1, 0] (by simp [Matrix.det_fin_two]) (by simp) ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha_def, ← hb_def, ← hc_def, ← hd_def, hb, hc, hd]
    · refine sl2_conj_of_anticomm t ht !![1, b / a; -2 * a / b, -1] ?_ (by simp) ?_
      · simp only [Matrix.det_fin_two_of]
        field_simp
        ring
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha_def, ← hb_def, ← hc_def, ← hd_def, hc, hd] <;>
          field_simp <;> ring1
  · obtain ⟨α, β, hαβ⟩ := exists_sq_add_sq_eq_neg_one hodd
    refine sl2_conj_of_anticomm t ht
      !![α + a * β, (β - 2 * a * α - a ^ 2 * β) / c; c * β, -(α + a * β)] ?_ (by simp) ?_
    · simp only [Matrix.det_fin_two_of]
      field_simp
      linear_combination (-1 : F) * hαβ
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha_def, ← hb_def, ← hc_def, ← hd_def, hd] <;>
        field_simp <;> first | ring1 | linear_combination β * e00

theorem sl2Data_sl2 [Finite F] (hodd : Odd (Nat.card F)) :
    SL2Data (Matrix.SpecialLinearGroup (Fin 2) F) (-1) := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  refine ⟨by simp, sl2_neg_one_ne h2, fun a => by simp, fun a ha => sl2_center a ha,
    fun a ha => sl2_invol h2 a ha, ?_, fun t ht => sl2_invert h2 hodd t ht⟩
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨t, Subtype.ext ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  show !![(0 : F), 1; -1, 0] * !![0, 1; -1, 0] = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end SL2

theorem sl2Data_of_model {X : Type} [Group X] (h : HasSL2Model X Odd) : ∃ z : X, SL2Data X z := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F := e.trans (specialLinearGroupEquivStatedSL 2 F).symm
  exact ⟨_, SL2Data.of_equiv e' (sl2Data_sl2 hodd)⟩

end S3Sec29D1

end CFSG.GH74.Generic.BProg.B3
