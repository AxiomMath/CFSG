module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddRootCommutators
public import CFSG.LieType.Chevalley.AllRootWeylConjugation

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  MvPolynomial
open scoped commutatorElement

theorem pinnedX_commutator_row
    {τ : Tag} {R : Type} [CommRing R] {r : PairRow} (hr : r ∈ pairTable τ) (x y : R) :
    pinnedX τ R (orbitCertRoot τ r.1) x * pinnedX τ R (orbitCertRoot τ r.2.1) y *
        pinnedX τ R (orbitCertRoot τ r.1) (-x) * pinnedX τ R (orbitCertRoot τ r.2.1) (-y) =
      (r.2.2.2.map fun f => pinnedX τ R (orbitCertRoot τ f.2.2.1)
        ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hid⟩ := (rank_two_pair_certificate τ).2 r hr
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![x, y] with hg
  have hg0 : g (X 0) = x := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = y := eval₂Hom_X' _ _ _
  have hL := (((baseChange_pinnedX g (orbitCertRoot τ r.1) (X 0)).mul
    (baseChange_pinnedX g (orbitCertRoot τ r.2.1) (X 1))).mul
    (baseChange_pinnedX g (orbitCertRoot τ r.1) (-X 0))).mul
    (baseChange_pinnedX g (orbitCertRoot τ r.2.1) (-X 1))
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hid] at hL
  have hR := baseChange_prod_map_pinnedX g r.2.2.2 (fun f => orbitCertRoot τ f.2.2.1)
    (fun f => ((f.2.2.2 : MvPolynomial (Fin 2) ℤ) * X 0 ^ f.1 * X 1 ^ f.2.1))
  simp only [map_mul, map_neg, hg0, hg1, map_pow, map_intCast] at hL hR
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact hL.unique hR

abbrev gR : Fin Tag.G2.rank → ℤ := ![0, 1]
abbrev gA : Fin Tag.G2.rank → ℤ := ![1, 0]
abbrev gU : Fin Tag.G2.rank → ℤ := ![1, 1]
abbrev gV : Fin Tag.G2.rank → ℤ := ![1, 2]
abbrev gB : Fin Tag.G2.rank → ℤ := ![1, 3]
abbrev gC : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem pos6 : orbitCertRoot .G2 6 = gR := by funext i; fin_cases i <;> rfl
theorem pos7 : orbitCertRoot .G2 7 = gA := by funext i; fin_cases i <;> rfl
theorem pos8 : orbitCertRoot .G2 8 = gU := by funext i; fin_cases i <;> rfl
theorem pos9 : orbitCertRoot .G2 9 = gV := by funext i; fin_cases i <;> rfl
theorem pos10 : orbitCertRoot .G2 10 = gB := by funext i; fin_cases i <;> rfl
theorem pos11 : orbitCertRoot .G2 11 = gC := by funext i; fin_cases i <;> rfl

section Rows

variable
    {K : Type} [Field K]

theorem comm_r_a (s t : K) :
    ⁅pinnedX .G2 K gR s, pinnedX .G2 K gA t⁆ =
      pinnedX .G2 K gU (-(s * t)) * (pinnedX .G2 K gV (s ^ 2 * t) *
        (pinnedX .G2 K gB (s ^ 3 * t) * pinnedX .G2 K gC (2 * s ^ 3 * t ^ 2))) := by
  have h := pinnedX_commutator_row (τ := .G2) (R := K)
    (r := (6, 7, 12, [(1, 1, 8, -1), (2, 1, 9, 1), (3, 1, 10, 1), (3, 2, 11, 2)])) (by decide) s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [pos6, pos7, pos8, pos9, pos10, pos11] at h
  simp only [Int.cast_neg, Int.cast_one, Int.cast_ofNat, pow_one, one_mul, neg_mul] at h
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact h

theorem comm_r_u (s t : K) :
    ⁅pinnedX .G2 K gR s, pinnedX .G2 K gU t⁆ =
      pinnedX .G2 K gV (-(2 * s * t)) * (pinnedX .G2 K gC (-(3 * s * t ^ 2)) *
        pinnedX .G2 K gB (-(3 * s ^ 2 * t))) := by
  have h := pinnedX_commutator_row (τ := .G2) (R := K)
    (r := (6, 8, 12, [(1, 1, 9, -2), (1, 2, 11, -3), (2, 1, 10, -3)])) (by decide) s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [pos6, pos8, pos9, pos10, pos11] at h
  simp only [Int.cast_neg, Int.cast_ofNat, pow_one, neg_mul] at h
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact h

theorem comm_r_v (s t : K) :
    ⁅pinnedX .G2 K gR s, pinnedX .G2 K gV t⁆ = pinnedX .G2 K gB (3 * s * t) := by
  have h := pinnedX_commutator_row (τ := .G2) (R := K)
    (r := (6, 9, 12, [(1, 1, 10, 3)])) (by decide) s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [pos6, pos9, pos10] at h
  simp only [Int.cast_ofNat, pow_one] at h
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact h

theorem comm_a_b (s t : K) :
    ⁅pinnedX .G2 K gA s, pinnedX .G2 K gB t⁆ = pinnedX .G2 K gC (s * t) := by
  have h := pinnedX_commutator_row (τ := .G2) (R := K)
    (r := (7, 10, 12, [(1, 1, 11, 1)])) (by decide) s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [pos7, pos10, pos11] at h
  simp only [Int.cast_one, pow_one, one_mul] at h
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
  exact h

theorem commute_a_u (s t : K) : Commute (pinnedX .G2 K gA s) (pinnedX .G2 K gU t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((7, 8, 12, []) : PairRow)) (by decide) rfl 1 (α := gA) (β := gU)
    (by rw [one_smul]; exact pos7) (by rw [one_smul]; exact pos8) s t
  exact this

theorem commute_a_v (s t : K) : Commute (pinnedX .G2 K gA s) (pinnedX .G2 K gV t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((7, 9, 12, []) : PairRow)) (by decide) rfl 1 (α := gA) (β := gV)
    (by rw [one_smul]; exact pos7) (by rw [one_smul]; exact pos9) s t
  exact this

theorem commute_a_c (s t : K) : Commute (pinnedX .G2 K gA s) (pinnedX .G2 K gC t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((7, 11, 12, []) : PairRow)) (by decide) rfl 1 (α := gA) (β := gC)
    (by rw [one_smul]; exact pos7) (by rw [one_smul]; exact pos11) s t
  exact this

theorem commute_r_b (s t : K) : Commute (pinnedX .G2 K gR s) (pinnedX .G2 K gB t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 10, 12, []) : PairRow)) (by decide) rfl 1 (α := gR) (β := gB)
    (by rw [one_smul]; exact pos6) (by rw [one_smul]; exact pos10) s t
  exact this

theorem commute_r_c (s t : K) : Commute (pinnedX .G2 K gR s) (pinnedX .G2 K gC t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 11, 12, []) : PairRow)) (by decide) rfl 1 (α := gR) (β := gC)
    (by rw [one_smul]; exact pos6) (by rw [one_smul]; exact pos11) s t
  exact this

abbrev sA : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
abbrev sR : WeylGroup .G2 := simple .G2 ⟨1, by decide⟩

theorem sA_r : sA • gR = gU := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sA_v : sA • gV = gV := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sA_b : sA • gB = gC := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sA_c : sA • gC = gB := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sRA_r : (sR * sA) • gR = gV := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sRA_b : (sR * sA) • gB = gC := by
  rw [mul_smul, simple_smul, simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sARA_r : (sA * sR * sA) • gR = gV := by
  rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)
theorem sARA_b : (sA * sR * sA) • gB = gB := by
  rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)
theorem sR_a : sR • gA = gB := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
theorem sR_c : sR • gC = gC := by
  rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)

theorem commute_u_b (s t : K) : Commute (pinnedX .G2 K gU s) (pinnedX .G2 K gB t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 11, 12, []) : PairRow)) (by decide) rfl sA (α := gU) (β := gB)
    (by rw [pos6]; exact sA_r) (by rw [pos11]; exact sA_c) s t
  exact this

theorem commute_u_c (s t : K) : Commute (pinnedX .G2 K gU s) (pinnedX .G2 K gC t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 10, 12, []) : PairRow)) (by decide) rfl sA (α := gU) (β := gC)
    (by rw [pos6]; exact sA_r) (by rw [pos10]; exact sA_b) s t
  exact this

theorem commute_v_b (s t : K) : Commute (pinnedX .G2 K gV s) (pinnedX .G2 K gB t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 10, 12, []) : PairRow)) (by decide) rfl (sA * sR * sA) (α := gV) (β := gB)
    (by rw [pos6]; exact sARA_r) (by rw [pos10]; exact sARA_b) s t
  exact this

theorem commute_v_c (s t : K) : Commute (pinnedX .G2 K gV s) (pinnedX .G2 K gC t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((6, 10, 12, []) : PairRow)) (by decide) rfl (sR * sA) (α := gV) (β := gC)
    (by rw [pos6]; exact sRA_r) (by rw [pos10]; exact sRA_b) s t
  exact this

theorem commute_b_c (s t : K) : Commute (pinnedX .G2 K gB s) (pinnedX .G2 K gC t) := by
  have := commute_pinnedX_of_nil (τ := .G2) (R := K)
    (r := ((7, 11, 12, []) : PairRow)) (by decide) rfl sR (α := gB) (β := gC)
    (by rw [pos7]; exact sR_a) (by rw [pos11]; exact sR_c) s t
  exact this

theorem comm_u_v_signed :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ {R : Type} [CommRing R] (x y : R),
      ⁅pinnedX .G2 R gU x, pinnedX .G2 R gV y⁆ = pinnedX .G2 R gC (((ε * 3 : ℤ) : R) * (x * y)) := by
  obtain ⟨εf, hεf, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow)) (by decide) sA
  refine ⟨εf (1, 1, 10, 3), hεf _, fun {R} _ x y => ?_⟩
  have h' := h (R := R) (α := gU) (β := gV) (by rw [pos6]; exact sA_r)
    (by rw [pos9]; exact sA_v) x y
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos10] at h'
  rw [h']
  have : sA • gB = gC := sA_b
  simp only [this, pow_one]
  congr 1
  push_cast
  ring

end Rows

abbrev iA : Fin Tag.G2.rank := ⟨0, by decide⟩
abbrev iR : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem isRoot_gA : IsRoot .G2 gA := by
  rw [← pos7]; exact isRoot_decodeVec_witness (by decide)

theorem isRoot_gB : IsRoot .G2 gB := by
  rw [← pos10]; exact isRoot_decodeVec_witness (by decide)

theorem isRoot_gU : IsRoot .G2 gU := by
  rw [← pos8]; exact isRoot_decodeVec_witness (by decide)

theorem isRoot_gV : IsRoot .G2 gV := by
  rw [← pos9]; exact isRoot_decodeVec_witness (by decide)

theorem isRoot_gC : IsRoot .G2 gC := by
  rw [← pos11]; exact isRoot_decodeVec_witness (by decide)

theorem isRoot_gR : IsRoot .G2 gR := by
  rw [← pos6]; exact isRoot_decodeVec_witness (by decide)

section Weyl

variable
    {K : Type} [Field K]

theorem nR_a (c : K) :
    weylElt .G2 K iR 1 * pinnedX .G2 K gA c * (weylElt .G2 K iR 1)⁻¹ =
      pinnedX .G2 K gB c := by
  have h := all_root_weyl_conjugation .G2 K iR isRoot_gA (1 : Kˣ) c
  have h1 : reflect .G2 iR gA = gB := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iR gA = 1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

theorem nR_b (c : K) :
    weylElt .G2 K iR 1 * pinnedX .G2 K gB c * (weylElt .G2 K iR 1)⁻¹ =
      pinnedX .G2 K gA (-c) := by
  have h := all_root_weyl_conjugation .G2 K iR isRoot_gB (1 : Kˣ) c
  have h1 : reflect .G2 iR gB = gA := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iR gB = -1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

theorem nR_u (c : K) :
    weylElt .G2 K iR 1 * pinnedX .G2 K gU c * (weylElt .G2 K iR 1)⁻¹ =
      pinnedX .G2 K gV c := by
  have h := all_root_weyl_conjugation .G2 K iR isRoot_gU (1 : Kˣ) c
  have h1 : reflect .G2 iR gU = gV := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iR gU = 1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

theorem nR_v (c : K) :
    weylElt .G2 K iR 1 * pinnedX .G2 K gV c * (weylElt .G2 K iR 1)⁻¹ =
      pinnedX .G2 K gU (-c) := by
  have h := all_root_weyl_conjugation .G2 K iR isRoot_gV (1 : Kˣ) c
  have h1 : reflect .G2 iR gV = gU := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iR gV = -1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

theorem nR_c (c : K) :
    weylElt .G2 K iR 1 * pinnedX .G2 K gC c * (weylElt .G2 K iR 1)⁻¹ =
      pinnedX .G2 K gC c := by
  have h := all_root_weyl_conjugation .G2 K iR isRoot_gC (1 : Kˣ) c
  have h1 : reflect .G2 iR gC = gC := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iR gC = 1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

theorem nA_b (c : K) :
    weylElt .G2 K iA 1 * pinnedX .G2 K gB c * (weylElt .G2 K iA 1)⁻¹ =
      pinnedX .G2 K gC c := by
  have h := all_root_weyl_conjugation .G2 K iA isRoot_gB (1 : Kˣ) c
  have h1 : reflect .G2 iA gB = gC := by funext i; fin_cases i <;> rfl
  have h2 : allRootWeylSign .G2 iA gB = 1 := by decide +kernel
  rw [h1, h2] at h
  simpa using h

end Weyl

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
