module

public import CFSG.Monster.B.TwoA.Unitary.Twenty
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyAlg
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23UnitaryInputs
public import Certificates.Certificate3177
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3175
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate16016
import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Unitary.Planes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Unitary CFSG.Fischer Matrix

attribute [local irreducible] decW u20RecRows u20Gens u20Words u20Basis

theorem nuWord_lt : ∀ k ∈ nuWord, k < 17 := by decide

@[expose] noncomputable def nuU :
    Usig := wordU nuWord

theorem rowsGeom_nuWord : rowsGeom (wordRows nuWord) 11 = zeroRows :=
  Certificates.certificate3177.1

section Rows

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (b : Module.Basis (Fin 20) (ZMod 2) V)

theorem endOf_rowsPow_apply (R : Array ℕ) {x : V} (hx : endOf b R x = x) (n : ℕ) :
    endOf b (rowsPow R n) x = x := by
  induction n with
  | zero => rw [rowsPow, endOf_idRows, Module.End.one_apply]
  | succ n ih => rw [rowsPow, endOf_rowsMul, Module.End.mul_apply, ih, hx]

theorem endOf_rowsGeom_apply (R : Array ℕ) {x : V} (hx : endOf b R x = x) (n : ℕ) :
    endOf b (rowsGeom R n) x = n • x := by
  induction n with
  | zero => rw [rowsGeom, endOf_zeroRows, LinearMap.zero_apply, zero_smul]
  | succ n ih =>
    rw [rowsGeom, endOf_rowsXor, LinearMap.add_apply, ih, endOf_rowsPow_apply b R hx, succ_nsmul]

end Rows

theorem eq_zero_of_w20End_nuU
    {x : W20} (hx : w20End nuU x = x)
    :
    x = 0 := by
  have hT : endOf b20 (wordRows nuWord) x = x := by
    rw [← w20End_wordU nuWord nuWord_lt]
    exact hx
  have h := endOf_rowsGeom_apply b20 _ hT 11
  rw [rowsGeom_nuWord, endOf_zeroRows, LinearMap.zero_apply, ← Nat.cast_smul_eq_nsmul (ZMod 2),
    show ((11 : ℕ) : ZMod 2) = 1 from rfl, one_smul] at h
  exact h.symm

theorem eq_zero_or_eq_sigmaW_of_fixed
    {x : Wv v0}
    (hx : x ∈ sigmaPerp)
    (hfix : wAct v0 (nuU : Kstab v0) x = x) : x = 0 ∨ x = sigmaW := by
  have h1 : w20End nuU (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨x, hx⟩ := by
    rw [w20End_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext ((perpEnd_apply _ _).trans hfix))
  have h2 := eq_zero_of_w20End_nuU h1
  rw [Submodule.Quotient.mk_eq_zero, Unitary.sigLine, Submodule.mem_span_singleton] at h2
  obtain ⟨a, ha⟩ := h2
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · left
    rw [zero_smul] at ha
    exact (congrArg Subtype.val ha).symm
  · right
    rw [one_smul] at ha
    exact (congrArg Subtype.val ha).symm

theorem nuPowM_zero : nuPowM 0 = 1 :=
  Certificates.certificate3177.2.1

theorem nuPowM_one : nuPowM 1 = nuMat :=
  Certificates.certificate3177.2.2.1

theorem nuPowM_succ :
    ∀ i < 5, nuPowM (i + 1) = nuPowM i * nuPowM 1 :=
  Certificates.certificate3177.2.2.2.1

theorem nuPowM_eleven : nuPowM 5 * nuPowM 5 * nuPowM 1 = 1 :=
  Certificates.certificate3177.2.2.2.2.1

theorem nuMat_pow_eq (i : ℕ) (hi : i < 6) :
    nuMat ^ i = nuPowM i := by
  induction i with
  | zero => rw [pow_zero, nuPowM_zero]
  | succ i ih => rw [pow_succ, ih (by omega), nuPowM_succ i (by omega), nuPowM_one]

theorem nuMat_pow : nuMat ^ 11 = 1 := by
  rw [show 11 = 5 + 5 + 1 from rfl, pow_add, pow_add, pow_one, nuMat_pow_eq 5 (by norm_num),
    ← nuPowM_one, nuPowM_eleven]

theorem trace_nuMat_ne :
    Matrix.trace nuMat ≠ Matrix.trace (barM nuMat) := by
  rw [← nuPowM_one]
  exact Certificates.certificate3177.2.2.2.2.2.1

theorem cycInv_mul : cycInv * cycMat = 1 :=
  Certificates.certificate3177.2.2.2.2.2.2.1

theorem isScalarM_of_sq : ∀ c : Fin 6 → F4,
    IsScalarM ((∑ i : Fin 6, c i • nuPowM i) * ∑ i : Fin 6, c i • nuPowM i) →
      IsScalarM (∑ i : Fin 6, c i • nuPowM i) :=
  Certificates.certificate3177.2.2.2.2.2.2.2

theorem eq_sum_of_commute {n : ℕ} {R : Type*} [CommRing R] {X P Q : Matrix (Fin n) (Fin n) R}
    {v : Fin n → R} (hP : ∀ i, P i = v ᵥ* X ^ (i : ℕ)) (hQ : Q * P = 1)
    {A : Matrix (Fin n) (Fin n) R} (hA : A * X = X * A) :
    A = ∑ i : Fin n, ((v ᵥ* A) ᵥ* Q) i • X ^ (i : ℕ) := by
  set B := ∑ i : Fin n, ((v ᵥ* A) ᵥ* Q) i • X ^ (i : ℕ) with hB
  have hAX : ∀ k : ℕ, A * X ^ k = X ^ k * A := fun k => ((Commute.pow_right hA k)).eq
  have hBX : ∀ k : ℕ, B * X ^ k = X ^ k * B := by
    intro k
    rw [hB, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← pow_add, ← pow_add, add_comm]
  have hvB : v ᵥ* B = v ᵥ* A := by
    have e1 : v ᵥ* B = ((v ᵥ* A) ᵥ* Q) ᵥ* P := by
      rw [hB, Matrix.vecMul_sum]
      funext j
      simp only [Matrix.vecMul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
        dotProduct, hP]
    rw [e1, Matrix.vecMul_vecMul, hQ, Matrix.vecMul_one]
  have hrow : ∀ (M : Matrix (Fin n) (Fin n) R), (∀ k : ℕ, M * X ^ k = X ^ k * M) →
      ∀ i j, (P * M) i j = ((v ᵥ* M) ᵥ* X ^ (i : ℕ)) j := by
    intro M hM i j
    have e1 : (P * M) i j = (P i ᵥ* M) j := by simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    rw [e1, hP, Matrix.vecMul_vecMul, ← hM, ← Matrix.vecMul_vecMul]
  have hPAB : P * A = P * B := Matrix.ext fun i j => by rw [hrow A hAX, hrow B hBX, hvB]
  calc A = Q * P * A := by rw [hQ, Matrix.one_mul]
    _ = Q * (P * A) := Matrix.mul_assoc _ _ _
    _ = Q * (P * B) := by rw [hPAB]
    _ = B := by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]

theorem isScalarM_of_commute_nuMat {A : Matrix (Fin 6) (Fin 6) F4}
    (hA : A * nuMat = nuMat * A)
    (hsq : IsScalarM (A * A)) : IsScalarM A := by
  have hP : ∀ i : Fin 6, cycMat i = Pi.single 0 1 ᵥ* nuMat ^ (i : ℕ) := by
    intro i
    rw [nuMat_pow_eq i i.2, Matrix.single_one_vecMul]
    rfl
  have e := eq_sum_of_commute hP cycInv_mul hA
  have e2 : ∀ c : Fin 6 → F4, ∑ i : Fin 6, c i • nuMat ^ (i : ℕ) = ∑ i : Fin 6, c i • nuPowM i :=
    fun c => Finset.sum_congr rfl fun i _ => by rw [nuMat_pow_eq i i.2]
  rw [e, e2] at hsq ⊢
  exact isScalarM_of_sq _ hsq

theorem isScalarM_iff {A : Matrix (Fin 6) (Fin 6) F4} :
    IsScalarM A ↔ A = Matrix.scalar (Fin 6) (A 0 0) := by
  constructor
  · intro h
    ext i j
    rw [h (i, j), Matrix.scalar_apply, Matrix.diagonal_apply]
  · intro h p
    have e := congrFun (congrFun h p.1) p.2
    rw [e, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem b6N_eq (k : Fin 17) (hk : (k : ℕ) ≠ 5) : b6N k = b6Mat k := by
  rw [b6N, barPowM, b6Frob_eq, ite_eq_right hk, ite_eq_left rfl]

theorem slElt_eq (k : Fin 17) (hk : (k : ℕ) ≠ 5) :
    slElt k = SemidirectProduct.inl ((b6SU k : SUh) : SUh ⧸ Zh) := by
  refine SemidirectProduct.ext rfl ?_
  rw [SemidirectProduct.right_inl]
  change Multiplicative.ofAdd (b6Frob k) = 1
  rw [b6Frob_eq, ite_eq_right hk]
  rfl

@[expose] noncomputable def nuSU :
    SUh := b6SU 0 * b6SU 3 * b6SU 4 * b6SU 7 * b6SU 16

theorem coe_nuSU :
    (((nuSU : SUh) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = nuMat := by
  simp only [nuSU, Subgroup.coe_mul, Units.val_mul, coe_b6SU]
  rw [b6N_eq 0 (by decide), b6N_eq 3 (by decide), b6N_eq 4 (by decide), b6N_eq 7 (by decide),
    b6N_eq 16 (by decide)]
  rfl

theorem wordU_cons
    {k : ℕ} (hk : k < 17) (w : List ℕ) :
    wordU (k :: w) = genU ⟨k, hk⟩ * wordU w := by
  change (if h : k < 17 then genU ⟨k, h⟩ else 1) * wordU w = _
  rw [dite_eq_left hk]

theorem phiU_nuU :
    phiU nuU = SemidirectProduct.inl ((nuSU : SUh) : SUh ⧸ Zh) := by
  have e : nuU = genU 0 * (genU 3 * (genU 4 * (genU 7 * (genU 16 * 1)))) := by
    rw [nuU, nuWord, wordU_cons (by norm_num), wordU_cons (by norm_num),
      wordU_cons (by norm_num), wordU_cons (by norm_num), wordU_cons (by norm_num)]
    rfl
  rw [e, map_mul, map_mul, map_mul, map_mul, map_mul, map_one, phiU_genU, phiU_genU, phiU_genU,
    phiU_genU, phiU_genU, slElt_eq 0 (by decide), slElt_eq 3 (by decide), slElt_eq 4 (by decide),
    slElt_eq 7 (by decide), slElt_eq 16 (by decide), mul_one, ← map_mul, ← map_mul, ← map_mul,
    ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  simp only [nuSU, mul_assoc]

theorem scalar_eq_one_of_conj {A Y X : GL (Fin 6) F4} {c : F4ˣ} (hX : X ^ 11 = 1)
    (hY : Y ^ 11 = 1) (h : A * Y * A⁻¹ = GeneralLinearGroup.scalar (Fin 6) c * X) : c = 1 := by
  have h1 : (A * Y * A⁻¹) ^ 11 = 1 := by rw [conj_pow, hY, mul_one, mul_inv_cancel]
  rw [h, (Commute.mul_pow (scalar_commute c X).symm 11), hX, mul_one] at h1
  have h1' : GeneralLinearGroup.scalar (Fin 6) (c ^ 11) = 1 := by rw [map_pow]; exact h1
  have h2 : ((c ^ 11 : F4ˣ) : F4) = 1 := by
    have := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) 0 0) h1'
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at this
    exact this
  have h3 : ∀ x : F4, x ^ 11 = 1 → x = 1 := by decide
  exact Units.ext (h3 _ (by rw [← Units.val_pow_eq_pow_val]; exact h2))

theorem conj_eq_of_inv_mul_eq {M : Type*} [Group M] {a y y' s : M} (hs : ∀ g, g * s = s * g)
    (h : (a * y)⁻¹ * (y' * a) = s) : a * y * a⁻¹ = s⁻¹ * y' := by
  have e1 : y' * a = a * y * s := by rw [← h]; group
  have e2 : y' = a * y * a⁻¹ * s := by
    calc y' = y' * a * a⁻¹ := by group
      _ = a * y * s * a⁻¹ := by rw [e1]
      _ = a * y * (s * a⁻¹) := by group
      _ = a * y * (a⁻¹ * s) := by rw [hs a⁻¹]
      _ = a * y * a⁻¹ * s := by group
  rw [e2, hs (a * y * a⁻¹)]
  group

theorem exists_scalar_of_mk_eq {A Y Y' : SUh}
    (h : ((A * Y : SUh) : SUh ⧸ Zh) = ((Y' * A : SUh) : SUh ⧸ Zh)) :
    ∃ c : F4ˣ, (A : GL (Fin 6) F4) * Y * (A : GL (Fin 6) F4)⁻¹ =
      GeneralLinearGroup.scalar (Fin 6) c * Y' := by
  rw [QuotientGroup.eq] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c⁻¹, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul] at hc
  rw [conj_eq_of_inv_mul_eq (fun g => scalar_commute c g) hc, map_inv]

theorem nuSU_pow :
    ((nuSU : SUh) : GL (Fin 6) F4) ^ 11 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_nuSU, nuMat_pow, Units.val_one])

theorem frob_nuSU_pow :
    frobGL ((nuSU : SUh) : GL (Fin 6) F4) ^ 11 = 1 := by
  rw [← map_pow, nuSU_pow, map_one]

theorem nuMat_ne : nuMat 0 1 ≠ 0 := by
  rw [← nuPowM_one]
  decide

theorem nuSU_pow_SU : nuSU ^ 11 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, Subgroup.coe_one]; exact nuSU_pow)

theorem nuU_pow :
    nuU ^ 11 = 1 := by
  apply phiU.injective
  rw [map_pow, phiU_nuU, ← map_pow, ← QuotientGroup.mk_pow, nuSU_pow_SU, QuotientGroup.mk_one,
    map_one, map_one]

theorem nuU_ne_one :
    nuU ≠ 1 := by
  intro h
  have h1 : ((nuSU : SUh) : SUh ⧸ Zh) = 1 :=
    SemidirectProduct.inl_injective ((phiU_nuU.symm.trans (by rw [h, map_one])).trans
      (map_one _).symm)
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) 0 1) hc
  simp only [coe_nuSU, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 6) ≠ 1)] at h2
  exact nuMat_ne h2

theorem orderOf_nuU :
    orderOf nuU = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime nuU_pow nuU_ne_one

theorem eq_one_of_commute_mul_self
    {a : SUh ⧸ Zh}
    (hc : Commute a (nuSU : SUh ⧸ Zh))
    (h2 : a * a = 1) : a = 1 := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨c, hc'⟩ := exists_scalar_of_mk_eq (A := A) (Y := nuSU) (Y' := nuSU)
    (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc.eq)
  rw [scalar_eq_one_of_conj nuSU_pow nuSU_pow hc', map_one, one_mul] at hc'
  have hAX : ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * nuMat =
      nuMat * ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
    have e : (A : GL (Fin 6) F4) * nuSU = nuSU * A := by
      calc (A : GL (Fin 6) F4) * nuSU =
          (A : GL (Fin 6) F4) * nuSU * (A : GL (Fin 6) F4)⁻¹ * (A : GL (Fin 6) F4) := by group
        _ = nuSU * A := by rw [hc']
    have e' := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) e
    simp only [Units.val_mul, coe_nuSU] at e'
    exact e'
  have hA2 : A * A ∈ Zh := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact h2
  obtain ⟨μ, hμ⟩ := hA2
  have hsq : IsScalarM (((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := by
    have e := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) hμ
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at e
    have h00 : (Matrix.scalar (Fin 6) (μ : F4)) 0 0 = μ := by
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    rw [isScalarM_iff, e, h00]
  have hs := isScalarM_iff.1 (isScalarM_of_commute_nuMat hAX hsq)
  rw [QuotientGroup.eq_one_iff]
  have h0 : ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) 0 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs
    have h1 := Units.mul_inv (A : GL (Fin 6) F4)
    rw [hs, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  exact ⟨Units.mk0 _ h0, Units.ext (by rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hs])⟩

theorem not_commute_outer (A : SUh) :
    ¬ Commute (⟨(A : SUh ⧸ Zh), Multiplicative.ofAdd 1⟩ : SigmaU6)
      (SemidirectProduct.inl (nuSU : SUh ⧸ Zh)) := by
  intro hc
  have hl := congrArg SemidirectProduct.left hc.eq
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    map_one, MulAut.one_apply] at hl
  rw [frobHomU_apply, toAdd_ofAdd, frobPowQ_one, frobQ_mk] at hl
  obtain ⟨c, hc'⟩ := exists_scalar_of_mk_eq (A := A) (Y := frobSU nuSU) (Y' := nuSU)
    (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hl)
  rw [coe_frobSU] at hc'
  rw [scalar_eq_one_of_conj nuSU_pow frob_nuSU_pow hc', map_one, one_mul] at hc'
  have ht := congrArg (fun g : GL (Fin 6) F4 => Matrix.trace (g : Matrix (Fin 6) (Fin 6) F4)) hc'
  simp only [Units.val_mul] at ht
  rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, coe_frobGL, coe_nuSU] at ht
  exact trace_nuMat_ne ht.symm

theorem eq_one_of_commute_two_pow
    {a : SUh ⧸ Zh}
    (hc : Commute a (nuSU : SUh ⧸ Zh)) :
    ∀ m : ℕ, a ^ 2 ^ m = 1 → a = 1
  | 0, h => by rwa [pow_zero, pow_one] at h
  | m + 1, h => by
    have h' : a ^ 2 ^ m * a ^ 2 ^ m = 1 := by rw [← pow_two, ← pow_mul, ← pow_succ]; exact h
    exact eq_one_of_commute_two_pow hc m (eq_one_of_commute_mul_self (hc.pow_left _) h')

theorem eq_one_of_commute_nuU
    {s : Usig} (hs : Commute s nuU)
    (h2 : ∃ m : ℕ, s ^ 2 ^ m = 1) :
    s = 1 := by
  obtain ⟨m, hm⟩ := h2
  apply phiU.injective
  rw [map_one]
  have hc : Commute (phiU s) (SemidirectProduct.inl (nuSU : SUh ⧸ Zh)) := by
    rw [← phiU_nuU]
    exact hs.map phiU
  have hm' : phiU s ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
  generalize phiU s = σ at hc hm' ⊢
  obtain ⟨a, ε⟩ := σ
  rcases zmod2_cases' (Multiplicative.toAdd ε) with h | h
  · have hε : ε = 1 := by rw [← ofAdd_toAdd ε, h]; rfl
    subst hε
    have hinl : (⟨a, 1⟩ : SigmaU6) = SemidirectProduct.inl a := rfl
    rw [hinl] at hc hm' ⊢
    have hca : Commute a (nuSU : SUh ⧸ Zh) := by
      have := hc.eq
      rw [← map_mul, ← map_mul] at this
      exact SemidirectProduct.inl_injective this
    have ham : a ^ 2 ^ m = 1 := by
      rw [← map_pow] at hm'
      exact SemidirectProduct.inl_injective (hm'.trans (map_one _).symm)
    rw [eq_one_of_commute_two_pow hca m ham, map_one]
  · exfalso
    have hε : ε = Multiplicative.ofAdd 1 := by rw [← ofAdd_toAdd ε, h]
    subst hε
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
    exact not_commute_outer A hc

theorem eq_one_of_commute
    {u s : Usig}
    (hu : nuU ∈ Subgroup.zpowers u) (hs : Commute s u)
    (h2 : ∃ m : ℕ, s ^ 2 ^ m = 1) : s = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
  exact eq_one_of_commute_nuU (hk ▸ hs.zpow_right k) h2

theorem eq_zero_or_eq_sigmaW_of_fixed'
    {u : Usig}
    (hu : nuU ∈ Subgroup.zpowers u) {x : Wv v0}
    (hx : x ∈ sigmaPerp) (hfix : wAct v0 (u : Kstab v0) x = x) : x = 0 ∨ x = sigmaW := by
  have h1 : (u : Kstab v0) ∈ wStab x := mem_wStab.2 hfix
  have h2 : ((nuU : Usig) : Kstab v0) ∈ wStab x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← hk, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem _ h1 k
  exact eq_zero_or_eq_sigmaW_of_fixed hx (mem_wStab.1 h2)

theorem zmod11_of_pow_two_pow : ∀ (m : ℕ) (x : ZMod 11), x ^ 2 ^ m = 1 → x = 1 ∨ x = -1
  | 0, x, h => Or.inl (by rwa [pow_zero, pow_one] at h)
  | m + 1, x, h => by
    have h' : (x ^ 2) ^ 2 ^ m = 1 := by rw [← pow_mul, ← pow_succ']; exact h
    have hsq : ∀ y : ZMod 11, y ^ 2 = 1 → y = 1 ∨ y = -1 := by decide
    have hne : ∀ y : ZMod 11, y ^ 2 ≠ -1 := by decide
    rcases zmod11_of_pow_two_pow m (x ^ 2) h' with h1 | h1
    · exact hsq x h1
    · exact absurd h1 (hne x)

theorem conj_pow_eq {M : Type*} [Group M] {Y u : M} {n : ℕ} (h : Y * u * Y⁻¹ = u ^ n) :
    ∀ j : ℕ, Y ^ j * u * (Y ^ j)⁻¹ = u ^ (n ^ j)
  | 0 => by rw [pow_zero, pow_zero, pow_one, one_mul, inv_one, mul_one]
  | j + 1 => by
    calc Y ^ (j + 1) * u * (Y ^ (j + 1))⁻¹ = Y * (Y ^ j * u * (Y ^ j)⁻¹) * Y⁻¹ := by
          rw [pow_succ']; group
      _ = (Y * u * Y⁻¹) ^ (n ^ j) := by rw [conj_pow_eq h j, conj_pow]
      _ = u ^ (n ^ (j + 1)) := by rw [h, ← pow_mul, pow_succ']

theorem conj_eq_inv_of_normalizes
    {u Y : Usig}
    (hu : nuU ∈ Subgroup.zpowers u)
    (hu11 : orderOf u = 11) (hY : Y * u * Y⁻¹ ∈ Subgroup.zpowers u)
    (h2 : ∃ m : ℕ, Y ^ 2 ^ m = 1) (hY1 : Y ≠ 1) : Y * u * Y⁻¹ = u⁻¹ := by
  obtain ⟨m, hm⟩ := h2
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 ((mem_powers_iff_mem_zpowers).2 hY)
  have h1 := conj_pow_eq hn.symm (2 ^ m)
  rw [hm, one_mul, inv_one, mul_one] at h1
  have h3 : n ^ 2 ^ m ≡ 1 [MOD 11] := by
    rw [← hu11, ← pow_eq_pow_iff_modEq, pow_one]
    exact h1.symm
  have h4 : ((n : ZMod 11)) ^ 2 ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ 11).2 h3
    push_cast at this
    exact this
  have hval : ∀ z : ZMod 11, (n : ZMod 11) = z → n % 11 = z.val := fun z hz => by
    rw [← hz, ZMod.val_natCast]
  have hpow : u ^ n = u ^ (n % 11) := by rw [← hu11, pow_mod_orderOf]
  rcases zmod11_of_pow_two_pow m _ h4 with h5 | h5
  · exfalso
    apply hY1
    refine eq_one_of_commute hu ?_ ⟨m, hm⟩
    have e : Y * u * Y⁻¹ = u := by
      rw [← hn, hpow, hval 1 h5, show (1 : ZMod 11).val = 1 by decide, pow_one]
    exact (mul_inv_eq_iff_eq_mul.1 e)
  · rw [← hn, hpow, hval (-1) h5]
    have e : u ^ 11 = 1 := by rw [← hu11, pow_orderOf_eq_one]
    rw [show (-1 : ZMod 11).val = 10 by decide, eq_inv_iff_mul_eq_one, ← pow_succ, e]

end CFSG.EvenSmallLie.TwoE6
