module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin

open Matrix
open CFSG.HardMathSupport.Curtis.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne

theorem exists_projectiveSL_of_typeA {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.p = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (f : ℕ), 1 ≤ f ∧
      Nat.card K = 2 ^ f ∧ 2 ≤ r + 1 ∧ (r + 1 = 2 → 4 ≤ 2 ^ f) ∧
      Nonempty (S ≃* projectiveSL (r + 1) K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 1 ≤ r := hrange.1
  have h4 : r = 1 → 4 ≤ q.p ^ q.exponent := by
    simpa only [TauCeti.PrimePower.card_def] using hrange.2
  have hf := q.exponent_pos
  have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (GaloisField q.p q.exponent) 2 :=
    charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hK])
  refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hchar, q.exponent, hf, hK,
    by omega, fun h => ?_, ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩
  have := h4 (by omega)
  rwa [hq] at this

section Aut

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem mem_semilinearAutGroup_of_pow_eq_one (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)}
    {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) : α ∈ semilinearAutGroup n K :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd hn hm hα

theorem exists_scalar_of_conjAut_eq_one (hn : 3 ≤ n) {B : GL (Fin n) K}
    (h : conjAut n K B = 1) : ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = B :=
  (eq_one_of_conjAut_mul_fieldAut_eq_one hn B 1 (by rw [map_one, mul_one, h])).2

theorem exists_conjAut_of_mem_linearAutGroup (hn : 3 ≤ n) {ζ : MulAut (projectiveSL n K)}
    (hζD : ζ ∈ linearAutGroup n K) {p : ℕ} (hζp : ζ ^ p = 1) :
    ∃ y : GL (Fin n) K, conjAut n K y = ζ ∧
      ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = y ^ p := by
  obtain ⟨y, rfl⟩ := mem_linearAutGroup_iff.1 hζD
  refine ⟨y, rfl, exists_scalar_of_conjAut_eq_one hn ?_⟩
  rw [map_pow]
  exact hζp

theorem conjAut_mul_fieldAut_pow_eq_one (hn : 3 ≤ n) {A : GL (Fin n) K} {σ : K ≃+* K} {m : ℕ}
    (h : (conjAut n K A * fieldAut n K σ) ^ m = 1) :
    σ ^ m = 1 ∧ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c =
      CFSG.RankThree.UnitaryDescent.twistedNorm σ A m := by
  rw [CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow] at h
  obtain ⟨h1, h2⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h
  exact ⟨h1, h2⟩

theorem exists_scalar_of_comm (hn : 3 ≤ n) {A y : GL (Fin n) K} {σ : K ≃+* K}
    (h : (conjAut n K A * fieldAut n K σ) * conjAut n K y =
      conjAut n K y * (conjAut n K A * fieldAut n K σ)) :
    ∃ c : Kˣ, A * GeneralLinearGroup.map (σ : K →+* K) y * A⁻¹ =
      GeneralLinearGroup.scalar (Fin n) c * y := by
  have h1 : conjAut n K A * fieldAut n K σ * conjAut n K y =
      conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) y) * fieldAut n K σ := by
    have := conjAut_mul_fieldAut_mul A y σ 1
    rw [map_one, mul_one, mul_one] at this
    exact this
  have h2 : conjAut n K y * (conjAut n K A * fieldAut n K σ) =
      conjAut n K (y * A) * fieldAut n K σ := by
    simp [mul_assoc]
  rw [h1, h2] at h
  have h3 := mul_right_cancel h
  have h4 : conjAut n K ((A * GeneralLinearGroup.map (σ : K →+* K) y) * (y * A)⁻¹) = 1 := by
    rw [map_mul, h3, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hn h4
  refine ⟨c, ?_⟩
  have h5 : A * GeneralLinearGroup.map (σ : K →+* K) y =
      GeneralLinearGroup.scalar (Fin n) c * (y * A) := by
    rw [hc, inv_mul_cancel_right]
  rw [mul_inv_eq_iff_eq_mul, h5, mul_assoc]

end Aut

section Outer

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem lin_outer_not_isSolvable [CharP K 2] (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : MulAut (projectiveSL n K)} (hζ : ζ ∈ semilinearAutGroup n K)
    (hζD : ζ ∉ linearAutGroup n K) (hζp : ζ ^ p = 1) : ¬ Group.IsSolvable ↥(autFix ζ) := by
  intro hsolv
  have : Fact p.Prime := ⟨hp⟩
  have hζ1 : ζ ≠ 1 := fun h1 => hζD (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
      Nat.prime_two hf hn hK
  obtain ⟨-, σ, -, ⟨h, -, hζeq⟩, -⟩ := hdesc p hp hp2 ζ hζ hζD hord
  set k := semilinearFixedSubfield σ with hk
  have hσk : ∀ c ∈ k, σ c = c := fun c hc => hc
  let ψ : projectiveSL n ↥k →* autFix ζ :=
    { toFun := fun a => ⟨h (linearSubfieldInclusion n k a), by
        change ζ (h (linearSubfieldInclusion n k a)) = h (linearSubfieldInclusion n k a)
        rw [hζeq]
        change h (fieldAut n K σ (h⁻¹ (h (linearSubfieldInclusion n k a)))) = _
        rw [MulAut.inv_apply, MulEquiv.symm_apply_apply,
          fieldAut_linearSubfieldInclusion hσk]⟩
      map_one' := by
        apply Subtype.ext
        change h (linearSubfieldInclusion n k 1) = 1
        rw [map_one, map_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        change h (linearSubfieldInclusion n k (a * b)) =
          h (linearSubfieldInclusion n k a) * h (linearSubfieldInclusion n k b)
        rw [map_mul, map_mul] }
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply linearSubfieldInclusion_injective (by omega : 0 < n) k
    exact h.injective (congrArg Subtype.val hab)
  have hsolv' : Group.IsSolvable (projectiveSL n ↥k) :=
    Group.isSolvable_of_isSolvable_injective hψinj
  have hsimple := KCLinearSubfield.isSimpleGroup_projectiveSL (n := n) (K := ↥k) hn
  have hnc := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn
  exact hnc (IsSimpleGroup.comm_iff_isSolvable.2 hsolv')

omit [Finite K] in
theorem lin_outer_false [CharP K 2] (hn : 3 ≤ n) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : MulAut (projectiveSL n K)} (hζ : ζ ∈ semilinearAutGroup n K)
    (hζD : ζ ∉ linearAutGroup n K) (hζp : ζ ^ p = 1) (hsolv : Group.IsSolvable ↥(autFix ζ)) :
    False :=
  lin_outer_not_isSolvable hn hf hK hp hp2 hζ hζD hζp hsolv

end Outer

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLin
