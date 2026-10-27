module

public import CFSG.CharacterTheory.OddOrderBasics.Schur
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped Classical

namespace CFSG.DefectZeroSylow

section RankOne

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isProj_range_of_mul_self {E : Module.End K V} (hE : E * E = E) :
    LinearMap.IsProj (LinearMap.range E) E := by
  refine ⟨fun x => LinearMap.mem_range_self E x, ?_⟩
  rintro x ⟨y, rfl⟩
  rw [← Module.End.mul_apply, hE]

variable [FiniteDimensional K V]

theorem trace_eq_finrank_range_of_mul_self {E : Module.End K V} (hE : E * E = E) :
    LinearMap.trace K V E = (Module.finrank K (LinearMap.range E) : K) :=
  (isProj_range_of_mul_self hE).trace

theorem mul_mul_eq_trace_smul [CharZero K] {E : Module.End K V} (hE : E * E = E)
    (htr : LinearMap.trace K V E = 1) (X : Module.End K V) :
    E * X * E = LinearMap.trace K V (E * X) • E := by
  have hrank : Module.finrank K (LinearMap.range E) = 1 := by
    have h := trace_eq_finrank_range_of_mul_self hE
    rw [htr] at h
    exact_mod_cast h.symm
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp hrank
  obtain ⟨c, hc⟩ := hv ⟨E (X v), LinearMap.mem_range_self E _⟩
  have hmain : E * X * E = c • E := by
    ext u
    obtain ⟨a, ha⟩ := hv ⟨E u, LinearMap.mem_range_self E u⟩
    have ha' : E u = a • (v : V) := by
      simpa using (congrArg Subtype.val ha).symm
    have hc' : E (X v) = c • (v : V) := by
      simpa using (congrArg Subtype.val hc).symm
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ha', map_smul, hc']
    rw [smul_comm]
  have htrace : LinearMap.trace K V (E * X) = c := by
    have h1 : E * X = E * (E * X) := by rw [← mul_assoc, hE]
    rw [h1, LinearMap.trace_mul_comm, hmain, map_smul, htr, smul_eq_mul, mul_one]
  rw [hmain, htrace]

end RankOne

section Average

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]

@[expose] noncomputable def averageOperator (ρ : Representation ℂ G V) (Q : Subgroup G) :
    Module.End ℂ V :=
  (Nat.card Q : ℂ)⁻¹ • ∑ x : Q, ρ x

variable (ρ : Representation ℂ G V) (Q : Subgroup G)

theorem mul_averageOperator {y : G} (hy : y ∈ Q) :
    ρ y * averageOperator ρ Q = averageOperator ρ Q := by
  unfold averageOperator
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨y, hy⟩ : Q)) _ _ (fun x => rfl)

theorem averageOperator_mul {y : G} (hy : y ∈ Q) :
    averageOperator ρ Q * ρ y = averageOperator ρ Q := by
  unfold averageOperator
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨y, hy⟩ : Q)) _ _ (fun x => rfl)

theorem averageOperator_mul_self : averageOperator ρ Q * averageOperator ρ Q =
    averageOperator ρ Q := by
  nth_rw 1 [averageOperator]
  rw [smul_mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun x _ => mul_averageOperator ρ Q x.2), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]

theorem mul_averageOperator_mul (L R : Module.End ℂ V) :
    L * averageOperator ρ Q * R = (Nat.card Q : ℂ)⁻¹ • ∑ x : Q, L * ρ x * R := by
  simp only [averageOperator, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]

theorem trace_averageOperator [FiniteDimensional ℂ V] :
    LinearMap.trace ℂ V (averageOperator ρ Q) =
      (Nat.card Q : ℂ)⁻¹ * ∑ x : Q, ρ.character x := by
  simp [averageOperator, map_sum, Representation.character]

end Average

section Spherical

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]

variable (ρ : Representation ℂ G V) (Q : Subgroup G) in
@[expose] noncomputable def sphericalFunction (g : G) : ℂ :=
  LinearMap.trace ℂ V (averageOperator ρ Q * ρ g)

variable {ρ : Representation ℂ G V} {Q : Subgroup G}

theorem sphericalFunction_mul_left {x : G} (hx : x ∈ Q) (g : G) :
    sphericalFunction ρ Q (x * g) = sphericalFunction ρ Q g := by
  rw [sphericalFunction, map_mul ρ, ← mul_assoc, averageOperator_mul ρ Q hx, sphericalFunction]

theorem sphericalFunction_mul_right (g : G) {y : G} (hy : y ∈ Q) :
    sphericalFunction ρ Q (g * y) = sphericalFunction ρ Q g := by
  rw [sphericalFunction, map_mul ρ, ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc,
    mul_averageOperator ρ Q hy, sphericalFunction]

theorem sphericalFunction_mul_mul {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (g : G) :
    sphericalFunction ρ Q (x * g * y) = sphericalFunction ρ Q g := by
  rw [sphericalFunction_mul_right _ hy, sphericalFunction_mul_left hx]

theorem sphericalFunction_one (htr : LinearMap.trace ℂ V (averageOperator ρ Q) = 1) :
    sphericalFunction ρ Q 1 = 1 := by
  rw [sphericalFunction, map_one, mul_one, htr]

variable [FiniteDimensional ℂ V] (htr : LinearMap.trace ℂ V (averageOperator ρ Q) = 1)
include htr

theorem averageOperator_mul_mul (g : G) :
    averageOperator ρ Q * ρ g * averageOperator ρ Q =
      sphericalFunction ρ Q g • averageOperator ρ Q :=
  mul_mul_eq_trace_smul (averageOperator_mul_self ρ Q) htr _

theorem sum_sphericalFunction_mul (a g : G) :
    ∑ x : Q, sphericalFunction ρ Q (a * x * g) =
      Nat.card Q * (sphericalFunction ρ Q a * sphericalFunction ρ Q g) := by
  have h1 : averageOperator ρ Q * ρ a * averageOperator ρ Q * ρ g * averageOperator ρ Q =
      (sphericalFunction ρ Q a * sphericalFunction ρ Q g) • averageOperator ρ Q := by
    rw [averageOperator_mul_mul htr, smul_mul_assoc, smul_mul_assoc, averageOperator_mul_mul htr,
      smul_smul]
  have h2 : averageOperator ρ Q * ρ a * averageOperator ρ Q * ρ g * averageOperator ρ Q =
      (Nat.card Q : ℂ)⁻¹ • ∑ x : Q, sphericalFunction ρ Q (a * x * g) • averageOperator ρ Q := by
    rw [mul_assoc _ (ρ g), mul_averageOperator_mul]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← averageOperator_mul_mul htr, map_mul ρ, map_mul ρ]
    simp only [mul_assoc]
  have h3 := congrArg (LinearMap.trace ℂ V) (h1.symm.trans h2)
  simp only [map_smul, map_sum, smul_eq_mul, htr, mul_one] at h3
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [h3, ← mul_assoc, mul_inv_cancel₀ hQ, one_mul]

theorem sum_sphericalFunction_mul_inv (hirr : ρ.IsIrreducible) :
    ∑ g : G, sphericalFunction ρ Q g * sphericalFunction ρ Q g⁻¹ =
      (Nat.card G : ℂ) / Module.finrank ℂ V := by
  let T : Module.End ℂ V := ∑ g : G, ρ g * averageOperator ρ Q * ρ g⁻¹
  have hcomm : ∀ h : G, T ∘ₗ ρ h = ρ h ∘ₗ T := by
    intro h
    change T * ρ h = ρ h * T
    simp only [T, Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft, map_mul ρ, mul_inv_rev, inv_inv, mul_assoc]
    rw [← mul_assoc (ρ h) (ρ h⁻¹), ← map_mul ρ h h⁻¹, mul_inv_cancel, map_one, one_mul]
  obtain ⟨s, hs⟩ := CFSG.OddOrderBasics.complex_irreducible_commuting_scalar ρ hirr T hcomm
  have htrT : LinearMap.trace ℂ V T = Nat.card G := by
    have hterm : ∀ g : G, LinearMap.trace ℂ V (ρ g * averageOperator ρ Q * ρ g⁻¹) = 1 := by
      intro g
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, inv_mul_cancel, map_one, one_mul,
        htr]
    simp only [T, map_sum, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  have hs' : s * Module.finrank ℂ V = Nat.card G := by
    rw [← htrT, hs, map_smul, LinearMap.trace_id, smul_eq_mul]
  have h1 : averageOperator ρ Q * T * averageOperator ρ Q = s • averageOperator ρ Q := by
    rw [hs, ← Module.End.one_eq_id, mul_smul_comm, smul_mul_assoc, mul_one,
      averageOperator_mul_self]
  have h2 : averageOperator ρ Q * T * averageOperator ρ Q =
      ∑ g : G, (sphericalFunction ρ Q g * sphericalFunction ρ Q g⁻¹) • averageOperator ρ Q := by
    simp only [T, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← smul_smul, ← averageOperator_mul_mul htr g⁻¹, ← smul_mul_assoc, ← smul_mul_assoc,
      ← averageOperator_mul_mul htr g]
    simp only [mul_assoc]
  have h3 := congrArg (LinearMap.trace ℂ V) (h1.symm.trans h2)
  simp only [map_smul, map_sum, smul_eq_mul, htr, mul_one] at h3
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hV : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs'
    exact hG hs'.symm
  rw [← h3, eq_div_iff hV, hs']

end Spherical

end CFSG.DefectZeroSylow
