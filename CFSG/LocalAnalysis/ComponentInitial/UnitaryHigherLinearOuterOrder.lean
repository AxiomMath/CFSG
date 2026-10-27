module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem index_powRange_dvd_gcd {k : Type} [Field k] [Finite k] (n : ℕ) :
    (powMonoidHom n : kˣ →* kˣ).range.index ∣ Nat.gcd n (Nat.card k - 1) := by
  refine Nat.dvd_gcd ?_ ?_
  · have hcyc : IsCyclic (kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range) :=
      isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    change Nat.card (kˣ ⧸ (powMonoidHom n : kˣ →* kˣ).range) ∣ n
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  · rw [← Nat.card_units]
    exact Subgroup.index_dvd_card _

theorem relIndex_inner_linearAutGroup_dvd {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n) :
    (inner (projectiveSL n k)).relIndex (linearAutGroup n k) ∣ Nat.gcd n (Nat.card k - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hD : linearAutGroup n k = (conjAut n k).range := by
    rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
  have hcomap : ((inner (projectiveSL n k)).subgroupOf (conjAut n k).range).comap
      (conjAut n k).rangeRestrict = (inner (projectiveSL n k)).comap (conjAut n k) := by
    ext A
    rfl
  have hle : ((powMonoidHom n : kˣ →* kˣ).range).comap GeneralLinearGroup.det ≤
      (inner (projectiveSL n k)).comap (conjAut n k) := by
    rintro A ⟨u, hu⟩
    have hdet : (((GeneralLinearGroup.scalar (Fin n) u⁻¹ * A : GL (Fin n) k)) :
        Matrix (Fin n) (Fin n) k).det = 1 := by
      have h1 := congrArg (fun v : kˣ => (v : k)) hu
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val,
        GeneralLinearGroup.val_det_apply] at h1
      rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← h1, Units.val_inv_eq_inv_val,
        inv_pow, inv_mul_cancel₀ (pow_ne_zero _ u.ne_zero)]
    obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin n) k,
        SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) u⁻¹ * A :=
      ⟨⟨_, hdet⟩, Units.ext rfl⟩
    have hA : A = GeneralLinearGroup.scalar (Fin n) u * SpecialLinearGroup.toGL g := by
      rw [hg, map_inv, mul_inv_cancel_left]
    change conjAut n k A ∈ inner (projectiveSL n k)
    rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
    exact ⟨_, rfl⟩
  calc (inner (projectiveSL n k)).relIndex (linearAutGroup n k)
      = ((inner (projectiveSL n k)).comap (conjAut n k)).index := by
        rw [hD, Subgroup.relIndex, ← hcomap,
          Subgroup.index_comap_of_surjective _ (MonoidHom.rangeRestrict_surjective _)]
    _ ∣ (((powMonoidHom n : kˣ →* kˣ).range).comap GeneralLinearGroup.det).index :=
        Subgroup.index_dvd_of_le hle
    _ = (powMonoidHom n : kˣ →* kˣ).range.index :=
        Subgroup.index_comap_of_surjective _ GeneralLinearGroup.det_surjective
    _ ∣ Nat.gcd n (Nat.card k - 1) := index_powRange_dvd_gcd n

theorem higher_linear_outer_order_divides_field_gcd_bound {k : Type} [Field k] {p f n : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n) (hk : Nat.card k = p ^ f) :
    Nat.card (Outer (projectiveSL n k)) ∣ 2 * f * Nat.gcd n (p ^ f - 1) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hp.pos f).ne')
  have : Finite (MulAut (projectiveSL n k)) :=
    Finite.of_injective (fun e : MulAut (projectiveSL n k) => (e : projectiveSL n k →
      projectiveSL n k)) fun a b hab => MulEquiv.ext (congrFun hab)
  have hR := (automorphism_generation (K := k) hn).1
  obtain ⟨hID, -, hDnorm, -, -, -, -, hRE, -, -⟩ := standard_outer_quotients (n := n) (K := k)
  rw [hR] at hDnorm hRE
  have hDE : linearAutGroup n k ≤ semilinearAutGroup n k := linearAutGroup_le_semilinearAutGroup
  have h1 := relIndex_inner_linearAutGroup_dvd (k := k) (n := n) (by omega)
  rw [hk] at h1
  have hDn : (linearAutGroup n k).Normal := ⟨fun d hd g =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have hE : semilinearAutGroup n k = linearAutGroup n k ⊔ (fieldAut n k).range := by
    rw [semilinearAutGroup, Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range,
      Subgroup.closure_eq]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp hf hk
  have : Finite (k ≃+* k) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h2 : (linearAutGroup n k).relIndex (semilinearAutGroup n k) ∣ f := by
    rw [hE, Subgroup.relIndex_sup_left, ← hcard]
    refine (Subgroup.index_dvd_card _).trans ?_
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_card _
  have h3 : (semilinearAutGroup n k).index ∣ 2 := by
    have hle : (semilinearAutGroup n k).index ≤ 2 := by
      rwa [← Subgroup.relIndex_top_right]
    have h0 : (semilinearAutGroup n k).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (semilinearAutGroup n k).index = 1 ∨
        (semilinearAutGroup n k).index = 2) with h | h <;> rw [h]
    · exact one_dvd 2
  have hID' : inner (projectiveSL n k) ≤ linearAutGroup n k := hID
  change (inner (projectiveSL n k)).index ∣ _
  rw [← Subgroup.relIndex_mul_index hID', ← Subgroup.relIndex_mul_index hDE]
  calc (inner (projectiveSL n k)).relIndex (linearAutGroup n k) *
        ((linearAutGroup n k).relIndex (semilinearAutGroup n k) *
          (semilinearAutGroup n k).index)
      ∣ Nat.gcd n (p ^ f - 1) * (f * 2) := Nat.mul_dvd_mul h1 (Nat.mul_dvd_mul h2 h3)
    _ = 2 * f * Nat.gcd n (p ^ f - 1) := by ring

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
