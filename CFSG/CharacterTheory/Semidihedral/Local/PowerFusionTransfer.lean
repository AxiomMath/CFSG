module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Semidihedral.Local

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem transfer_eq_pow_index_of_power_fusion (S : Sylow p G) (N : Subgroup S) [N.Normal]
    [IsMulCommutative (S ⧸ N)] (x : S)
    (hfus : ∀ (k : ℕ) (g : G) (h : g⁻¹ * (x : G) ^ k * g ∈ (S : Subgroup G)),
      (QuotientGroup.mk' N ⟨g⁻¹ * (x : G) ^ k * g, h⟩ : S ⧸ N) = QuotientGroup.mk' N (x ^ k)) :
    (QuotientGroup.mk' N).transfer (x : G) =
      QuotientGroup.mk' N x ^ (S : Subgroup G).index := by
  classical
  let := Fintype.ofFinite
    (Quotient (MulAction.orbitRel (Subgroup.zpowers (x : G)) (G ⧸ (S : Subgroup G))))
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod (S : Subgroup G) (x : G), ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [hfus, map_pow]

theorem power_fusion_transfer_detection (S : Sylow p G) (N : Subgroup S) [N.Normal]
    [IsMulCommutative (S ⧸ N)] (x : S) (hx : x ∉ N)
    (hfus : ∀ (k : ℕ) (g : G) (h : g⁻¹ * (x : G) ^ k * g ∈ (S : Subgroup G)),
      (QuotientGroup.mk' N ⟨g⁻¹ * (x : G) ^ k * g, h⟩ : S ⧸ N) = QuotientGroup.mk' N (x ^ k)) :
    let T : G →* S ⧸ N := (QuotientGroup.mk' N).transfer
    T x = QuotientGroup.mk' N x ^ (S : Subgroup G).index ∧ T x ≠ 1 ∧ T.ker.Normal ∧
      (x : G) ∉ T.ker ∧ Finite (G ⧸ T.ker) ∧ Nontrivial (G ⧸ T.ker) ∧ IsPGroup p (G ⧸ T.ker) ∧
      ∀ a b : G ⧸ T.ker, a * b = b * a := by
  intro T
  have hT : T x = QuotientGroup.mk' N x ^ (S : Subgroup G).index :=
    transfer_eq_pow_index_of_power_fusion S N x hfus
  have hpS : IsPGroup p (S ⧸ N) :=
    S.isPGroup'.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hTx : T x ≠ 1 := by
    rw [hT]
    intro h
    have hx1 : QuotientGroup.mk' N x ≠ 1 := by
      rw [QuotientGroup.mk'_apply, ne_eq, QuotientGroup.eq_one_iff]
      exact hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hpS (QuotientGroup.mk' N x)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hk, pow_zero]))
    have hdvd : p ^ k ∣ (S : Subgroup G).index := hk ▸ orderOf_dvd_of_pow_eq_one h
    exact S.not_dvd_index ((dvd_pow_self p hk0).trans hdvd)
  have hxK : (x : G) ∉ T.ker := fun h => hTx (MonoidHom.mem_ker.mp h)
  have hcomm : ∀ a b : G ⧸ T.ker, a * b = b * a := by
    intro a b
    apply QuotientGroup.kerLift_injective T
    rw [map_mul, map_mul, mul_comm]
  refine ⟨hT, hTx, inferInstance, hxK, inferInstance, ?_, ?_, hcomm⟩
  · refine nontrivial_of_ne (QuotientGroup.mk (x : G)) 1 ?_
    rw [ne_eq, QuotientGroup.eq_one_iff]
    exact hxK
  · exact (hpS.to_subgroup T.range).of_equiv (QuotientGroup.quotientKerEquivRange T).symm

end CFSG.Semidihedral.Local
